/*
 * Copyright 2009-2017 Aarhus University
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package dk.brics.tajs.solver;

import com.google.gson.Gson;
import com.google.gson.GsonBuilder;
import dk.brics.tajs.analysis.SourceTracker;
import dk.brics.tajs.flowgraph.AbstractNode;
import dk.brics.tajs.flowgraph.BasicBlock;
import dk.brics.tajs.flowgraph.FlowGraph;
import dk.brics.tajs.flowgraph.Function;
import dk.brics.tajs.flowgraph.SourceLocation;
import dk.brics.tajs.flowgraph.jsnodes.BeginForInNode;
import dk.brics.tajs.flowgraph.jsnodes.CallNode;
import dk.brics.tajs.flowgraph.jsnodes.EndForInNode;
import dk.brics.tajs.flowgraph.jsnodes.ExceptionalReturnNode;
import dk.brics.tajs.flowgraph.jsnodes.ReadVariableNode;
import dk.brics.tajs.flowgraph.jsnodes.ReturnNode;
import dk.brics.tajs.flowgraph.jsnodes.WriteVariableNode;
import dk.brics.tajs.lattice.Obj;
import dk.brics.tajs.lattice.ObjectLabel;
import dk.brics.tajs.lattice.ScopeChain;
import dk.brics.tajs.lattice.State;
import dk.brics.tajs.lattice.Value;
import dk.brics.tajs.options.Options;
import dk.brics.tajs.solver.IAnalysisLatticeElement.MergeResult;
import dk.brics.tajs.util.AnalysisException;
import dk.brics.tajs.util.AnalysisLimitationException;
import dk.brics.tajs.util.TotalsLog;
import net.htmlparser.jericho.Source;
import org.apache.log4j.Logger;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.io.Writer;
import java.net.URI;
import java.net.URISyntaxException;
import java.net.URL;
import java.nio.file.FileSystems;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.StandardOpenOption;
import java.sql.Timestamp;
import java.text.Collator;
import java.text.SimpleDateFormat;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Currency;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.TreeSet;
import java.util.function.Supplier;

/**
 * Generic fixpoint solver for flow graphs.
 */
public class GenericSolver<StateType extends IState<StateType, ContextType, CallEdgeType>,
        ContextType extends IContext<ContextType>,
        CallEdgeType extends ICallEdge<StateType>,
        MonitoringType extends ISolverMonitoring<StateType, ContextType>,
        AnalysisType extends IAnalysis<StateType, ContextType, CallEdgeType, MonitoringType, AnalysisType>> {

    private static Logger log = Logger.getLogger(GenericSolver.class);

    private final AnalysisType analysis;

    private final SolverSynchronizer sync;

    private FlowGraph flowgraph;

    private BasicBlock global_entry_block;

    private IAnalysisLatticeElement<StateType, ContextType, CallEdgeType> the_analysis_lattice_element;

    private WorkList<ContextType> worklist;

    private CallDependencies<ContextType> deps;

    private AbstractNode current_node;

    private StateType current_state;

    private URL htmlFile = null;


    private Map<BasicBlock, Integer> analyzedBlocks = new HashMap<>();
    private Map<AbstractNode, Integer> analyzedNodes = new HashMap<>();

    /**
     * Messages are disabled during fixpoint iteration and enabled in the subsequent scan phase.
     */
    private boolean messages_enabled;

    private SolverInterface c;

    /**
     * Interface to solver used while evaluating transfer functions.
     * Provides callbacks from transfer functions to solver state.
     */
    public class SolverInterface {

        private SolverInterface() {
        }

        /**
         * Returns the node currently being visited.
         */
        public AbstractNode getNode() {
            if (current_node == null)
                throw new AnalysisException("Unexpected call to getNode");
            return current_node;
        }

        /**
         * Returns the current abstract state.
         */
        public StateType getState() {
            return current_state;
        }

        /**
         * Sets the current abstract state.
         */
        public void setState(StateType state) {
            current_state = state;
        }

        /**
         * Runs the given supplier function with the given state set to current.
         */
        public <T> T withState(StateType state, Supplier<T> fun) {
            StateType old = current_state;
            current_state = state;
            T res = fun.get();
            current_state = old;
            return res;
        }

        /**
         * Runs the given function with the given state set to current.
         */
        public void withState(StateType state, Runnable fun) {
            withState(state, () -> {
                // this is sketchy, but doing for TESTing
                // erikt was here
                try {
                    fun.run();
                } catch(Exception e){

                }
                return null;
            });
        }

        /**
         * Runs the given supplier function with the given state and node set to current.
         */
        public <T> T withStateAndNode(StateType state, AbstractNode node, Supplier<T> fun) {
            // TODO merge implementation with withState?
            // TODO implement return-void variant?
            AbstractNode old_node = current_node;
            StateType old_state = current_state;
            current_state = state;
            current_node = node;
            T res = fun.get();
            current_node = old_node;
            current_state = old_state;
            return res;
        }

        /**
         * Returns the flow graph.
         */
        public FlowGraph getFlowGraph() {
            return flowgraph;
        }

        /**
         * Returns the analysis object.
         */
        public AnalysisType getAnalysis() {
            return analysis;
        }

        /**
         * Returns the analysis lattice element.
         */
        public IAnalysisLatticeElement<StateType, ContextType, CallEdgeType> getAnalysisLatticeElement() {
            return the_analysis_lattice_element;
        }

        /**
         * Returns the monitoring object of the analysis.
         */
        public MonitoringType getMonitoring() {
            return analysis.getMonitoring();
        }

        /**
         * Returns true if in message scanning phase.
         */
        public boolean isScanning() {
            return messages_enabled;
        }

        /**
         * Merges <code>state</code> into the entry state of <code>block</code> in context <code>context</code>
         * and updates the work list accordingly.
         * The given state may be modified by this operation.
         * Ignored if in scan phase.
         */
        public void propagateToBasicBlock(StateType state, BasicBlock block, ContextType context) {
            if (messages_enabled)
                return;
            propagateAndUpdateWorklist(state, block, context, false);
        }

        /**
         * Propagates dataflow and updates the worklist if needed.
         */
        private boolean propagateAndUpdateWorklist(StateType state, BasicBlock block, ContextType context, boolean localize) {
            boolean changed = propagate(state, new BlockAndContext<>(block, context), localize);
            if (changed) {
                addToWorklist(block, context);
            }
            return changed;
        }

        /**
         * Propagates dataflow.
         * Does *not* modify the worklist
         *
         * @return true iff the destination state changed
         */
        public boolean propagate(StateType state, BlockAndContext<ContextType> to, boolean localize) {
            BlockAndContext<ContextType> from = new BlockAndContext<>(state.getBasicBlock(), state.getContext()); // save the block and context; they change during the call to propagate
            getMonitoring().visitPropagationPre(from, to);
            MergeResult res = the_analysis_lattice_element.propagate(state, to, localize);
            boolean changed = res != null;
            getMonitoring().visitPropagationPost(from, to, changed);
            the_analysis_lattice_element.getCallGraph().registerBlockContext(to);
            if (changed) {
                analysis.getMonitoring().visitNewFlow(to.getBlock(), to.getContext(), the_analysis_lattice_element.getState(to), res.getDiff(), "CALL");
                if (log.isDebugEnabled())
                    log.debug("New flow at block " + to.getBlock().getIndex() + " node "
                            + to.getBlock().getFirstNode().getIndex() + ", context " + to.getContext()
                            + (res.getDiff() != null ? ", diff:" + res.getDiff() : ""));
            }
            return changed;
        }

        /**
         * Adds the given location to the worklist.
         */
        public void addToWorklist(BasicBlock block, ContextType context) {
            if (worklist.add(worklist.new Entry(block, context)))
                deps.incrementFunctionActivityLevel(BlockAndContext.makeEntry(block, context));
            if (sync != null)
                sync.markPendingBlock(block);
        }

        /**
         * Merges the edge state into the entry state of the callee in the given context and updates the work list accordingly.
         * Also updates the call graph and triggers reevaluation of ordinary/exceptional return flow.
         * The given state may be modified by this operation.
         * Ignored if in scan phase.
         */
        public void propagateToFunctionEntry(AbstractNode call_node, ContextType caller_context, StateType edge_state,
                                             ContextType edge_context, BasicBlock callee_entry, boolean implicit) {
            if (messages_enabled)
                return;
            if (call_node.getIndex()==84){
                String erikwazhere="";
            }
            CallGraph<StateType, ContextType, CallEdgeType> cg = the_analysis_lattice_element.getCallGraph();
            // add to existing call edge
            if (cg.addTarget(call_node, caller_context, callee_entry, edge_context, edge_state, sync, analysis, c.getMonitoring())) {
                // new flow at call edge, transform it relative to the function entry states and contexts
                ContextType callee_context = edge_state.transform(cg.getCallEdge(call_node, caller_context, callee_entry, edge_context),
                        edge_context, the_analysis_lattice_element.getStates(callee_entry), callee_entry);
                cg.addSource(call_node, caller_context, callee_entry, callee_context, edge_context, implicit);
                // propagate transformed state into function entry
                if (propagateAndUpdateWorklist(edge_state, callee_entry, callee_context, true)) {
                    // charge the call edge
                    deps.chargeCallEdge(call_node.getBlock(), caller_context, edge_context, callee_entry, callee_context);
                }
            }
            ContextType callee_context = edge_context; // TODO: update this if State.transform doesn't just return the edge context as callee context
            // process existing ordinary/exceptional return flow
            StateType stored_state = current_state;
            AbstractNode stored_node = current_node;
            current_state = null;
            current_node = null;
            analysis.getNodeTransferFunctions().transferReturn(call_node, callee_entry, caller_context, callee_context, edge_context, implicit);
            current_state = stored_state;
            current_node = stored_node;
        }

        /**
         * Transforms the given state inversely according to the call edge.
         */
        public void returnFromFunctionExit(StateType return_state, AbstractNode call_node, ContextType caller_context,
                                           BasicBlock callee_entry, ContextType edge_context, boolean implicit) {
            CallEdgeType edge = the_analysis_lattice_element.getCallGraph().getCallEdge(call_node, caller_context, callee_entry, edge_context);
            if (return_state.transformInverse(edge, callee_entry, return_state.getContext())) {
                // need to re-process the incoming flow at function entry
                propagateToFunctionEntry(call_node, caller_context, edge.getState(), edge_context, callee_entry, implicit);
            }
        }

        /**
         * Checks whether the given edge is charged.
         * Always returns true if charged edges are disabled.
         */
        public boolean isCallEdgeCharged(BasicBlock caller, ContextType caller_context, ContextType edge_context,
                                         BlockAndContext<ContextType> callee_entry) {
            return deps.isCallEdgeCharged(caller, caller_context, edge_context, callee_entry.getBlock(), callee_entry.getContext());
        }

        public void setNode(AbstractNode node) {
            current_node = node;
        }

        public WorkList<ContextType> getWorklist() {
            return worklist;
        }
    }

    /**
     * Constructs a new solver.
     */
    public GenericSolver(AnalysisType analysis, SolverSynchronizer sync) {
        this.analysis = analysis;
        this.sync = sync;
        Locale.setDefault(Locale.US); // there be dragons if this is not set...
    }

    /**
     * Initializes the solver for the given flow graph and HTML document.
     */
    public void init(FlowGraph fg, Source document, URL htmlFile) {
        if (the_analysis_lattice_element != null)
            throw new IllegalStateException("init() called repeatedly");
        flowgraph = fg;
        global_entry_block = fg.getEntryBlock();
        the_analysis_lattice_element = analysis.makeAnalysisLattice(fg);
        analysis.initContextSensitivity(fg);
        c = new SolverInterface();
        analysis.setSolverInterface(c);
        // initialize worklist
        worklist = new WorkList<>(analysis.getWorklistStrategy());
        deps = new CallDependencies<>();
        current_node = global_entry_block.getFirstNode();
        // build initial state
        StateType initialState = analysis.getInitialStateBuilder().build(global_entry_block, c, document);
        c.propagateToBasicBlock(initialState, initialState.getBasicBlock(), initialState.getContext());
        this.htmlFile = htmlFile;
    }

    public static void clearTheFile(File fileToClear) {
        try {
            FileWriter fwOb = new FileWriter(fileToClear, false);
            PrintWriter pwOb = new PrintWriter(fwOb, false);
            pwOb.flush();
            pwOb.close();
            fwOb.close();
        } catch (IOException ioe) {
            System.out.println(ioe);
            ioe.printStackTrace();
            throw new RuntimeException("Stopping because file " + fileToClear.toString() + "locked.");
        }
    }

    /**
     * Runs the solver.
     */
    public void solve() {
        Map<BasicBlock,Integer> visits = new HashMap<>();
        String terminatedEarly = null;
        StringBuffer logbuf = new StringBuffer();
        int instCount = 0, threshCnt = 0, printCnt = 0;
        //File fileLogSolve = new File("tajs-solve.addFiles");
        //Path pathLogSolve = Paths.get(fileLogSolve.toURI());
        Map<String, Integer> sourceLinesTracker = new HashMap<>();
        //clearTheFile(fileLogSolve);

        //printFlowGraph();

        //logTimeStamp(logbuf, pathLogSolve, true);
        System.out.flush();
        System.out.println("***********************************111111**********************************************************");
        //System.out.println(flowgraph.toStringFG(true));
        System.out.println("************************************111111*********************************************************");
        System.out.flush();

        String lastSrcPath = "";
        try {
            String nextFunctionToCall = "";
            // iterate until fixpoint
            boolean hitFirstForceCall = false;

            block_loop:
            while (!worklist.isEmpty()) {
                boolean allSearched = true;
                int analyzedCnt = 0, totsAnalyzed =0;
                for (Function func :flowgraph.getFunctions()){
                    if (!flowgraph.isHostEnvironmentSource(func.getSourceLocation())) {
                        if (func.isFullyAnalyzed(flowgraph)) {
                            analyzedCnt++;
                        } else {
                            allSearched = false;
                        }
                        totsAnalyzed++;
                    }
                }
                if (allSearched){
                    //break;
                }
                String analysisStatus = "" + analyzedCnt + " of " + flowgraph.getFunctions().size();

                if (!analysis.getMonitoring().allowNextIteration()) {
                    terminatedEarly = "Terminating fixpoint solver early and unsoundly!";
                    break;
                }

                if (sync != null) {
                    sync.waitIfSingleStep();
                    log.warn("Worklist: " + worklist);
                }
                /*String worklist_out = worklist.toString();
                if (!worklist_out.isEmpty()) {
                    addFiles.info("Worklist: " + worklist);
                }*/

                // pick a pending entry
                WorkList<ContextType>.Entry p = worklist.removeNext();
                if (p == null)
                    continue; // entry may have been removed
                BasicBlock block = p.getBlock();
                block.increaseTimesAccessed();
                if (visits.containsKey(block)){
                    visits.put(block,visits.get(block) + 1);
                } else{
                    visits.put(block,1);
                }

                ContextType context = p.getContext();

                if (sync != null)
                    sync.markActiveBlock(block);
                deps.decrementFunctionActivityLevel(BlockAndContext.makeEntry(block, context));
                StateType state = the_analysis_lattice_element.getState(block, p.getContext());

                State tstate = (State) current_state;
                int level_cnt = 0;

                /** block printing and scopechain padding **/
                String succs = "--> [";
                for (BasicBlock bb : block.getSuccessors()){
                    succs += " " + bb.getIndex();
                }
                succs += " ]";
                String scopechain_spaces = "";
                if (tstate != null && tstate.getExecutionContext() != null) {

                    for (Iterator<Set<ObjectLabel>> it = ScopeChain.iterable(tstate.getExecutionContext().getScopeChain()).iterator(); it.hasNext(); ) {
                        Set<ObjectLabel> sc = it.next();
                        level_cnt++;
                        scopechain_spaces += "    ";
                    }
                }
                System.out.println("\t" + scopechain_spaces + "Block "+ block.getIndex() + " level=" + level_cnt +  " visits = " + visits.get(block) + " Analysis:" + analysisStatus +"\t\t\t\t" + succs);


                if (state == null)
                    throw new AnalysisException();
                // basic block transfer
                current_state = state.clone();
                analysis.getMonitoring().visitBlockTransferPre(block, current_state);
                if (global_entry_block == block)
                    current_state.localize(null); // use *localized* initial state
                if (Options.get().isIntermediateStatesEnabled())
                    if (log.isDebugEnabled())
                        log.debug("Before block transfer: " + current_state);
                try {
                    try {
                        int blocks_procd = 0;

                        //Print out BLOCK being analyzed
                        //System.out.println(block.toStringFG(flowgraph, true));

                        for (AbstractNode n : block.getNodes()) {
                            current_node = n;

                            if (current_node.getSourceLocation().toString().contains("call-all-functions")){
                                if (current_node instanceof ReadVariableNode){
                                    ReadVariableNode rvn = (ReadVariableNode) current_node;

                                    if (rvn.toString().contains("anonfun")){
                                        String erikwazhere="";

                                    }
                                    nextFunctionToCall = rvn.getVariableName();
                                    if (!hitFirstForceCall) {
                                        System.out.println("++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++");
                                        System.out.println("++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++");
                                        System.out.println("++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++");
                                        System.out.println("\n\n+++++  \t\t" + scopechain_spaces + "READING FOR CALL OF " + nextFunctionToCall + "\n\n");
                                        System.out.println("++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++");
                                        System.out.println("++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++");
                                        System.out.println("++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++");
                                        hitFirstForceCall=true;
                                    } else {
                                        System.out.println("\t\t" + scopechain_spaces + "READING FOR CALL OF " + nextFunctionToCall);
                                    }
                                }
                                if (current_node instanceof CallNode && !nextFunctionToCall.isEmpty()){
                                    CallNode cn = (CallNode) current_node;
                                    System.out.println(cn);
                                    if (cn.toString().contains("call[v27,'random',v29]")){
                                        String erikwazhere="";
                                    }
                                    if (cn.getFunctionRegister() != -1) {
                                        Value fnreg = ((State) current_state).getRegisters().get(cn.getFunctionRegister());
                                        boolean previouslyAnalyzed = current_node.hasBeenAccessed();

                                        if (!previouslyAnalyzed) {
                                            for (ObjectLabel ol : fnreg.getObjectLabels()) {
                                                if (ol.getKind() == ObjectLabel.Kind.FUNCTION && ol.hasFunction()) {
                                                    previouslyAnalyzed |= ol.getFunction().getEntry().hasBeenAccessed();
                                                }
                                            }
                                        }
                                        // if previously analyzed skip it.
                                        if (previouslyAnalyzed) {
                                            System.out.println("\t\t" + scopechain_spaces + "SHOULD BE SKIPPING CALL and ANALYSIS of " + nextFunctionToCall);
                                            c.propagateToBasicBlock(current_state.clone(), block.getSingleSuccessor(), context);
                                            continue block_loop;
                                        } else {
                                            // fall through the procesing logic to force call
                                            System.out.println("\t\t" + scopechain_spaces + "FORCING CALL and ANALYSIS of " + nextFunctionToCall);
                                        }
                                        //Value funcreg = ((State)current_state).getRegisters().get(cn.getFunctionRegister());
                                    }
                                }
                                String erikwazhere="";
                            }
                            if (current_node.toString().contains("anonymous>()")){
                                String erikwazhere="";
                            }
                            System.out.println("\t\t" + scopechain_spaces + current_node.getIndex() + " " + current_node
                                    + " " + current_node.getSourceLocation().toString());

                            n.increaseTimesAccessed();

                            if (current_state.isNone()) {
                                continue block_loop;
                            }

                            String srcPath = n.getSourceLocation().toUserFriendlyString(false);
                            if (sourceLinesTracker.containsKey(srcPath)) {
                                if (sourceLinesTracker.get(srcPath) < n.getSourceLocation().getLineNumber()) {
                                    sourceLinesTracker.put(srcPath, n.getSourceLocation().getLineNumber());
                                }
                            } else {
                                sourceLinesTracker.put(srcPath, n.getSourceLocation().getLineNumber());
                            }
                            String srcFN = (new File(srcPath)).getName();
                            instCount++;

                            if (instCount % 1000 == 0) {
                                printCnt = checkPrintCnt(instCount, printCnt);

                                //threshCnt = checkThreshCnt(logbuf, instCount, threshCnt, pathLogSolve, n, srcFN);
                            } else {
                                if (instCount == 1) {
                                    //addFiles.warn(n.getSourceLocation());
                                    System.out.print(String.format("%3d", 0));

                                    logbuf.append(instCount + ")" + n.getIndex() + " " + n + ":" + srcFN + ":" + n.getSourceLocation().getLineNumber() + ":" + n.getSourceLocation().getColumnNumber() + "\n");
                                } else {
                                    // logbuf.append(instCount +  ")" + n.getIndex() + " " + n + ":" + srcFN + ":" + n.getSourceLocation().getLineNumber() + ":" + n.getSourceLocation().getColumnNumber() +"\n");
                                }
                            }
                            if (current_node instanceof ReturnNode) {
                                String erikwazhere = "";
                            }
                            //System.out.println(instCount + ")" + n.getIndex() + " " + n + ":" + srcFN + ":" + n.getSourceLocation().getLineNumber() + ":" + n.getSourceLocation().getColumnNumber() + "\n");
                            //System.out.println(logbuf);
                            //addFiles.warn(logbuf);
                            //logbuf.setLength(0);

                            if (log.isDebugEnabled())
                                log.debug("Visiting node " + current_node.getIndex() + ": "
                                        + current_node + " at " + current_node.getSourceLocation());

                            analysis.getMonitoring().visitNodeTransferPre(current_node, current_state);
                            try {
                                /********************************************************************************************
                                 *
                                 *  DEBUG BREAK RULES!!!
                                 *
                                 ********************************************************************************************/

                                if (block.getIndex() == 366 ) { 
                                    //System.out.println(instCount +  ")" + n.getIndex() + " " + n + ":" + srcFN + ":" + n.getSourceLocation().getLineNumber() + ":" + n.getSourceLocation().getColumnNumber() +"\n");
                                    //System.out.println("\t\t" + scopechain_spaces + "---debug--- block=" + block.getIndex() + " node = " + current_node.getIndex() + " " + current_node.toString());
                                    String erikwazhere = "";
                                    //System.out.println(current_node.isRegistersDone());
                                }

                                if (current_node.getSourceLocation().toString().contains("call-all-functions")){

                                    String erikwazhere="";
                                    //System.out.println(current_node);
                                }
                                if (current_node.toString().contains("call[v13,'add',v15,-]")){
                                    String erikwazhere="";
                                }
                                try {

                                    // !!!!!!!!!!!!!! TRANSFER HERE
                                    analysis.getNodeTransferFunctions().transfer(current_node);

                                    if (block.getIndex()==6677777){
                                        Map<ContextType, StateType> bstate = the_analysis_lattice_element.getStates(block);
                                        String erikwazhere="";
                                        //System.out.println(current_node);
                                    }
                                } catch (Exception ex){
                                    System.out.flush();
                                    System.out.println("Error occured with \n\tblock=" + block.getIndex() + "\n\tnode = " + current_node.getIndex() + "\n\t" + current_node.toString() +  " " + current_node.getSourceLocation().toString());
                                    throw ex;
                                }
                                blocks_procd++;
                            } catch (AnalysisLimitationException e) {
                                current_node.errorWasCaught();
                                block.errorWasCaught();
                                if (Options.get().isTestEnabled() && !Options.get().isAnalysisLimitationWarnOnly()) {
                                    throw e;
                                } else {
                                    throw e;
                                    /*terminatedEarly = String.format("Stopping analysis prematurely: %s", e.getMessage());
                                    break block_loop;*/
                                }

                            } finally {

                                //condPrintState(instCount);

                                analysis.getMonitoring().visitNodeTransferPost(current_node, current_state);

                                /***
                                 *  ADDings this to try to fix error below, but no lcuk
                                 *  Exception in thread "main" java.lang.IllegalArgumentException: Non-Function object label: @Object.prototype.propertyIsEnumerable[native]
                                 at dk.brics.tajs.lattice.ObjectLabel.getFunction(ObjectLabel.java:236)
                                 at dk.brics.tajs.solver.GenericSolver.solve(GenericSolver.java:545)
                                 at dk.brics.tajs.Main.run(Main.java:309)
                                 at dk.brics.tajs.Main.main(Main.java:105)
                                 */
//                                if (current_node.getSourceLocation().toString().contains("call-all-functions")
//                                        && current_node instanceof WriteVariableNode){
//                                    Value wval = ((State)current_state).getRegisters().get(((WriteVariableNode) current_node).getValueRegister());
//                                    wval.setInternalFuncPointer();
//                                }
                                /*if (current_node.getIndex() == 64){
                                    State cs = (State) current_state;
                                    //Object label put into store at 119
                                    System.out.println("##################### 64 Current Store ####################");
                                    System.out.println(cs.getStore().entrySet());
                                }*/

                                /**/
                            }
                            if (current_state.isNone()) {
                                //System.out.println("~~~~~~~~~~~~~~NO STATE FOUND.....WHY!!!!!!!!!!!!!!!!!!! " + n);

                                log.debug("No non-exceptional flow");
                                continue block_loop;
                            }
                            if (Options.get().isIntermediateStatesEnabled())
                                if (log.isDebugEnabled())
                                    log.debug("After node transfer: " + current_state.toStringBrief());
                        } // end cycle through abstract nodes within a block

                        StateType test = the_analysis_lattice_element.getState(block, p.getContext());
                        if (test == null || test.isNone()) {
                            //System.out.println("___SOLVE____NO STATE FOUND.....WHY!!!!!!!!!!!!!!!!!!! " + block);
                        }
                        if (blocks_procd != block.getNodes().size() && !current_node.getSourceLocation().toString().contains("call-all-functions")) {
                            System.out.println("\t\t+++++++++++++-----> Difference between actual and number of blocks " + blocks_procd + " " + block.getNodes().size());
                        }
                    } finally {
                        analysis.getMonitoring().visitBlockTransferPost(block, current_state);
                    }
                    // edge transfer
                    for (Iterator<BasicBlock> i = block.getSuccessors().iterator(); i.hasNext(); ) {
                        BasicBlock succ = i.next();
                        StateType s = i.hasNext() ? current_state.clone() : current_state;
                        ContextType new_context = analysis.getEdgeTransferFunctions().transfer(block, succ, s);
                        if (new_context != null) {
                            try {
                                c.propagateToBasicBlock(s, succ, new_context);
                            } catch (IndexOutOfBoundsException iob){
                                String erikwazhere="";
                            }
                        }

                    }

                } finally {
                    // discharge incoming call edges if the function is now inactive
                    deps.dischargeIfInactive(BlockAndContext.makeEntry(block, context));
                }
                if (sync != null)
                    sync.unMarkActiveBlock();

                /*if (worklist.isEmpty()){
                    //going to exit worklist
                    System.out.println("BEEP BEEP!!!");
                    for (Function function : flowgraph.getFunctions()) {
                        if (!function.isFullyAnalyzed(flowgraph) && !flowgraph.isHostEnvironmentSource(function.getSourceLocation())){

                            System.out.println("\tBING BING BANG BING BONG");
                            System.out.println("\t" + function + " " + function.getName() + " " +function.getIndex() + " " + function.getSourceLocation());
                            StateType new_state = current_state.clone();
                            BasicBlock bb = function.getEntry();
                            ContextType new_context = analysis.getEdgeTransferFunctions().transfer(block, bb, new_state);
                            if (new_context != null){
                                c.propagateToBasicBlock(new_state , bb, new_state.getContext());
                            }

                            //worklist.add(context, function.getEntry())
                        }
                    }

                }*/

            } //end while
        } finally {
            //System.out.println(logbuf);
            /*try {
                Files.write(pathLogSolve, logbuf.toString().getBytes(), StandardOpenOption.APPEND);
                //System.out.println(logbuf.toString());
                logbuf.setLength(0);
            } catch (IOException e) {
                addFiles.warn("Error", e);
            }*/
            Iterator it = sourceLinesTracker.entrySet().iterator();
            while (it.hasNext()) {
                Map.Entry pair = (Map.Entry) it.next();
                log.warn("\n" + pair.getKey() + " Max Line Processed=" + pair.getValue());
            }

            analysis.getMonitoring().visitIterationDone();
        }
        if (terminatedEarly != null) {
            log.warn(terminatedEarly);
        } else {
            deps.assertEmpty();
        }
        System.out.println(" ****** Finished Solving covering " + instCount + " loops ******");
        messages_enabled = true;
    }

    private int checkThreshCnt(StringBuffer logbuf, int instCount, int threshCnt, Path pathLogSolve, AbstractNode n, String srcFN) {
        threshCnt++;
        logbuf.append(instCount + ")" + n.getIndex() + " " + n + ":" + srcFN + ":" + n.getSourceLocation().getLineNumber() + ":" + n.getSourceLocation().getColumnNumber() + "\n");
        try {
            Files.write(pathLogSolve, logbuf.toString().getBytes(), StandardOpenOption.APPEND);
            //System.out.println(logbuf.toString());
            logbuf.setLength(0);
        } catch (IOException e) {
            log.warn("Error", e);
        }
        if (threshCnt % 50 == 0) {
            //System.out.println("");
            //System.out.print(String.format("%3d", threshCnt));
        }
        return threshCnt;
    }

    private int checkPrintCnt(int instCount, int printCnt) {
        if ((instCount / 1000) % 10 == 0) {
            printCnt += 1;
            if (printCnt % 10 == 0) {
                printCnt = 0;
            }
            System.out.print(String.format("%d", printCnt));
        } else {
            System.out.print("|");
        }
        System.out.flush();
        return printCnt;
    }

    private void logTimeStamp(StringBuffer logbuf, Path pathLogSolve, boolean isStarting) {
        try {

            String timeStamp = new SimpleDateFormat("yyyy.MM.dd.HH.mm.ss").format(new Timestamp(System.currentTimeMillis()));
            if (isStarting) {
                log.warn("Starting At: " + timeStamp + "");
            } else {
                log.warn("Ending At: " + timeStamp + "");
            }

            timeStamp += "\n";
            Files.write(pathLogSolve, timeStamp.getBytes(), StandardOpenOption.APPEND);
            logbuf.setLength(0);
        } catch (IOException e) {
            log.warn("Error", e);
        }
    }

    private void condPrintState(int instCount, AbstractNode node) {
        State cs = (State) current_state;

        boolean found = false;
        Collection<String> keylist = new TreeSet<>(Collator.getInstance());
        for (Entry<ObjectLabel, Obj> ent : cs.getStore().entrySet()) {
            String outstr = "";

            if (ent.getKey().toString().contains("HTMLDivElement")) {
                Value ihval = ent.getValue().getProperties().get("innerHTML");
                if (ihval != null) {
                    //System.out.println("\t" + current_node );
                    found = true;
                    //outstr += ("\t\t" + ihval.valueHistory);
                }
            }

            Obj obj = ent.getValue();
            boolean littles = false;
            if (!obj.getProperties().entrySet().isEmpty() && ent.getKey().toString().contains("global") || ent.getKey().toString().contains("HTMLDivElement")) {

                for (Entry<String, Value> ent2 : obj.getProperties().entrySet()) {
                    if (ent2.getKey().contains("innerHTML")) {
                        outstr += ("\tStored:" + ent.getKey().toString() + " " + ent.getKey().hashCode() + "\n");
                        outstr += ("\t\t" + ent2.getKey() + " '" + ent2.getValue().valueHistory + "'\n");
                        found = true;
                    } else {
                        //outstr += ("\t\t" + ent2.getKey());
                    }
                    littles = true;
                }
            }
            //String fnName = ent.getValue();

            if (littles) {
                outstr += "\n";
            }
            keylist.add(outstr);
        }

        if (found) {
            //System.out.println((instCount) + " " + current_node);
            for (String s : keylist) {

                System.out.print(s);
            }
        } else {
            if (node instanceof CallNode) {
                CallNode cn = (CallNode) node;
                //System.out.println("\t\tFor the CALLNODE!!!!!!!NOTHING!!!!!!! Buwahahaha\n");
                for (int i = 0; i < cn.getNumberOfArgs(); i++) {
                    Value v = cs.getRegisters().get(cn.getArgRegister(i));
                    //System.out.println("\t\t\targ=" + i + " reg=" + cn.getArgRegister(i) + " " + v.toString());
                    for (ObjectLabel ol : v.getObjectLabels()) {

                        //System.out.println("\t\t\t\t" + ol.hashCode() + " " + cs.getObject(ol, false));
                    }
                }
            }
        }
    }
/*

    private StringBuilder printFunctionFlow(BasicBlock block, Set<BasicBlock> visited, boolean allBlocksInFunctionHaveState, StringBuilder fnBlocks){
        if (block.getIndex() == 78){
            String erikwazhere="";
        }
        visited.add(block);
        boolean processBlock = false;
        for (AbstractNode node : block.getNodes()) {
            // skip this block, b/c it's probably a TAJS block, or we have a bug :)
            if (node.getSourceLocation().getEndLineNumber() == 0) {
                continue;
            }
            */
/*            if (node instanceof ReturnNode || node instanceof ExceptionalReturnNode ||
                                node instanceof CallNode || node instanceof BeginForInNode || node instanceof EndForInNode){
                            continue;
                        }
            if (node instanceof ReturnNode || node instanceof ExceptionalReturnNode ||
                    node instanceof BeginForInNode || node instanceof EndForInNode){
                continue;
            }*//*

            processBlock = true;
        }
        //skipping because all blocks are either TAJS code or made up of nodes that probably do not have a state.
        if (processBlock){
            String stateInfo = "";
            boolean currentBlockHasState = false;
            for (Entry<ContextType, StateType> me : the_analysis_lattice_element.getStates(block).entrySet()) {
                if (!me.getValue().isNone()) {
                    if (stateInfo.isEmpty()) {
                        stateInfo = "[ ";
                    }
                    State st = (State) me.getValue();
                    stateInfo += st.toSimpleString();
                    currentBlockHasState = true;
                }
            }

            if (currentBlockHasState) {
                stateInfo += "]";
            } else {
                stateInfo = "--<[ NO STATE ]>--";
            }

            if (allBlocksInFunctionHaveState) {
                fnBlocks.append(block.getIndex() + " ");
            } else {

            }
            fnBlocks.append("\tBlock #" + block.getIndex() + " with " + block.getNodes().size() + " node" + "  " + stateInfo +  " " + block.hasBeenAccessed() + "\n");
            String blockStartLine = "";
            String blockEndLine = "";

            for (AbstractNode node : block.getNodes()) {

                // gather some state info
                fnBlocks.append("\t\t" + "node#" + node.getIndex() + " " + node
                        + " " + node.getSourceLocation().getLineNumber()
                        + ":" + node.getSourceLocation().getColumnNumber() + "\n");
                if (!currentBlockHasState && node.getSourceLocation().getLineNumber() >= 0) {
                    fnBlocks.append("\t\t" + "node#" + node.getIndex() + " " + node
                            + " " + node.getSourceLocation().getLineNumber()
                            + ":" + node.getSourceLocation().getColumnNumber() + "\n");
                } else {
                    if (blockStartLine.isEmpty()){
                        blockStartLine = node.getSourceLocation().toShortString();
                    }
                    blockEndLine = node.getSourceLocation().toShortString();
                }
                //sourceTracker.add(node);

            }
            if (!blockStartLine.isEmpty()) {
                fnBlocks.deleteCharAt(fnBlocks.length()-1);
                fnBlocks.append(" ");
                fnBlocks.append(blockStartLine);

                if (!blockStartLine.equals(blockEndLine)) {

                    fnBlocks.append("->");
                    fnBlocks.append(blockEndLine);
                }
                fnBlocks.append("\n");
            }

            for (BasicBlock nextBlock: block.getSuccessors()){

                if (!visited.contains(nextBlock)){
                    //System.out.println("" +  block.getIndex() + " " );
                    fnBlocks = printFunctionFlow(nextBlock, visited, allBlocksInFunctionHaveState, fnBlocks);
                }

            }
        }

        return fnBlocks;
    }

    private void printFlowGraph2() {
        int instCount = 0;
        StringBuffer sb = new StringBuffer();
        SourceTracker sourceTracker = new SourceTracker();
        // Let's send this to a file instead, blah.html.parsed nodes, then can process from python
        System.out.println("*********************************************************************************************");

        // so, if it has no STATE then it probably wasn't analyzed? and has no flow?

        PrintWriter writer = null;
        try {

            if (htmlFile != null) {
                File f = new File(htmlFile.toURI());
                writer = new PrintWriter(f.getAbsolutePath() + ".parsed");
            }
            StringBuilder fnBlocks = new StringBuilder();
            fnBlocks = printFunctionFlow(flowgraph.getEntryBlock(), new HashSet<>(), false, fnBlocks);
            System.out.print(fnBlocks);
            */
/*for (Function function : flowgraph.getFunctions()) {

                StringBuilder fnTitle = new StringBuilder();

                boolean functionHasOneState = false;
                boolean allBlocksInFunctionHaveState = true;
                Path fpath = FileSystems.getDefault().getPath(function.getSourceLocation().toUserFriendlyString(false));

                if (fpath.getFileName().toString().startsWith("HOST")) {
                    continue;
                }
                if (function.getSourceLocation().toShortString(true).isEmpty()) {
                    String erikwzhere = "";
                }
                String fnName = function.toString();
                if (function.isMain()) {
                    fnName = "main body";
                }

                fnTitle.append(fnName + " in '" + fpath.getFileName() + "' " + function.getSourceLocation().toShortString(true));

                //determine if if all blocks in function have 1 or more states
                for (BasicBlock block : function.getBlocks()) {
                    String stateInfo = "";
                    boolean currentBlockHasState = !the_analysis_lattice_element.getStates(block).isEmpty();
                    for (AbstractNode node : block.getNodes()) {

                    }
                    allBlocksInFunctionHaveState &= currentBlockHasState;
                    functionHasOneState |= currentBlockHasState;
                }

                // if all blocks within function have no state, then probably not called so only show fn
                if (!functionHasOneState) {
                    continue;
                }



                if (!functionHasOneState) {
                    fnTitle.append(" !!!! NO STATE FOR FUNCTIONS, FUNCTION NOT ANALYZED !!!\n");
                    System.out.print(fnTitle);
                    System.out.print(fnBlocks);
                } else {
                    //fnTitle.append(" {...Analyzed...}\n");
                    System.out.println(fnTitle);
                    System.out.print(fnBlocks);
                }
            }*//*

        } catch (IOException ioe) {
            ioe.printStackTrace();
        } catch (URISyntaxException e) {
            e.printStackTrace();
        } finally {
            if (writer != null) {
                writer.close();
            }
        }
        sourceTracker.analyzeLinesParsed();
        System.out.println("*********************************************************************************************");
    }

    private void printFlowGraph() {
        int instCount = 0;
        StringBuffer sb = new StringBuffer();
        SourceTracker sourceTracker = new SourceTracker();
        // Let's send this to a file instead, blah.html.parsed nodes, then can process from python
        System.out.println("*********************************************************************************************");

        // so, if it has no STATE then it probably wasn't analyzed? and has no flow?

        PrintWriter writer = null;
        try {

            if (htmlFile != null) {
                File f = new File(htmlFile.toURI());
                writer = new PrintWriter(f.getAbsolutePath() + ".parsed");
            }

            for (Function function : flowgraph.getFunctions()) {
                StringBuilder fnTitle = new StringBuilder();
                StringBuilder fnBlocks = new StringBuilder();
                boolean functionHasOneState = false;
                boolean allBlocksInFunctionHaveState = true;
                Path fpath = FileSystems.getDefault().getPath(function.getSourceLocation().toUserFriendlyString(false));

                if (fpath.getFileName().toString().startsWith("HOST")) {
                    continue;
                }
                if (function.getSourceLocation().toShortString(true).isEmpty()) {
                    String erikwzhere = "";
                }
                String fnName = function.toString();
                if (function.isMain()) {
                    fnName = "main body";
                }

                fnTitle.append(function.getIndex() + " " + fnName + " in '" + fpath.getFileName() + "' " + function.getSourceLocation().toShortString(true));

                //determine if if all blocks in function have 1 or more states
                for (BasicBlock block : function.getBlocks()) {
                    String stateInfo = "";
                    boolean currentBlockHasState = !the_analysis_lattice_element.getStates(block).isEmpty();
                    for (AbstractNode node : block.getNodes()) {

                    }
                    allBlocksInFunctionHaveState &= currentBlockHasState;
                    functionHasOneState |= currentBlockHasState;
                }

                // if all blocks within function have no state, then probably not called so only show fn
                if (!functionHasOneState) {
                    continue;
                }

                for (BasicBlock block : function.getBlocks()) {
                    if (block.getIndex() == 78){
                        String erikwazhere="";
                    }
                    boolean skipBlock = true;
                    for (AbstractNode node : block.getNodes()) {
                        // skip this block, b/c it's probably a TAJS block, or we have a bug :)
                        if (node.getSourceLocation().getEndLineNumber() == 0){
                            continue;
                        }
                        if (node instanceof ReturnNode || node instanceof ExceptionalReturnNode ||
                                node instanceof CallNode || node instanceof BeginForInNode || node instanceof EndForInNode){
                            continue;
                        }
                        if (node instanceof ReturnNode || node instanceof ExceptionalReturnNode ||
                                node instanceof BeginForInNode || node instanceof EndForInNode){
                            continue;
                        }
                        skipBlock = false;

                    }
                    //skipping because all blocks are either TAJS code or made up of nodes that probably do not have a state.
                    if (skipBlock){
                        continue;
                    }
                    String stateInfo = "";
                    boolean currentBlockHasState = false;
                    for (Entry<ContextType, StateType> me : the_analysis_lattice_element.getStates(block).entrySet()) {
                        if (!me.getValue().isNone()) {
                            if (stateInfo.isEmpty()) {
                                stateInfo = "[ ";
                            }
                            State st = (State) me.getValue();
                            stateInfo += st.toSimpleString();
                            currentBlockHasState = true;
                        }
                    }

                    if (currentBlockHasState) {
                        stateInfo += "]";
                    } else {
                        stateInfo = "--<[ NO STATE ]>--";
                    }

                    if (allBlocksInFunctionHaveState) {
                        fnBlocks.append(block.getIndex() + " ");
                    } else {
                        fnBlocks.append("\tBlock #" + block.getIndex() + " with " + block.getNodes().size() + " node" + "  " + stateInfo +  " " + block.hasBeenAccessed() + "\n");
                    }
                    String blockStartLine = "";
                    String blockEndLine = "";

                    for (AbstractNode node : block.getNodes()) {

                        // gather some state info
                        instCount++;
                        if (!currentBlockHasState && node.getSourceLocation().getLineNumber() >= 0) {
                            fnBlocks.append("\t\t" + instCount + ") node#" + node.getIndex() + " " + node
                                    + " " + node.getSourceLocation().getLineNumber()
                                    + ":" + node.getSourceLocation().getColumnNumber() + "\n");
                        } else {
                            if (blockStartLine.isEmpty()){
                                blockStartLine = node.getSourceLocation().toShortString();
                            }
                            blockEndLine = node.getSourceLocation().toShortString();
                        }
                        sourceTracker.add(node);

                        if (writer != null) {
                            writer.println(node.toString() + " " + node.getSourceLocation());
                        }
                    }
                    if (!blockStartLine.isEmpty()) {
                        fnBlocks.deleteCharAt(fnBlocks.length()-1);
                        fnBlocks.append(" ");
                        fnBlocks.append(blockStartLine);

                        if (!blockStartLine.equals(blockEndLine)) {

                            fnBlocks.append("->");
                            fnBlocks.append(blockEndLine);
                        }
                        fnBlocks.append("\n");
                    }

                }
                if (!functionHasOneState) {
                    fnTitle.append(" !!!! NO STATE FOR FUNCTIONS, FUNCTION NOT ANALYZED !!!\n");
                    System.out.print(fnTitle);
                    System.out.print(fnBlocks);
                } else {
                    //fnTitle.append(" {...Analyzed...}\n");
                    System.out.println(fnTitle);
                    System.out.print(fnBlocks);
                }
            }
        } catch (IOException ioe) {
            ioe.printStackTrace();
        } catch (URISyntaxException e) {
            e.printStackTrace();
        } finally {
            if (writer != null) {
                writer.close();
            }
        }
        sourceTracker.analyzeLinesParsed();
        System.out.println("*********************************************************************************************");
    }
*/

    /**
     * Scans for messages. Takes one round through all nodes and all contexts without invoking <code>propagate</code>.
     * {@link #solve()} must be called first.
     */
    public void scan() {
        if (the_analysis_lattice_element == null)
            throw new IllegalStateException("scan() called before solve()");

        System.out.println("*********************************************************************************************");
        System.out.println(flowgraph.toStringFG(false));
        System.out.println("*********************************************************************************************");

        Map<SourceLocation, Value> allFoundSLs = new HashMap<>();
        int scancnt = 0;
        URI sourcename = null;
        StringBuffer logbuf = new StringBuffer();
        int instCount = 0, threshCnt = 0, printCnt = 0;
        //File fileLogScan = new File("tajs-scan.addFiles");
        //Path pathLogScan = Paths.get(fileLogScan.toURI());
        /*try {
            Thread.sleep(1000);
        } catch (InterruptedException ie){
            ie.printStackTrace();
        }*/
        //clearTheFile(fileLogScan);

        //logTimeStamp(logbuf, pathLogScan, true);
        // visit each block
        for (Function function : flowgraph.getFunctions()) {
            if (log.isDebugEnabled())
                log.debug("Scanning " + function + " at " + function.getSourceLocation());

            analysis.getMonitoring().visitFunction(function, the_analysis_lattice_element.getStates(function.getEntry()).values());
            StringBuilder skippedBlocks = new StringBuilder();



            for (BasicBlock block : function.getBlocks()) {
                boolean state_found = false;

                if (log.isDebugEnabled())
                    log.debug("Scanning " + block + " at " + block.getSourceLocation());
                block_loop:
                for (Entry<ContextType, StateType> me : the_analysis_lattice_element.getStates(block).entrySet()) {
                    if (!state_found) {
                        if (skippedBlocks.length() > 0) {
                            //addFiles.warn("Blocks with no state skipped: " + skippedBlocks);
                            skippedBlocks = new StringBuilder();
                        }
                        //addFiles.warn("Block " + block.getIndex());
                        state_found = true;
                    }
                    current_state = me.getValue().clone();
                    analysis.getMonitoring().visitBlockTransferPre(block, current_state);
                    try {

                        ContextType context = me.getKey();
                        if (global_entry_block == block)
                            current_state.localize(null); // use *localized* initial state
                        if (log.isDebugEnabled()) {
                            log.debug("Context: " + context);
                            if (Options.get().isIntermediateStatesEnabled())
                                log.debug("Before block transfer: " + current_state);
                        }
                        for (AbstractNode node : block.getNodes()) {
                            current_node = node;
                           /* if (node.getIndex() == 64){
                                System.out.println("!!!!!!!!!!!!!!!!!!!!!!!!!!!!FOUND IT!!!!!!");
                            }*/
                            //addFiles.warn("\t" + block.getIndex() + ":" + node.getIndex() + ") " + node + " " + node.getSourceLocation());
                            String srcPath = node.getSourceLocation().toUserFriendlyString(false);
                            String srcFN = (new File(srcPath)).getName();

                            instCount++;

                            if (instCount % 1000 == 0) {
                                printCnt = checkPrintCnt(instCount, printCnt);
                                //threshCnt = checkThreshCnt(logbuf, instCount, threshCnt, pathLogScan, node, srcFN);
                            } else {
                                if (instCount == 1) {
                                    System.out.print(String.format("%3d", 0));
                                    logbuf.append(instCount + ")" + node.getIndex() + " " + node + ":" + srcFN + ":" + node.getSourceLocation().getLineNumber() + ":" + node.getSourceLocation().getColumnNumber() + "\n");
                                } else {
                                    //logbuf.append(instCount +  ")" + node.getIndex() + " " + node + ":" + srcFN + ":" + node.getSourceLocation().getLineNumber() + ":" + node.getSourceLocation().getColumnNumber() +"\n");
                                }
                            }

                            if (log.isDebugEnabled())
                                log.debug("node " + current_node.getIndex() + ": " + current_node);
                            if (current_state.isNone())
                                continue block_loop; // unreachable, so skip the rest of the block
                            analysis.getMonitoring().visitNodeTransferPre(current_node, current_state);

                            try {

                                analysis.getNodeTransferFunctions().transfer(node);
                                scancnt++;
                            } catch (AnalysisLimitationException e) {
                                if (Options.get().isTestEnabled() && !Options.get().isAnalysisLimitationWarnOnly()) {
                                    throw e;
                                }
                                e.printStackTrace();
                            } finally {
                                /*if (instCount > 130 && instCount < 151) {
                                    System.out.println(" vvvvvvvvvvvvvvvvvv" + instCount + " [" + current_node.getIndex() + "] " + current_node + " " + context + "vvvvvvvvvvvvvvvvvvvvvvv");
                                    condPrintState(instCount, node);
                                    System.out.println(" ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^");
                                } else if (current_node.toString().contains("appendChild")) {
                                    System.out.println(" vvvvvvvvvvvvvvvvvv" + instCount + " " + " [" + current_node.getIndex() + "] " + current_node + " " + context + "vvvvvvvvvvvvvvvvvvvvvvv");
                                    State cs = (State) current_state;
                                    //Object label put into store at 119
                                    System.out.println("!!!!!!! " + cs.getStore().entrySet());
                                    for (Map.Entry<ObjectLabel, Obj> ent : cs.getStore().entrySet()) {
                                        System.out.println("\t" + ent.getKey().hashCode() + " " + ent.getKey().toString().contains("HTMLDivElement"));
                                        if (ent.getKey().toString().contains("HTMLDivElement")) {
                                            System.out.println("\t\tProperties=" + ent.getValue().getProperties());
                                            Value ihval = ent.getValue().getProperties().get("innerHTML");
                                            if (ihval != null) {
                                                System.out.println("\t\t\t" + ihval.valueHistory);
                                            }
                                        }
                                    }

                                    condPrintState(instCount, node);
                                    System.out.println(" ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^");
                                } else {
                                    System.out.println(" vvvvvvvvvvvvvvvvvv" + instCount + " " + " [" + current_node.getIndex() + "] " + current_node + " " + context + "vvvvvvvvvvvvvvvvvvvvvvv");
                                    System.out.println(" ^^^^^^^^^^^^^^^^^^" + instCount + " " + current_node + "^^^^^^^^^^^^^^^^^^^^^^");
                                    condPrintState(instCount, node);
                                }*/

                                analysis.getMonitoring().visitNodeTransferPost(current_node, current_state);
                            }
                            if (current_node.toString().contains("innerHTML")) {
                                //System.out.println("\n***********************************************");
                                //System.out.println("" + node.getIndex() + " " + node);
                                State cs = (State) current_state;
                                for (Map.Entry<ObjectLabel, Obj> ent : cs.getStore().entrySet()) {
                                    //System.out.println("\t" + ent.getKey().toString() + ent.getKey().hashCode());
                                    if (ent.getKey().toString().contains("HTMLDivElement")) {
                                        Value ihval = ent.getValue().getProperties().get("innerHTML");
                                        //System.out.println("\t\t" + ihval);
                                        if (ihval != null) {
                                            //  System.out.println("\t" + current_node);
                                            // System.out.println("\t\t" + ihval.valueHistory);
                                        }
                                    }
                                }
                                //System.out.println("***********************************************\n");
                            }
                        }
                    } finally {
                        analysis.getMonitoring().visitBlockTransferPost(block, current_state);
                        State cs = (State) current_state;

                        cs.getSourceLocs().forEach(allFoundSLs::putIfAbsent);
                    }
                }
                if (sourcename == null && allFoundSLs.size() > 0) {
                    try {
                        SourceLocation mainSL = function.getSourceLocation();
                        if (mainSL.isDynamic()) {
                            sourcename = mainSL.getStaticSourceLocation().getLocation().toURI();
                        } else {
                            sourcename = mainSL.getLocation().toURI();
                        }
                    } catch (Exception e) {
                        e.printStackTrace();
                    }
                }
                if (state_found) {
                    StringBuilder sb = new StringBuilder();
                    for (BasicBlock succ : block.getSuccessors()) {
                        sb.append(block.getIndex() + " ");
                    }
                    if (block.getSuccessors().size() > 1) {
                        //addFiles.warn("\t\tSuccessors: " + sb);
                    } else {
                        //addFiles.warn("\t\tSuccessor: " + sb);
                    }
                } else {
                    skippedBlocks.append(block.getIndex() + " ");
                }
            }
            if (skippedBlocks.length() > 0) {
                //addFiles.warn("Blocks with no state skipped: " + skippedBlocks);
            }
        }

        System.out.println("SCANCNT " + scancnt);

        String output = "";

        Map<String, List<SourceLocation>> all = new HashMap<>();
        //Map<String, SourceLocation> all = new HashMap<>();

        for (Map.Entry<SourceLocation, Value> ent : allFoundSLs.entrySet()) {
            SourceLocation sl = ent.getKey();
            Value v = ent.getValue();
            String key = v.getStr();
            String prefix = v.getTypePrefixTrack();
            key = prefix +key;
            if (all.containsKey(key)) {
                all.get(key).add(sl);
            } else {
                List<SourceLocation> newlist = new ArrayList<>();
                newlist.add(sl);
                all.put(key, newlist);
            }
            output += "";

            output += sl.getLineNumber() + ":" + sl.getColumnNumber() + " to "
                    + sl.getEndLineNumber() + ":" + sl.getEndColumnNumber() + "";
        }

        System.out.println(output);
//        if (allFoundSLs.isEmpty()) {
//            output += sourcename + " Literals NOT found or NOT used ";
//        } else {
//            //System.out.println("here" + allFoundSLs.size());
//
//        }
        TotalsLog.report(all);

        //logTimeStamp(logbuf, pathLogScan, false);

    }

    /**
     * Returns the analysis lattice element.
     * {@link #solve()} must be called first.
     */
    public IAnalysisLatticeElement<StateType, ContextType, CallEdgeType> getAnalysisLatticeElement() {
        if (the_analysis_lattice_element == null)
            throw new IllegalStateException("getAnalysisLatticeElement() called before solve()");
        return the_analysis_lattice_element;
    }

    /**
     * Returns the flow graph.
     */
    public FlowGraph getFlowGraph() {
        return flowgraph;
    }
}
