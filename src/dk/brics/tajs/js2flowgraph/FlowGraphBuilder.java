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

package dk.brics.tajs.js2flowgraph;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.Lists;
import com.google.javascript.jscomp.parsing.parser.IdentifierToken;
import com.google.javascript.jscomp.parsing.parser.Parser.Config.Mode;
import com.google.javascript.jscomp.parsing.parser.trees.FormalParameterListTree;
import com.google.javascript.jscomp.parsing.parser.trees.FunctionDeclarationTree.Kind;
import com.google.javascript.jscomp.parsing.parser.trees.IdentifierExpressionTree;
import com.google.javascript.jscomp.parsing.parser.trees.ProgramTree;
import dk.brics.tajs.flowgraph.AbstractNode;
import dk.brics.tajs.flowgraph.BasicBlock;
import dk.brics.tajs.flowgraph.FlowGraph;
import dk.brics.tajs.flowgraph.Function;
import dk.brics.tajs.flowgraph.HostEnvSources;
import dk.brics.tajs.flowgraph.JavaScriptSource;
import dk.brics.tajs.flowgraph.SourceLocation;
import dk.brics.tajs.flowgraph.SourceLocation.SourceLocationMaker;
import dk.brics.tajs.flowgraph.SourceLocation.SyntheticLocationMaker;
import dk.brics.tajs.flowgraph.TAJSFunctionName;
import dk.brics.tajs.flowgraph.ValueLogLocationInformation;
import dk.brics.tajs.flowgraph.jsnodes.BeginForInNode;
import dk.brics.tajs.flowgraph.jsnodes.BeginLoopNode;
import dk.brics.tajs.flowgraph.jsnodes.CallNode;
import dk.brics.tajs.flowgraph.jsnodes.CatchNode;
import dk.brics.tajs.flowgraph.jsnodes.ConstantNode;
import dk.brics.tajs.flowgraph.jsnodes.DeclareFunctionNode;
import dk.brics.tajs.flowgraph.jsnodes.DeclareVariableNode;
import dk.brics.tajs.flowgraph.jsnodes.EndForInNode;
import dk.brics.tajs.flowgraph.jsnodes.EndLoopNode;
import dk.brics.tajs.flowgraph.jsnodes.EventDispatcherNode;
import dk.brics.tajs.flowgraph.jsnodes.EventDispatcherNode.Type;
import dk.brics.tajs.flowgraph.jsnodes.IfNode;
import dk.brics.tajs.flowgraph.jsnodes.Node;
import dk.brics.tajs.flowgraph.jsnodes.NopNode;
import dk.brics.tajs.flowgraph.jsnodes.ReadPropertyNode;
import dk.brics.tajs.flowgraph.jsnodes.ReadVariableNode;
import dk.brics.tajs.flowgraph.jsnodes.ThrowNode;
import dk.brics.tajs.flowgraph.jsnodes.WritePropertyNode;
import dk.brics.tajs.flowgraph.jsnodes.WriteVariableNode;
import dk.brics.tajs.flowgraph.syntaticinfo.RawSyntacticInformation;
import dk.brics.tajs.js2flowgraph.JavaScriptParser.ParseResult;
import dk.brics.tajs.js2flowgraph.JavaScriptParser.SyntaxMesssage;
import dk.brics.tajs.options.Options;
import dk.brics.tajs.util.AnalysisException;
import dk.brics.tajs.util.Collections;
import dk.brics.tajs.util.Collectors;
import dk.brics.tajs.util.Pair;
import dk.brics.tajs.util.ParseError;
import org.apache.log4j.Logger;

import java.net.URL;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Comparator;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;
import java.util.Stack;

import static dk.brics.tajs.js2flowgraph.FunctionBuilderHelper.addNodeToBlock;
import static dk.brics.tajs.js2flowgraph.FunctionBuilderHelper.makeBasicBlock;
import static dk.brics.tajs.js2flowgraph.FunctionBuilderHelper.makeCatchBasicBlock;
import static dk.brics.tajs.js2flowgraph.FunctionBuilderHelper.makeSourceLocation;
import static dk.brics.tajs.js2flowgraph.FunctionBuilderHelper.makeSuccessorBasicBlock;
import static dk.brics.tajs.js2flowgraph.FunctionBuilderHelper.setupFunction;
import static dk.brics.tajs.util.Collections.newList;
import static dk.brics.tajs.util.Collections.newSet;
import static org.apache.log4j.Logger.getLogger;

/**
 * Converter from JavaScript source code to flow graphs.
 * The order the sources are provided is significant.
 */
@SuppressWarnings("FieldCanBeLocal")
public class FlowGraphBuilder {

    private static final Logger log = getLogger(FlowGraphBuilder.class);

    private static final boolean showParserWarnings = false;

    private final Mode mode = Mode.ES5; // TODO: (#3) currently ES5 mode

    private final boolean strict = false;

    private final JavaScriptParser parser;

    private final FunctionAndBlockManager functionAndBlocksManager;

    private final AstEnv initialEnv;

    private boolean closed = false;

    private TranslationResult processed;

    private ASTInfo astInfo;

    private final RawSyntacticInformation syntacticInformation;

    private final ValueLogLocationInformation valueLogMappingInformation;

    /**
     * Constructs a flow graph builder.
     *
     * @param env traversal environment
     * @param fab function/block manager
     */
    public FlowGraphBuilder(AstEnv env, FunctionAndBlockManager fab) {
        assert env != null;
        assert fab != null;
        functionAndBlocksManager = fab;
        astInfo = new ASTInfo();
        initialEnv = env;
        parser = new JavaScriptParser(mode, strict);
        processed = TranslationResult.makeAppendBlock(initialEnv.getAppendBlock());
        syntacticInformation = new RawSyntacticInformation();
        valueLogMappingInformation = new ValueLogLocationInformation();
    }

    /**
     * Transforms the given stand-alone JavaScript source code and appends it to the main function.
     */
    public Function transformStandAloneCode(String source, SourceLocationMaker sourceLocationMaker) {
        return transformCode(source, 0, 0, sourceLocationMaker);
    }

    /**
     * Transforms the given JavaScript source code and appends it to the main function, with location offsets.
     * The location offsets are used for setting the source locations in the flow graph.
     *
     * @param lineOffset   number of lines preceding the code
     * @param columnOffset number of columns preceding the first line of the code
     */
    Function transformCode(String source, int lineOffset, int columnOffset, SourceLocationMaker sourceLocationMaker) {
        final AstEnv env = initialEnv.makeAppendBlock(processed.getAppendBlock());
        ProgramTree t = makeAST(source, lineOffset, columnOffset, sourceLocationMaker);
        processed = new FunctionBuilder(astInfo, functionAndBlocksManager, sourceLocationMaker, makeSyntacticAnalysis()).process(t, env);
        return processed.getAppendBlock().getFunction();
    }

    /**
     * Parses the given JavaScript code.
     */
    private ProgramTree makeAST(String sourceContent, int lineOffset, int columnOffset, SourceLocationMaker sourceLocationMaker) {
        if (closed) {
            throw new RuntimeException("Already closed.");
        }

        // add line/column offsets (a bit hacky - but it avoids other silly encodings or extra fields)
        StringBuilder s = new StringBuilder();
        for (int i = 0; i < lineOffset; i++) {
            s.append("\n");
        }
        for (int i = 0; i < columnOffset; i++) {
            s.append(" ");
        }
        s.append(sourceContent);

        ParseResult parseResult = parser.parse(s.toString(), sourceLocationMaker);
        reportParseMessages(parseResult);
        astInfo.updateWith(parseResult.getProgramAST());
        return parseResult.getProgramAST();
    }

    /**
     * Reports parse errors and warnings to the addFiles.
     *
     * @throws ParseError if the parse result contains a parse error
     */
    private static void reportParseMessages(ParseResult parseResult) {
        if (!parseResult.getErrors().isEmpty()) {
            StringBuilder sb = new StringBuilder();
            for (SyntaxMesssage error : parseResult.getErrors()) {
                sb.append(String.format("%n%s: Syntax error: %s", error.getSourceLocation().toString(), error.getMessage()));
            }
            throw new ParseError(sb.toString());
        }
        if (showParserWarnings) {
            for (SyntaxMesssage warning : parseResult.getWarnings()) {
                log.warn(String.format("%s: Parser warning: %s", warning.getSourceLocation().toString(), warning.getMessage()));
            }
        }
    }

    /**
     * Transforms the given web application JavaScript source code.
     */
    public Function transformWebAppCode(JavaScriptSource s, SourceLocationMaker sourceLocationMaker) {
        switch (s.getKind()) {

            case FILE: { // TODO: (#119) processing order of external JavaScript files (sync/async loading...)
                // TODO: (#119) should be added as a load event, but that does not work currently...
                // Function function = processFunctionBody(Collections.<String>newList(), s.getFileName(), s.getJavaScript(), 0, initialEnv);
                // eventHandlers.add(Pair.make(function, EventHandlerKind.DOM_LOAD));
                return transformStandAloneCode(s.getCode(), sourceLocationMaker);
            }

            case EMBEDDED: { // TODO: (#119) currently ignoring events during page load (unsound)
                return transformCode(s.getCode(), s.getLineOffset(), s.getColumnOffset(), sourceLocationMaker);
            }

            case EVENTHANDLER: {
                Function function = transformFunctionBody(s.getCode(), s.getLineOffset(), s.getColumnOffset(), initialEnv, sourceLocationMaker);
                function.getNode().setDomEventType(s.getEventKind());
                return function;
            }
            default:
                throw new AnalysisException("Unhandled case: " + s.getKind());
        }
    }

    /**
     * Transforms the given code as a function body.
     *
     * @return the new function
     */
    private Function transformFunctionBody(String sourceContent, int lineOffset, int columnOffset, AstEnv env, SourceLocationMaker sourceLocationMaker) {
        ProgramTree tree = makeAST(sourceContent, lineOffset, columnOffset, sourceLocationMaker);
        FormalParameterListTree params = new FormalParameterListTree(tree.location, ImmutableList.of());
        return new FunctionBuilder(astInfo, functionAndBlocksManager, sourceLocationMaker, makeSyntacticAnalysis()).processFunctionDeclaration(Kind.DECLARATION, null, params, tree, env, makeSourceLocation(tree, sourceLocationMaker), null);
    }

    /**
     * Completes the flow graph construction.
     * This will:
     * <ul>
     * <li>Add the event dispatcher loop, if DOM mode enabled.
     * <li>Set the block order on each basic block (used by the analysis worklist).
     * <li>Set the index on each basic block and node.
     * <li>Return the resulting flow graph.
     * </ul>
     */
    public FlowGraph close() {
        FlowGraph flowGraph = close(null, initialEnv.getFunction().getOrdinaryExit());
        if (Options.get().isTestFlowGraphBuilderEnabled())
            log.info("fg2: " + flowGraph);
        flowGraph.check();
        return flowGraph;
    }

    /**
     * Add forced callers adds all the Calls to the end MAIN
     * @param env
     * @param anonFuncLabels
     * @return
     */
    private TranslationResult addForcedCallers( AstEnv env, List<String> anonFuncLabels) {
        SourceLocation dummySource = new SyntheticLocationMaker("call-all-functions-sources-loader (CALL SETUP)").makeUnspecifiedPosition();
        SourceLocation dummyDeclSource = new SyntheticLocationMaker("call-all-functions-sources-loader (DECLARATION)").makeUnspecifiedPosition();
        BasicBlock appendBlock = env.getAppendBlock();
        BasicBlock mainEntryBlock = null;
        appendBlock = makeSuccessorBasicBlock(appendBlock, functionAndBlocksManager);
        int constReg = env.getRegisterManager().nextRegister();
        ConstantNode cn = ConstantNode.makeString("true", constReg, dummySource);
        addNodeToBlock(cn, appendBlock, env.makeStatementLevel(false));
        IfNode ifn = new IfNode(constReg, dummySource);
        BeginLoopNode bln = new BeginLoopNode(ifn, false, dummySource);
        addNodeToBlock(bln, appendBlock, env.makeStatementLevel(false));
        System.out.println(appendBlock);

        appendBlock = makeSuccessorBasicBlock(appendBlock, functionAndBlocksManager);
        addNodeToBlock(ifn, appendBlock, env.makeStatementLevel(false));

        appendBlock = makeSuccessorBasicBlock(appendBlock, functionAndBlocksManager);
        BasicBlock trueBlock = appendBlock;
        int mathReg = env.getRegisterManager().nextRegister();
        int randFuncReg = env.getRegisterManager().nextRegister();
        ReadVariableNode rvn = new ReadVariableNode("Math", mathReg, AbstractNode.NO_VALUE, dummySource);
        addNodeToBlock(rvn, appendBlock, env.makeStatementLevel(false));
        ReadPropertyNode rpn = new ReadPropertyNode(mathReg, "random",  randFuncReg, dummySource);
        addNodeToBlock(rpn, appendBlock, env.makeStatementLevel(false));

        appendBlock = makeSuccessorBasicBlock(appendBlock, functionAndBlocksManager);
        int randResult = env.getRegisterManager().nextRegister();
        //CallNode(boolean constructor, int result_reg, int base_reg, int property_reg, String property_str, List<Integer> arg_regs, SourceLocation location) {
        CallNode randCall = new CallNode(false, randResult, mathReg, randFuncReg, "random", newList(), dummySource);
        addNodeToBlock(randCall, appendBlock, env.makeStatementLevel(false));

        appendBlock = makeSuccessorBasicBlock(appendBlock, functionAndBlocksManager);
        for (Function f : functionAndBlocksManager.getFunctions()) {
            if(f.isMain()){
                mainEntryBlock = f.getEntry();
            }
        }

//        for (Function f : functionAndBlocksManager.getFunctions()) {
//            if (!f.isMain() && f.getName() != null) {
//                appendBlock = createForcedCallBlocks(dummySource, env, appendBlock, f.getName(), randResult);
//            } else if(f.isMain()){
//                mainEntryBlock = f.getEntry();
//            }
//        }
        for (String varname : anonFuncLabels){
            if (mainEntryBlock != null){
                DeclareVariableNode dvn = new DeclareVariableNode(varname, dummyDeclSource );
                mainEntryBlock.addNode(dvn);
                appendBlock = createForcedCallBlocks( env, appendBlock, varname, randFuncReg);
            }
        }
        appendBlock = makeSuccessorBasicBlock(appendBlock, functionAndBlocksManager);
        EndLoopNode eln = new EndLoopNode(bln, dummySource);
        addNodeToBlock(eln, appendBlock, env.makeStatementLevel(false));

        appendBlock = makeSuccessorBasicBlock(appendBlock, functionAndBlocksManager);
        addNodeToBlock(new NopNode(dummySource), appendBlock, env.makeStatementLevel(false));
        BasicBlock falseBlock = appendBlock;
        ifn.setSuccessors(trueBlock, falseBlock);

//        for (String varname : Lists.reverse(anonFuncLabels)){
//            if (mainEntryBlock != null){
//                appendBlock = createForcedCallBlocks(dummySource, env, appendBlock, varname);
//            }
//        }
//        for (Function f : functionAndBlocksManager.getFunctions()) {
//            if (!f.isMain() && f.getName() != null) {
//                appendBlock = createForcedCallBlocks(dummySource, env, appendBlock, f.getName());
//            } else if(f.isMain()){
//                mainEntryBlock = f.getEntry();
//            }
//        }

        return TranslationResult.makeAppendBlock(appendBlock);
    }


    private BasicBlock createForcedCallBlocks(AstEnv env, BasicBlock appendBlock, String fnName, int randReg) {
        /*
        If
         */
        SourceLocation dummySetupSource = new SyntheticLocationMaker("call-all-functions-sources-loader (FORCED SETUP)").makeUnspecifiedPosition();
        SourceLocation dummyForcedReadSource = new SyntheticLocationMaker("call-all-functions-sources-loader (FORCED READ)").makeUnspecifiedPosition();
        SourceLocation dummyForcedParmReadSource = new SyntheticLocationMaker("call-all-functions-sources-loader (FORCED PARAM READ)").makeUnspecifiedPosition();
        SourceLocation dummyForcedCallSource = new SyntheticLocationMaker("call-all-functions-sources-loader (FORCED CALL )").makeUnspecifiedPosition();
        SourceLocation dummyForcedCatch = new SyntheticLocationMaker("call-all-functions-sources-loader (FORCED CATCH )").makeUnspecifiedPosition();
        int functionRegister = env.getRegisterManager().nextRegister();
        int baseRegister = getGlobalBaseReg(); //env.getRegisterManager().nextRegister();
        baseRegister = AbstractNode.NO_VALUE;
        int parmRegister = env.getRegisterManager().nextRegister();



        appendBlock = makeSuccessorBasicBlock(appendBlock, functionAndBlocksManager);


        IfNode ifn = new IfNode(randReg, dummySetupSource);
        addNodeToBlock(ifn, appendBlock, env.makeStatementLevel(false));
        BasicBlock ifBlock = appendBlock;

        appendBlock = makeSuccessorBasicBlock(appendBlock, functionAndBlocksManager);
        BasicBlock trueBlock = appendBlock;
        ReadVariableNode rvn = new ReadVariableNode(fnName, functionRegister, baseRegister, dummyForcedReadSource);

        addNodeToBlock(rvn, appendBlock, env.makeStatementLevel(false));
        ConstantNode cn = ConstantNode.makeString("myparm", parmRegister, dummyForcedParmReadSource);
        addNodeToBlock(cn, appendBlock, env.makeStatementLevel(false));
        appendBlock = makeSuccessorBasicBlock(appendBlock, functionAndBlocksManager);
        BasicBlock callBlock = appendBlock;
        CallNode callLoadedNode = new CallNode(false, parmRegister, baseRegister,
                functionRegister, newList(), dummyForcedCallSource);

        addNodeToBlock(new NopNode(dummySetupSource), appendBlock, env.makeStatementLevel(false));

        addNodeToBlock(callLoadedNode, appendBlock, env.makeStatementLevel(false));

        int errRegister = env.getRegisterManager().nextRegister();
        appendBlock = makeSuccessorBasicBlock(appendBlock, functionAndBlocksManager);
        // setting CallBlock above to this block for its exceptions, to catch problems in function so that forced
        // executions will continue despite error in function
        callBlock.setExceptionHandler(appendBlock);
        CatchNode catchNode = new CatchNode("err",errRegister,dummyForcedCatch);
        addNodeToBlock(catchNode, appendBlock, env.makeStatementLevel(false));
        //BeginWithNode beginWith = new CatchNode("err",errRegister,dummyForcedCatch);

        appendBlock = makeSuccessorBasicBlock(appendBlock, functionAndBlocksManager);
        BasicBlock falseBlock = appendBlock;
        addNodeToBlock(new NopNode(dummySetupSource), appendBlock, env.makeStatementLevel(false));

        ifn.setSuccessors(trueBlock, falseBlock);

        //System.out.println("added CALL for " + fnName + " " +  rvn + "-->" + callLoadedNode);

        return appendBlock;
    }



    private BasicBlock getStartOfMain(){
        int bbIndex = 0;
        Iterator<BasicBlock> bbIterator = functionAndBlocksManager.getBasicBlocks().iterator();
        boolean firstChange = false;
        while (bbIterator.hasNext()) {
            BasicBlock bb = bbIterator.next();
            boolean isHostSource = !bb.getNodes().isEmpty() && bb.getFirstNode().getSourceLocation() != null
                    && bb.getFirstNode().getSourceLocation().isHostEnviornment();

            // if not first change, then should be start of TAJS BB's
            if (!firstChange && isHostSource){
                firstChange = true;
            } else if(firstChange && !isHostSource){
                // once we have first change and go back to user BB's return the index as the start point.
                return bb;
            }

            bbIndex++;
        }
        throw new AnalysisException("couldn't find main after TAJS functions");
    }

    private BasicBlock getDefaultNadaNode() {
        int bbIndex = 0;
        Iterator<BasicBlock> bbIterator = functionAndBlocksManager.getBasicBlocks().iterator();
        boolean firstChange = false;
        while (bbIterator.hasNext()) {
            BasicBlock bb = bbIterator.next();
            if (bb.getFunction().getName().contains("__default_nd2()")){

            }
            boolean isHostSource = !bb.getNodes().isEmpty() && bb.getFirstNode().getSourceLocation() != null
                    && bb.getFirstNode().getSourceLocation().isHostEnviornment();

            // if not first change, then should be start of TAJS BB's
            if (!firstChange && isHostSource) {
                firstChange = true;
            } else if (firstChange && !isHostSource) {
                // once we have first change and go back to user BB's return the index as the start point.
                return bb;
            }

            bbIndex++;
        }
        throw new AnalysisException("couldn't find main after TAJS functions");
    }
    /**
     * This function iterates through all the BasicBlocks and their nodes
     * looking for Function declarations, the goal is to grab that function pointer
     * and set it to a global for calling as the final step of MAIN to make sure
     * every function gets analyzed at least once
     * 1) Read Declaration's result
     * 2) Point to previously declared function
     * @param loaderDummySourceLocation
     * @param mainEnv
     * @return
     */
    private List<String> createFuncPtrs222(SourceLocation loaderDummySourceLocation, AstEnv mainEnv) {
        loaderDummySourceLocation = new SyntheticLocationMaker("call-all-functions-sources-loader (FORCED CREATE)").makeUnspecifiedPosition();

        //for (BasicBlock bb : functionAndBlocksManager.getBasicBlocks())
        List<String> funcregs = new ArrayList<>();
        Iterator<BasicBlock> bbIterator = functionAndBlocksManager.getBasicBlocks().iterator();
        int anonFnIndex=1;
        int bbIndex =0;
        BasicBlock initializeFuncPtrsBlock = getStartOfMain();


        List<Node> firstNodes = new ArrayList<>();

        ReadVariableNode lastRVN= null;
        List<ReadPropertyNode>historyRPNs= new ArrayList<>();
        while (bbIterator.hasNext()){
            // find globalBaseReg
            int globalBaseReg = getGlobalBaseReg();
            BasicBlock bb = bbIterator.next();
            if (bbIndex == 1){
//                addNada2Do(bb);
                for (Node addnode : firstNodes){
                    bb.addNode(addnode);
                }
            }
            DeclareFunctionNode dfn = null;
            List<AbstractNode> newNodes = new ArrayList<AbstractNode>();

            AbstractNode nodeIterator[] = new AbstractNode[bb.getNodes().size()];
            nodeIterator = bb.getNodes().toArray(nodeIterator);

            if (!bb.getFunction().getSourceLocation().isHostEnviornment()) {
                System.out.println("BLOCK #" + bb.getIndex());
                boolean foundDFN = false;
                for (int i = 0; i < nodeIterator.length; i++) {
                    AbstractNode an = nodeIterator[i];
                    if (an.toString().contains("constant[\"hereme\"")){
                        String erikwazhere="";
                    }
                    newNodes.add(an);

                    System.out.println("\t"+an.toString() + "  Clear Registers:" + an.isRegistersDone());
                    if (i < nodeIterator.length-1){
                        System.out.println("\t\t" + ((AbstractNode) nodeIterator[i+1]).toString());
                    }

                    if (an instanceof ReadVariableNode) {
                        lastRVN = (ReadVariableNode) an;
                    } else if (an instanceof ReadPropertyNode) {
                        historyRPNs.add((ReadPropertyNode) an);
                    }
                    if (an instanceof DeclareFunctionNode) {
                        foundDFN = true;
                        dfn = (DeclareFunctionNode) an;
                        String fnName = dfn.getFunction().getName();

                        //dfn.getFunction().getSourceLocation().getLineNumber();

                        // This handles anonymous functions
                        if (fnName == null && dfn.getResultRegister() > 0) {
                            fnName = "anonfun" + anonFnIndex;
                            String varName = "__" + fnName + "__";
                            funcregs.add(varName);

                            WriteVariableNode wvn = new WriteVariableNode(dfn.getResultRegister(), varName, loaderDummySourceLocation);
                            //System.out.println("writing to dfn.getResultRegister()" + wvn);
                            //System.out.println("\t " + dfn);
                            wvn.setBlock(dfn.getBlock());
                            newNodes.add(wvn);

                            ReadVariableNode rvn = new ReadVariableNode(varName, dfn.getResultRegister(), AbstractNode.NO_VALUE, loaderDummySourceLocation);
                            rvn.setBlock(dfn.getBlock());
                            newNodes.add(rvn);

                        } else if (fnName != null) {
                            //regular functions
                            String varName = "__" + fnName + "__";
                            int newFnRegister = mainEnv.getRegisterManager().nextRegister();
                            ReadVariableNode rvn = new ReadVariableNode(fnName, newFnRegister, AbstractNode.NO_VALUE, loaderDummySourceLocation);
                            newNodes.add(rvn);
                            rvn.setBlock(dfn.getBlock());

                            WriteVariableNode wvn = new WriteVariableNode(newFnRegister, varName, loaderDummySourceLocation);
                            wvn.setBlock(dfn.getBlock());
                            newNodes.add(wvn);

//                            if (bbIndex == 0){
//                                firstNodes.add(rvn);
//                                firstNodes.add(wvn);
//                            } else {
//                                bb.addNode(rvn);
//                                bb.addNode(wvn);
//                            }
                            funcregs.add(varName);
                        }

                        anonFnIndex++;


                    }
                }
                if (foundDFN){
                    boolean wasThereAClearRegs = bb.getLastNode().isRegistersDone();
                    for (AbstractNode an : newNodes) {
                        an.setRegistersDone(false);
                    }

                    bb.setNodes(newNodes);
                    bb.getLastNode().setRegistersDone(wasThereAClearRegs);
                    System.out.println("----- New Block ----");
                    for (AbstractNode an : bb.getNodes()) {
                        System.out.println("\t"+an.toString() + "  Clear Registers:" + an.isRegistersDone());
                    }
                    System.out.println("----- ---- ----");
                    String erikwazhere="";
                }


            }
//            AbstractNode nodeIterator[] = new AbstractNode[bb.getNodes().size()];
//            nodeIterator = bb.getNodes().toArray(nodeIterator);
//            if (!bb.getFunction().getSourceLocation().isHostEnviornment()) {
//
//                for (int i = 0; i < nodeIterator.length; i++) {
//                    AbstractNode an = nodeIterator[i];
//                    System.out.println("\n" + an.toString() );
//                    if (i < nodeIterator.length-1){
//                        System.out.println("\t\t" + ((AbstractNode) nodeIterator[i+1]).toString());
//                    }
//
//                    if (an instanceof ReadVariableNode) {
//                        lastRVN = (ReadVariableNode) an;
//                    } else if (an instanceof ReadPropertyNode) {
//                        historyRPNs.add((ReadPropertyNode) an);
//                    }
//                    if (an instanceof DeclareFunctionNode) {
//                        dfn = (DeclareFunctionNode) an;
//                        String fnName = dfn.getFunction().getName();
//
//                        //dfn.getFunction().getSourceLocation().getLineNumber();
//
//                        // This handles anonymous functions
//                        if (fnName == null && dfn.getResultRegister() > 0) {
//                            fnName = "anonfun" + anonFnIndex;
//                            String varName = "__" + fnName + "__";
//                            funcregs.add(varName);
//
//                            //goal is to keep the internal var from ever being interpreted as undefined.
////                            int placeholderFnReg = mainEnv.getRegisterManager().nextRegister();
////                            initializeFuncPtrsBlock.addNode(new ReadVariableNode("__default_nd2", placeholderFnReg, globalBaseReg, loaderDummySourceLocation));
////                            initializeFuncPtrsBlock.addNode(new WriteVariableNode(placeholderFnReg, varName, loaderDummySourceLocation));
//
//                            //System.out.println(fnName + " " + dfn.getSourceLocation());
//                            boolean usedUserGlobal = false;
//                            // if function declaration is followed by a Write Variable or Property
//                            // the value in the register is lost, so the nodes below read the written variable or p
//                            // property and then write it to the global
//                            if ((i + 1) < nodeIterator.length && (nodeIterator[i + 1] instanceof WriteVariableNode || nodeIterator[i + 1] instanceof WritePropertyNode)) {
//                                //System.out.println("Checking for var");
//                                if (varName.equals("__anonfun585__")){
//                                    String erikwazhere="";
//                                }
//                                int newFnRegister = mainEnv.getRegisterManager().nextRegister();
//
//                                if (nodeIterator[i + 1] instanceof WriteVariableNode) {
//                                    WriteVariableNode fnWVN = (WriteVariableNode) nodeIterator[i + 1];
//                                    if (fnWVN.getValueRegister() == dfn.getResultRegister()) {
//                                        // Read Var using variable name already defined
//                                        ReadVariableNode rvn = new ReadVariableNode(fnWVN.getVariableName(), newFnRegister, globalBaseReg, loaderDummySourceLocation);
//                                        bb.addNode(rvn);
//                                        usedUserGlobal = true;
//                                    }
//                                } else {
//                                    WritePropertyNode fnWPN = (WritePropertyNode) nodeIterator[i + 1];
//                                    boolean checkforBaseVar = lastRVN != null && fnWPN.getBaseRegister() == lastRVN.getResultRegister();
//                                    boolean checkforBaseProp = !historyRPNs.isEmpty() && fnWPN.getBaseRegister() == historyRPNs.get(historyRPNs.size()-1).getResultRegister();
//                                    if (fnWPN.getValueRegister() == dfn.getResultRegister() && (checkforBaseProp || checkforBaseVar)) {
//
//                                        if (checkforBaseVar) {
//                                            ReadVariableNode  rvn = new ReadVariableNode(lastRVN.getVariableName(), fnWPN.getBaseRegister(), globalBaseReg, loaderDummySourceLocation);
//                                            bb.addNode(rvn);
//                                        } else {
//                                            List<AbstractNode> nodesToAdd = new ArrayList<>();
//                                            int childBaseReg = fnWPN.getBaseRegister();
//                                            for (int j=(historyRPNs.size()-1);j >= 0; j--){
//                                                ReadPropertyNode evalRPN = historyRPNs.get(j);
//                                                if (childBaseReg == evalRPN.getResultRegister()) {
//                                                    ReadPropertyNode rpn;
//                                                    if (evalRPN.getPropertyRegister() == -1) {
//                                                        rpn = new ReadPropertyNode(evalRPN.getBaseRegister(), evalRPN.getPropertyString(), childBaseReg, loaderDummySourceLocation);
//                                                    } else {
//                                                        rpn = new ReadPropertyNode(evalRPN.getBaseRegister(), evalRPN.getPropertyRegister(), childBaseReg, loaderDummySourceLocation);
//                                                    }
//                                                    nodesToAdd.add(rpn);
//                                                    childBaseReg = evalRPN.getBaseRegister();
//                                                } else {
//                                                    break;
//                                                }
//                                            }
//                                            if (lastRVN == null){
//                                                throw new AnalysisException("Last variable found to read is null");
//                                            }
//                                            ReadVariableNode  rvn = new ReadVariableNode(lastRVN.getVariableName(), childBaseReg, globalBaseReg, loaderDummySourceLocation);
//                                            bb.addNode(rvn);
//                                            nodesToAdd = Lists.reverse(nodesToAdd);
//                                            for (AbstractNode antoadd : nodesToAdd){
//                                                bb.addNode(antoadd);
//                                            }
//
//
//                                        }
//
//                                        ReadPropertyNode rpn;
//                                        if (fnWPN.getPropertyString() == null) {
//                                            rpn = new ReadPropertyNode(fnWPN.getBaseRegister(), fnWPN.getPropertyRegister(), newFnRegister, loaderDummySourceLocation);
//                                        } else {
//                                            rpn = new ReadPropertyNode(fnWPN.getBaseRegister(), fnWPN.getPropertyString(), newFnRegister, loaderDummySourceLocation);
//                                        }
//                                        bb.addNode(rpn);
//                                        usedUserGlobal = true;
//                                    } else if (fnWPN.getValueRegister() == dfn.getResultRegister()) {
//                                        System.out.println("\n\nSkipping, NEED to track up source to get a currently existing register value\n\n");
//                                        anonFnIndex++;
//                                        continue;
//                                    }
//                                }
//                                if (usedUserGlobal) {
//                                    WriteVariableNode wvn = new WriteVariableNode(newFnRegister, varName, loaderDummySourceLocation);
//                                    bb.addNode(wvn);
//                                }
//                            }
//
//                            if (!usedUserGlobal) {
//                                //int globalBaseReg = getGlobalBaseReg();
//                                WriteVariableNode wvn = new WriteVariableNode(dfn.getResultRegister(), varName, loaderDummySourceLocation);
//                                //System.out.println("writing to dfn.getResultRegister()" + wvn);
//                                //System.out.println("\t " + dfn);
//
//                                bb.addNode(wvn);
//                                ReadVariableNode rvn = new ReadVariableNode(varName, dfn.getResultRegister(), globalBaseReg, loaderDummySourceLocation);
//                                bb.addNode(rvn);
//                            }
//                        } else if (fnName != null) {
//                            //regular functions
//                            String varName = "__" + fnName + "__";
//                            //int globalBaseReg = getGlobalBaseReg();
//                            int newFnRegister = mainEnv.getRegisterManager().nextRegister();
//                            ReadVariableNode rvn = new ReadVariableNode(fnName, newFnRegister, globalBaseReg, loaderDummySourceLocation);
//
//                            WriteVariableNode wvn = new WriteVariableNode(newFnRegister, varName, loaderDummySourceLocation);
//                            if (bbIndex == 0){
//                                firstNodes.add(rvn);
//                                firstNodes.add(wvn);
//                            } else {
//                                bb.addNode(rvn);
//                                bb.addNode(wvn);
//                            }
//                            funcregs.add(varName);
//                        }
//
//                        anonFnIndex++;
//
//
//                    }
//                }
//            }
            bbIndex++;
        }
        return funcregs;
    }
    /**
     * This function iterates through all the BasicBlocks and their nodes
     * looking for Function declarations, the goal is to grab that function pointer
     * and set it to a global for calling as the final step of MAIN to make sure
     * every function gets analyzed at least once
     * 1) Read Declaration's result
     * 2) Point to previously declared function
     * @param loaderDummySourceLocation
     * @param mainEnv
     * @return
     */
    private List<String> createFuncPtrs(SourceLocation loaderDummySourceLocation, AstEnv mainEnv) {
        //for (BasicBlock bb : functionAndBlocksManager.getBasicBlocks())
        List<String> funcregs = new ArrayList<>();
        Iterator<BasicBlock> bbIterator = functionAndBlocksManager.getBasicBlocks().iterator();
        int anonFnIndex=1;
        int bbIndex =0;
        BasicBlock initializeFuncPtrsBlock = getStartOfMain();

        // find globalBaseReg
        List<Node> firstNodes = new ArrayList<>();
        int globalBaseReg = getGlobalBaseReg();
        ReadVariableNode lastRVN= null;
        List<ReadPropertyNode>historyRPNs= new ArrayList<>();
        while (bbIterator.hasNext()){
            BasicBlock bb = bbIterator.next();
            if (bbIndex == 1){
//                addNada2Do(bb);
                for (Node addnode : firstNodes){
                    bb.addNode(addnode);
                }
            }
            DeclareFunctionNode dfn = null;
            AbstractNode nodeIterator[] = new AbstractNode[bb.getNodes().size()];
            nodeIterator = bb.getNodes().toArray(nodeIterator);
            if (!bb.getFunction().getSourceLocation().isHostEnviornment()) {

                for (int i = 0; i < nodeIterator.length; i++) {
                    AbstractNode an = nodeIterator[i];
                    if (an instanceof ReadVariableNode) {
                        lastRVN = (ReadVariableNode) an;
                    } else if (an instanceof ReadPropertyNode) {
                        historyRPNs.add((ReadPropertyNode) an);
                    }
                    if (an instanceof DeclareFunctionNode) {
                        dfn = (DeclareFunctionNode) an;
                        String fnName = dfn.getFunction().getName();

                        //dfn.getFunction().getSourceLocation().getLineNumber();

                        // This handles anonymous functions
                        if (fnName == null && dfn.getResultRegister() > 0) {
                            fnName = "anonfun" + anonFnIndex;
                            String varName = "__" + fnName + "__";
                            funcregs.add(varName);
                            if (varName.equals("__anonfun26__")){
                                String erikwazhere="";
                            }
                            //goal is to keep the internal var from ever being interpreted as undefined.
//                            int placeholderFnReg = mainEnv.getRegisterManager().nextRegister();
//                            initializeFuncPtrsBlock.addNode(new ReadVariableNode("__default_nd2", placeholderFnReg, globalBaseReg, loaderDummySourceLocation));
//                            initializeFuncPtrsBlock.addNode(new WriteVariableNode(placeholderFnReg, varName, loaderDummySourceLocation));

                            //System.out.println(fnName + " " + dfn.getSourceLocation());
                            boolean usedUserGlobal = false;
                            // if function declaration is followed by a Write Variable or Property
                            // the value in the register is lost, so the nodes below read the written variable or p
                            // property and then write it to the global
                            if ((i + 1) < nodeIterator.length && (nodeIterator[i + 1] instanceof WriteVariableNode || nodeIterator[i + 1] instanceof WritePropertyNode)) {
                                //System.out.println("Checking for var");
                                if (varName.equals("__anonfun26__")){
                                    String erikwazhere="";
                                }
                                int newFnRegister = mainEnv.getRegisterManager().nextRegister();

                                if (nodeIterator[i + 1] instanceof WriteVariableNode) {
                                    WriteVariableNode fnWVN = (WriteVariableNode) nodeIterator[i + 1];
                                    if (fnWVN.getValueRegister() == dfn.getResultRegister()) {
                                        // Read Var using variable name already defined
                                        ReadVariableNode rvn = new ReadVariableNode(fnWVN.getVariableName(), newFnRegister, globalBaseReg, loaderDummySourceLocation);
                                        bb.addNode(rvn);
                                        usedUserGlobal = true;
                                    }
                                } else {
                                    WritePropertyNode fnWPN = (WritePropertyNode) nodeIterator[i + 1];
                                    boolean checkforBaseVar = lastRVN != null && fnWPN.getBaseRegister() == lastRVN.getResultRegister();
                                    boolean checkforBaseProp = !historyRPNs.isEmpty() && fnWPN.getBaseRegister() == historyRPNs.get(historyRPNs.size()-1).getResultRegister();
                                    if (fnWPN.getValueRegister() == dfn.getResultRegister() && (checkforBaseProp || checkforBaseVar)) {

                                        if (checkforBaseVar) {
                                            ReadVariableNode  rvn = new ReadVariableNode(lastRVN.getVariableName(), fnWPN.getBaseRegister(), globalBaseReg, loaderDummySourceLocation);
                                            bb.addNode(rvn);
                                        } else {
                                            List<AbstractNode> nodesToAdd = new ArrayList<>();
                                            int childBaseReg = fnWPN.getBaseRegister();
                                            for (int j=(historyRPNs.size()-1);j >= 0; j--){
                                                ReadPropertyNode evalRPN = historyRPNs.get(j);
                                                if (childBaseReg == evalRPN.getResultRegister()) {
                                                    ReadPropertyNode rpn;
                                                    if (evalRPN.getPropertyRegister() == -1) {
                                                        rpn = new ReadPropertyNode(evalRPN.getBaseRegister(), evalRPN.getPropertyString(), childBaseReg, loaderDummySourceLocation);
                                                    } else {
                                                        rpn = new ReadPropertyNode(evalRPN.getBaseRegister(), evalRPN.getPropertyRegister(), childBaseReg, loaderDummySourceLocation);
                                                    }
                                                    if (rpn.toString().contains("read-property[v85,v86,v84]")) {
                                                        String erikwazhere = "";
                                                    }
                                                    nodesToAdd.add(rpn);
                                                    childBaseReg = evalRPN.getBaseRegister();
                                                } else {
                                                    break;
                                                }
                                            }
                                            if (lastRVN == null){
                                                throw new AnalysisException("Last variable found to read is null");
                                            }
                                            ReadVariableNode  rvn = new ReadVariableNode(lastRVN.getVariableName(), childBaseReg, globalBaseReg, loaderDummySourceLocation);
                                            bb.addNode(rvn);
                                            nodesToAdd = Lists.reverse(nodesToAdd);
                                            for (AbstractNode antoadd : nodesToAdd){
                                                bb.addNode(antoadd);
                                            }


                                        }

                                        ReadPropertyNode rpn;
                                        if (fnWPN.getPropertyString() == null) {
                                            rpn = new ReadPropertyNode(fnWPN.getBaseRegister(), fnWPN.getPropertyRegister(), newFnRegister, loaderDummySourceLocation);
                                        } else {
                                            rpn = new ReadPropertyNode(fnWPN.getBaseRegister(), fnWPN.getPropertyString(), newFnRegister, loaderDummySourceLocation);
                                        }
                                        bb.addNode(rpn);
                                        usedUserGlobal = true;
                                    } else if (fnWPN.getValueRegister() == dfn.getResultRegister()) {
                                        System.out.println("\n\nSkipping, NEED to track up source to get a currently existing register value\n\n");
                                        anonFnIndex++;
                                        continue;
                                    }
                                }
                                if (usedUserGlobal) {
                                    WriteVariableNode wvn = new WriteVariableNode(newFnRegister, varName, loaderDummySourceLocation);
                                    bb.addNode(wvn);
                                }
                            }

                            if (!usedUserGlobal) {
                                //int globalBaseReg = getGlobalBaseReg();
                                WriteVariableNode wvn = new WriteVariableNode(dfn.getResultRegister(), varName, loaderDummySourceLocation);
                                //System.out.println("writing to dfn.getResultRegister()" + wvn);
                                //System.out.println("\t " + dfn);

                                bb.addNode(wvn);
                                ReadVariableNode rvn = new ReadVariableNode(varName, dfn.getResultRegister(), globalBaseReg, loaderDummySourceLocation);
                                bb.addNode(rvn);
                            }
                        } else if (fnName != null) {
                            //regular functions
                            String varName = "__" + fnName + "__";
                            //int globalBaseReg = getGlobalBaseReg();
                            int newFnRegister = mainEnv.getRegisterManager().nextRegister();
                            ReadVariableNode rvn = new ReadVariableNode(fnName, newFnRegister, globalBaseReg, loaderDummySourceLocation);

                            WriteVariableNode wvn = new WriteVariableNode(newFnRegister, varName, loaderDummySourceLocation);
                            if (bbIndex == 0){
                                firstNodes.add(rvn);
                                firstNodes.add(wvn);
                            } else {
                                bb.addNode(rvn);
                                bb.addNode(wvn);
                            }
                            funcregs.add(varName);
                        }

                        anonFnIndex++;


                    }
                }
            }
            bbIndex++;
        }
        return funcregs;
    }

    private int getGlobalBaseReg() {
        int globalBaseReg = -1;
        Iterator<BasicBlock> bbIterator = functionAndBlocksManager.getBasicBlocks().iterator();
        while (bbIterator.hasNext() && globalBaseReg == -1) {
            BasicBlock bb = bbIterator.next();
            for (AbstractNode an : bb.getNodes()){
                if (an instanceof ReadVariableNode){
                    ReadVariableNode rvn = (ReadVariableNode) an;
                    if (rvn.getResultBaseRegister() != AbstractNode.NO_VALUE){
                        globalBaseReg = rvn.getResultBaseRegister();
                        break;
                    }
                }
            }
        }
        return globalBaseReg;
    }
    /**
     * Completes the flow graph construction.
     *
     * @param flowGraph existing flow graph if extending, or null if creating a new
     * @param exitBlock the basic block where the last processed block will exit to
     * @see #close()
     */
    public FlowGraph close(FlowGraph flowGraph, BasicBlock exitBlock) {
        closed = true;
        boolean neverBeenDone = flowGraph ==null;

        SourceLocation loaderDummySourceLocation = new SyntheticLocationMaker("call-all-functions-sources-loader").makeUnspecifiedPosition();
        AstEnv mainEnv = this.initialEnv;

        List<String> anonFuncPtrs = createFuncPtrs222(loaderDummySourceLocation, mainEnv);

        AstEnv env = initialEnv.makeAppendBlock(processed.getAppendBlock());
        if (env.getAppendBlock().getExceptionHandler() != null){
            processed = addForcedCallers( env, anonFuncPtrs);
        }

        if (flowGraph == null) {
            processed = addEventDispatchers(initialEnv.getFunction().getEntry().getSourceLocation(), initialEnv.makeAppendBlock(processed.getAppendBlock()));
        }

        if (flowGraph == null) {
            flowGraph = new FlowGraph(initialEnv.getFunction());
        }
        flowGraph.addSyntacticInformation(syntacticInformation, valueLogMappingInformation);

        int origBlockCount = flowGraph.getNumberOfBlocks();
        int origNodeCount = flowGraph.getNumberOfNodes();

        // wire the last processed block to the exit
        if (exitBlock != null) {
            processed.getAppendBlock().addSuccessor(exitBlock);
        }

        Pair<List<Function>, List<BasicBlock>> blocksAndFunctions = functionAndBlocksManager.close();

        for (Function f : blocksAndFunctions.getFirst()) {
            flowGraph.addFunction(f);
        }
        flowGraph.getFunctions().forEach(f -> setEntryBlocks(f, functionAndBlocksManager));

        // bypass empty basic blocks
        boolean changed;
        do {
            changed = false;
            for (BasicBlock b1 : blocksAndFunctions.getSecond()) {
                for (BasicBlock b2 : newList(b1.getSuccessors())) {
                    // b1 has an ordinary edge to b2
                    if (b2.isEmpty()) {
                        // b2 is empty, bypass it
                        b1.removeSuccessor(b2);
                        for (BasicBlock b3 : b2.getSuccessors()) {
                            b1.addSuccessor(b3);
                            if (!b1.isEmpty() && b1.getLastNode() instanceof IfNode) {
                                // 'if' nodes have their own successors
                                IfNode ifn = (IfNode) b1.getLastNode();
                                BasicBlock succTrue = ifn.getSuccTrue();
                                BasicBlock succFalse = ifn.getSuccFalse();
                                if (b2 == succTrue && b2 == succFalse) {
                                    ifn.setSuccessors(b3, b3);
                                } else if (b2 == succTrue)
                                    ifn.setSuccessors(b3, succFalse);
                                else if (b2 == succFalse)
                                    ifn.setSuccessors(succTrue, b3);
                            }
                        }
                        changed = true; // b3 may itself be empty, so repeat (naive but fast enough in practice)
                    }
                }
            }
        } while (changed);

        // add each non-empty basic block to the flow graph
        for (BasicBlock b : blocksAndFunctions.getSecond()) {
            if (!b.isEmpty()) {
                flowGraph.addBlock(b);
            }
        }

        // complete links from end-for-in nodes to begin-for-in nodes (cannot be done at constructor time due to later cloning)
        Collection<EndForInNode> ends = newList();
        for (Function f : flowGraph.getFunctions()) {
            for (BasicBlock b : f.getBlocks()) {
                for (AbstractNode n : b.getNodes()) {
                    if (n instanceof EndForInNode) {
                        ends.add((EndForInNode) n);
                    }
                    if (n instanceof BeginForInNode) {
                        ((BeginForInNode) n).setEndNodes(Collections.newSet());
                    }
                }
            }
        }
        for (EndForInNode end : ends) {
            end.getBeginNode().getEndNodes().add(end);
        }

        // set block orders
        flowGraph.complete();

        // Avoid changes to block- & node-indexes due to a change in a hostenv-source.
        // (dynamically added code from eval et. al will still change)
        List<Function> sortedFunctions = newList(flowGraph.getFunctions());
        FlowGraph finalFlowGraph = flowGraph;
        try {
            sortedFunctions.sort((f1, f2) -> {

                Boolean f1host = finalFlowGraph.isHostEnvironmentSource(f1.getSourceLocation());
                Boolean f2host = finalFlowGraph.isHostEnvironmentSource(f2.getSourceLocation());

                int comp = f1host.compareTo(f2host);
                if (comp != 0){
                    return comp;
                } else {
                    String f1_name = f1.getSourceLocation().toString() + " " + f1.getName();
                    String f2_name = f2.getSourceLocation().toString() + " " + f1.getName();
                    if (f1.isMain()){
                        return -100;
                    } else if (f2.isMain()){
                        return 100;
                    }
                    if (f1.getSourceLocation().getLocation().equals(f2.getSourceLocation().getLocation())){
                        return f1.getSourceLocation().getLineNumber() - f2.getSourceLocation().getLineNumber();
                    }
                    return f1_name.compareTo(f2_name);
                }
            });
        } catch (IllegalArgumentException iae) {
            System.out.println(iae.getMessage());
        }

        int nodeCount = origNodeCount;
        int blockCount = origBlockCount;
        for (Function function : sortedFunctions) {
            //System.out.println("\t"+function + " " + function.getSourceLocation());
            List<BasicBlock> blocks = newList(function.getBlocks());
            blocks.sort(Comparator.comparingInt(BasicBlock::getOrder));

            for (BasicBlock block : blocks) {
                if (block.getIndex() == -1) {
                    block.setIndex(blockCount++);
                }
                for (AbstractNode n : block.getNodes())
                    if (n.getIndex() == -1) {
                        n.setIndex(nodeCount++);
                    }
            }
        }
        if (neverBeenDone) {
            System.out.println("%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%");
            for (Function function : sortedFunctions) {

                System.out.println("%" + function.toString() + " numblocks=" + function.getBlocks().size());
                for (BasicBlock block : function.getBlocks()) {
                    System.out.println("%\t" + block.getIndex() + " numnodes=" + block.getNodes().size());
                    for (AbstractNode n : block.getNodes())
                        System.out.println("%\t\t" + n.getIndex() + ") " + n.toString() + " " + n.getSourceLocation().toString());
                }
            }
            System.out.println("%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%");
        }


        return flowGraph;
    }

    /**
     * Sets the entry block of every block in a function.
     */
    private static void setEntryBlocks(Function f, FunctionAndBlockManager functionAndBlocksManager) {
        Stack<BasicBlock> entryStack = new Stack<>();
        entryStack.push(f.getEntry());

        setEntryBlocks(new TripleForSetEntryBlocksWorklist(null, f.getEntry(), entryStack), newSet(), functionAndBlocksManager);

        // needed if the blocks are unreachable
        f.getOrdinaryExit().setEntryBlock(f.getEntry());
        f.getExceptionalExit().setEntryBlock(f.getEntry());
    }

    public static final class TripleForSetEntryBlocksWorklist {

        private final BasicBlock predecessor;

        private final BasicBlock target;

        private final Stack<BasicBlock> entryStack;

        public TripleForSetEntryBlocksWorklist(BasicBlock predecessor, BasicBlock target, Stack<BasicBlock> entryStack) {
            this.predecessor = predecessor;
            this.target = target;
            this.entryStack = entryStack;
        }
    }

    /**
     * Recursively sets BasicBlock.entry_block
     * All blocks between "Begin" and "End" nodes form a region with a changed entry block see {@link BasicBlock#entry_block}
     */
    public static void setEntryBlocks(TripleForSetEntryBlocksWorklist startingPoint, Set<BasicBlock> visited, FunctionAndBlockManager functionAndBlocksManager) {
        LinkedList<TripleForSetEntryBlocksWorklist> worklist = new LinkedList<>();
        worklist.add(startingPoint);
        while (!worklist.isEmpty()) {
            TripleForSetEntryBlocksWorklist current = worklist.removeFirst();
            if (visited.contains(current.target)) {
                continue;
            }
            visited.add(current.target);

            Stack<BasicBlock> successorEntryStack = new Stack<>();
            successorEntryStack.addAll(current.entryStack);
            Stack<BasicBlock> exceptionEntryStack = new Stack<>();
            exceptionEntryStack.addAll(current.entryStack);
            current.target.setEntryBlock(successorEntryStack.peek());
            if (current.target == current.target.getEntryBlock()) {
                current.target.setEntryPredecessorBlock(current.predecessor);
            }
            if (!current.target.isEmpty()) {
                AbstractNode lastNode = current.target.getLastNode();
                if (!Options.get().isForInSpecializationDisabled()) {
                    if (lastNode instanceof BeginForInNode) {
                        successorEntryStack.push(current.target.getSingleSuccessor());
                    }
                    if (lastNode instanceof EndForInNode) {
                        successorEntryStack.pop();
                        exceptionEntryStack.pop();
                    }
                }
            }
            if (successorEntryStack.isEmpty()) {
                throw new AnalysisException("Empty entry_block stack due to " + current.target);
            }
            Set<BasicBlock> unvisitedSuccessors = newSet();
            unvisitedSuccessors.addAll(current.target.getSuccessors());
            unvisitedSuccessors.addAll(functionAndBlocksManager.getUnreachableSyntacticSuccessors(current.target));
            unvisitedSuccessors.removeAll(visited);
            unvisitedSuccessors.remove(null);
            worklist.addAll(unvisitedSuccessors.stream().map(b -> new TripleForSetEntryBlocksWorklist(current.target, b, successorEntryStack)).collect(Collectors.toList()));
            BasicBlock exceptionHandler = current.target.getExceptionHandler();
            if (exceptionHandler != null && !visited.contains(exceptionHandler)) {
                worklist.add(new TripleForSetEntryBlocksWorklist(current.target, exceptionHandler, exceptionEntryStack));
            }
        }
    }

    /**
     * Creates the nodes responsible for execution of registered event-handlers.
     */
    private TranslationResult addEventDispatchers(SourceLocation location, AstEnv env) {
        BasicBlock appendBlock = env.getAppendBlock();
        boolean needsEventLoop = Options.get().isDOMEnabled() || Options.get().isAsyncEventsEnabled();
        if (needsEventLoop) {
            appendBlock = makeSuccessorBasicBlock(appendBlock, functionAndBlocksManager);

            BasicBlock weakCatcher = injectCatcherForFunction(location, env);
            weakCatcher.addSuccessor(appendBlock);

            NopNode nopEntryNode = new NopNode("eventDispatchers: entry", location);
            nopEntryNode.setArtificial();
            appendBlock.addNode(nopEntryNode);

            if (Options.get().isDOMEnabled()) {
                BasicBlock lastDOMContentLoadedEventLoopBlock = addAsyncBlocks(Type.DOM_CONTENT_LOADED, true, "DOMContentLoaded", location, env.makeAppendBlock(appendBlock));
                BasicBlock lastLoadEventLoopBlock = addAsyncBlocks(Type.DOM_LOAD, true, "Load", location, env.makeAppendBlock(lastDOMContentLoadedEventLoopBlock));
                BasicBlock lastOtherEventLoopBlock = addAsyncBlocks(Type.DOM_OTHER, true, "Other", location, env.makeAppendBlock(lastLoadEventLoopBlock));
                BasicBlock lastUnloadEventLoopBlock = addAsyncBlocks(Type.DOM_UNLOAD, true, "Unload", location, env.makeAppendBlock(lastOtherEventLoopBlock));
                appendBlock = lastUnloadEventLoopBlock;
            } else if (Options.get().isAsyncEventsEnabled()) {
                appendBlock = addAsyncBlocks(Type.ASYNC, true, "Async", location, env.makeAppendBlock(appendBlock));
            }
        }
        return TranslationResult.makeAppendBlock(appendBlock);
    }

    /**
     * Injects an intermediary block before the exceptional exit of a function which can be used to maybe-ignore the exceptional data flow.
     *
     * @return block which maybe-ignores the exceptional dataflow of the function
     */
    private BasicBlock injectCatcherForFunction(SourceLocation location, AstEnv env) {
        // Implementation note: this replaces the current exceptional exit of the function.
        // Alternative strategies are:
        // (A) rewire all blocks with the current excepitonal exit as exception handler (this is a different hacky solution)
        // (B) use intermediary exception handler while constructing a function, and wire that handler and the exceptional exit together when done building the function (this is not hacky, but requires some refactorings)

        BasicBlock catchBlock = env.getFunction().getExceptionalExit();
        List<AbstractNode> exciptionalExitNodes = newList(catchBlock.getNodes());
        catchBlock.getNodes().clear();
        BasicBlock rethrowBlock = makeBasicBlock(env.getFunction(), functionAndBlocksManager);
        catchBlock.addSuccessor(rethrowBlock);
        BasicBlock newExceptionalExit = makeBasicBlock(env.getFunction(), functionAndBlocksManager);
        newExceptionalExit.getNodes().addAll(exciptionalExitNodes);
        rethrowBlock.setExceptionHandler(newExceptionalExit);
        env.getFunction().setExceptionalExit(newExceptionalExit);

        int catchRegister = env.getRegisterManager().nextRegister();
        CatchNode catchNode = new CatchNode(catchRegister, location);
        ThrowNode rethrowNode = new ThrowNode(catchRegister, location);
        catchNode.setArtificial();
        rethrowNode.setArtificial();
        addNodeToBlock(catchNode, catchBlock, env.makeStatementLevel(false));
        addNodeToBlock(rethrowNode, rethrowBlock, env);

        return catchBlock;
    }

    /**
     * Appends the required blocks for handling asyncronous dataflow in the flowgraph.
     * The blocks contains an event dispatcher for the chosen event type.
     */
    private BasicBlock addAsyncBlocks(Type eventType, boolean loop, String prettyEventName, SourceLocation location, AstEnv env) {
        Function fun = initialEnv.getFunction();
        BasicBlock appendBlock = env.getAppendBlock();
        // TODO support fire-once, but in unknown order handlers (e.g. load)

        // block structure
        BasicBlock first = makeSuccessorBasicBlock(appendBlock, functionAndBlocksManager);
        BasicBlock ordinaryExit = makeSuccessorBasicBlock(first, functionAndBlocksManager);
        BasicBlock exceptionalExit = makeCatchBasicBlock(first, functionAndBlocksManager);
        BasicBlock exceptionalExitRethrow = makeSuccessorBasicBlock(exceptionalExit, functionAndBlocksManager);
        // TODO minor optimization: make ordinaryExit and last the same block (also skips a node)
        BasicBlock last = makeSuccessorBasicBlock(ordinaryExit, functionAndBlocksManager);

        // will continue execution ...
        exceptionalExit.addSuccessor(last);
        exceptionalExit.setExceptionHandler(null);
        // ... but the global exceptional exit also gets flow (for error reporting only)
        exceptionalExitRethrow.setExceptionHandler(fun.getExceptionalExit());

        appendBlock.addSuccessor(last); // may skip loop entirely
        if (loop) {
            last.addSuccessor(first); // back loop
        }

        // nodes
        EventDispatcherNode dispatcherNode = new EventDispatcherNode(eventType, location);
        NopNode nopOrdinaryExitNode = new NopNode("eventDispatchers: ordinary exit " + prettyEventName, location);
        NopNode nopExceptionExitNode = new NopNode("eventDispatchers: exceptional exit " + prettyEventName, location);
        int catchRegister = env.getRegisterManager().nextRegister();
        CatchNode catchNode = new CatchNode(catchRegister, location);
        ThrowNode rethrowNode = new ThrowNode(catchRegister, location);
        NopNode nopLastNode = new NopNode("eventDispatchers: post " + prettyEventName, location);
        nopOrdinaryExitNode.setArtificial();
        nopExceptionExitNode.setArtificial();
        catchNode.setArtificial();
        rethrowNode.setArtificial();
        nopLastNode.setArtificial();
        addNodeToBlock(dispatcherNode, first, env);
        addNodeToBlock(nopOrdinaryExitNode, ordinaryExit, env);
        addNodeToBlock(catchNode, exceptionalExit, env.makeStatementLevel(false));
        addNodeToBlock(nopExceptionExitNode, exceptionalExit, env.makeStatementLevel(false));
        addNodeToBlock(rethrowNode, exceptionalExitRethrow, env);
        addNodeToBlock(nopLastNode, last, env);

        return last;
    }

    public ASTInfo getAstInfo() {
        return astInfo;
    }

    /**
     * Creates a call to a function that defines and calls functions containing the host function sources.
     *
     * @see HostEnvSources
     */
    public void addLoadersForHostFunctionSources(List<URL> sources) {
        if (sources.isEmpty()) {
            return;
        }
        // make loader
        AstEnv mainEnv = this.initialEnv;
        SourceLocation loaderDummySourceLocation = new SyntheticLocationMaker("host-environment-sources-loader").makeUnspecifiedPosition();

        BasicBlock appendBlock = mainEnv.getFunction().getEntry().getSingleSuccessor();
        for (URL source : sources) {
            appendBlock = makeSuccessorBasicBlock(appendBlock, functionAndBlocksManager);
            int sourceRegister = mainEnv.getRegisterManager().nextRegister();
            int internalRegister = mainEnv.getRegisterManager().nextRegister();
            int loadedFunctionRegister = mainEnv.getRegisterManager().nextRegister();

            ConstantNode sourceStringNode = ConstantNode.makeString(source.toString(), sourceRegister, loaderDummySourceLocation);
            ConstantNode internalFlagNode = ConstantNode.makeBoolean(true, internalRegister, loaderDummySourceLocation);
            CallNode callLoadNode = new CallNode(loadedFunctionRegister, TAJSFunctionName.TAJS_LOAD, newList(Arrays.asList(sourceRegister, internalRegister)), loaderDummySourceLocation);
            CallNode callLoadedNode = new CallNode(false, AbstractNode.NO_VALUE, AbstractNode.NO_VALUE, loadedFunctionRegister, newList(), loaderDummySourceLocation);

            addNodeToBlock(sourceStringNode, appendBlock, mainEnv.makeStatementLevel(false));
            addNodeToBlock(internalFlagNode, appendBlock, mainEnv.makeStatementLevel(false));
            appendBlock = makeSuccessorBasicBlock(appendBlock, functionAndBlocksManager);
            addNodeToBlock(callLoadNode, appendBlock, mainEnv.makeStatementLevel(false));
            appendBlock = makeSuccessorBasicBlock(appendBlock, functionAndBlocksManager);
            addNodeToBlock(callLoadedNode, appendBlock, mainEnv.makeStatementLevel(false));
        }

        BasicBlock postCallLoaderBlock = makeSuccessorBasicBlock(appendBlock, functionAndBlocksManager);
        processed = TranslationResult.makeAppendBlock(postCallLoaderBlock);
    }

    /**
     * Creates a Function for the given source.
     * <p>
     * <pre>
     *  function (parameters[0], parameters[1], ...) {
     *      SOURCE
     *  }
     * </pre>
     */
    public Function transformFunctionBody(String source, List<String> parameterNames, SourceLocationMaker sourceLocationMaker) {
        final AstEnv env = initialEnv.makeAppendBlock(processed.getAppendBlock());

        // create a synthetic wrapper function with the source as body
        ProgramTree tree = makeAST(source, 0, 0, sourceLocationMaker);
        List<IdentifierExpressionTree> parameters =
                parameterNames.stream().map(
                        n -> new IdentifierExpressionTree(null, new IdentifierToken(null, n)))
                        .collect(Collectors.toList());

        FormalParameterListTree params = new FormalParameterListTree(tree.location, ImmutableList.copyOf(parameters));

        Function function = new FunctionBuilder(astInfo, functionAndBlocksManager, sourceLocationMaker, makeSyntacticAnalysis()).processFunctionDeclaration(Kind.EXPRESSION, null, params, tree, env.makeResultRegister(AbstractNode.NO_VALUE), makeSourceLocation(tree, sourceLocationMaker), source);

        return function;
    }

    public static FlowGraphBuilder makeForMain(SourceLocationMaker sourceLocationMaker) {
        AstEnv env = AstEnv.makeInitial();
        Function main = new Function(null, null, null, sourceLocationMaker.makeUnspecifiedPosition());
        FunctionAndBlockManager fab = new FunctionAndBlockManager();
        env = setupFunction(main, env, fab);
        return new FlowGraphBuilder(env, fab);
    }

    private SyntacticAnalysis makeSyntacticAnalysis() {
        return new SyntacticAnalysis(syntacticInformation, new ValueLogLocationRemapping(valueLogMappingInformation));
    }
}
