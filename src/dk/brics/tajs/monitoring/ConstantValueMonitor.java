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

package dk.brics.tajs.monitoring;

import dk.brics.tajs.analysis.Solver;
import dk.brics.tajs.analysis.dom.DOMFunctions;
import dk.brics.tajs.flowgraph.AbstractNode;
import dk.brics.tajs.flowgraph.FlowGraph;
import dk.brics.tajs.flowgraph.jsnodes.CallNode;
import dk.brics.tajs.flowgraph.jsnodes.WritePropertyNode;
import dk.brics.tajs.lattice.Obj;
import dk.brics.tajs.lattice.ObjectLabel;
import dk.brics.tajs.lattice.State;
import dk.brics.tajs.lattice.Value;
import dk.brics.tajs.options.Options;
import dk.brics.tajs.solver.GenericSolver;
import dk.brics.tajs.util.TotalsLog;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static dk.brics.tajs.util.Collections.newSet;

/**
 * Monitor for checking
 */
public class ConstantValueMonitor extends DefaultAnalysisMonitoring {

    private Set<String> targetedJSMethods = new HashSet<>(Arrays.asList("appendChild", "write", "insertBefore", "getElementById"));

    private Map<Value, String> interactsWithDOM = new HashMap<>();

    AnalysisPhase phase = null;

    private FlowGraph fg;

    private Set<CallNode> assertionCallNodes = newSet();

    private Set<CallNode> reachableAssertionCallNodes = newSet();

    private Set<String> searchFor = null;

    private Set<String> searchType = null;

    public ConstantValueMonitor(String searchFor, String searchType) {


        this.searchFor = new HashSet<> (Arrays.asList(searchFor.split(",")));

        //this.searchFor = searchFor;
        //this.searchType = searchType;

        if (searchFor.length() > 0){
            String allInterestingProps = "id,class,classlist,classname";
            if (searchType.length()>1){
                allInterestingProps += "," + searchType;
            }
            this.searchType= new HashSet<> (Arrays.asList(allInterestingProps.toLowerCase().split(",")));
        }
        TotalsLog.addSearchFor(searchFor);

    }

    /*private static Set<CallNode> getAssertionCallNodes(FlowGraph flowGraph) {
        Set<TAJSFunctionName> assertionFunctions = newSet(Arrays.asList(TAJS_ASSERT, TAJS_ASSERT_EQUALS));
        return flowGraph.getFunctions().stream()
                .flatMap(f -> f.getBlocks().stream())
                .flatMap(b -> b.getNodes().stream())
                .filter(n -> n instanceof CallNode)
                .map(cn -> (CallNode) cn)
                .filter(cn -> assertionFunctions.contains(cn.getTajsFunctionName()))
                // ignore trivial TAJS_assert(false), which is used to assert dead code
                // ignore TAJS_assert(x, y, z, false), which is used to allow the assertion to be unreachable anyway
                .filter(cn -> !(cn.getTajsFunctionName() == TAJS_ASSERT && flowGraph.getSyntacticInformation().getTajsCallsWithLiteralFalseAsFirstOrFourthArgument().contains(cn)))
                .collect(Collectors.toSet());
    }*/

    @SuppressWarnings("unchecked")
    @Override
    public void visitNodeTransferPre(AbstractNode n, State s) {
        if (assertionCallNodes.contains(n) && !s.isNone()) {
            reachableAssertionCallNodes.add((CallNode) n); // safe cast due to set containment
        }
        if (phase == AnalysisPhase.ANALYSIS) {
            /*if (n.getIndex() == 8){
                System.out.println(s);
                String yo="";
            }*/

        }
    }

    @Override
    public void setSolverInterface(Solver.SolverInterface c) {
        this.fg = c.getFlowGraph();
    }

    @Override
    public void visitPhasePre(AnalysisPhase phase) {
        this.phase = phase;
        if (phase == AnalysisPhase.SCAN) {
            //assertionCallNodes.addAll(getAssertionCallNodes(fg));
        }
    }

    @Override
    public void visitNodeTransferPost(AbstractNode node, State state) {

        if (phase == AnalysisPhase.SCAN) {
            if (node.toString().contains("innerHTML")){
                System.out.println("Found inner html " + node.toString() +  " ");
                if (node instanceof WritePropertyNode){
                    WritePropertyNode ihWPN = (WritePropertyNode) node;
                    Value nodeVal = state.getRegisters().get(ihWPN.getValueRegister());
                    System.out.println("\t" + ihWPN.getValueRegister() + ": " + nodeVal);
                }
            }
            // this traps whether an object has been appended to the DOM
            if (node instanceof CallNode) {
                CallNode cn = ((CallNode) node);
                String fnName = cn.getPropertyString();

                if (targetedJSMethods.contains(fnName)) {
                    /*if (cn.getBaseRegister() < state.getRegisters().size() ){
                        Value v = state.getRegisters().get(cn.getBaseRegister());

                        for (ObjectLabel ol : v.getObjectLabels()){
                            if (HTMLBodyElement.INSTANCES.compareTo(ol) == 0){
                                String erikwayzhere="";
                                for (int i =0; i < cn.getNumberOfArgs(); i++){
                                    int attachedRegisterNum = cn.getArgRegister(i);
                                    if (attachedRegisterNum < state.getRegisters().size()){
                                        interactsWithDOM.add(state.getRegisters().get(attachedRegisterNum));
                                    }
                                }
                            }
                            System.out.println("SKIPPING " + cn + " " + ol);
                        }

                    }*/
                    String erikwayzhere = "";
                    //System.out.println("\n\n---------------------------" + cn.getIndex() +  "--------------------------------");
                    for (int i = 0; i < cn.getNumberOfArgs(); i++) {
                        int attachedRegisterNum = cn.getArgRegister(i);
                        if (attachedRegisterNum < state.getRegisters().size()) {
                            //Value toAdd = state.getRegisters().get(attachedRegisterNum);
                            /*System.out.println("Adding to IWD " + toAdd.hashCode());
                            for (ObjectLabel ol : toAdd.getObjectLabels()) {
                                Obj obj = state.getObject(ol, false);
                                System.out.println("\t\tol=" + ol + " " + ol.hashCode() + " " + obj.getProperties().size() + " " + obj.getProperties().containsKey("innerHTML"));
                            }*/
                            interactsWithDOM.put(state.getRegisters().get(attachedRegisterNum), fnName);
                        }
                    }
                    //System.out.println("-----------------------------------------------------------\n\n");

                    //FIXME: this should be temprary until I create flag for ovverriding getElementId output

                    int resultReg = cn.getResultRegister();
                    if (resultReg > -1) {
                        Value result = state.getRegisters().get(resultReg);
                        if (fnName.equals("getElementById")) {
                            if (cn.toString().contains("v7")) {
                                String erikwazhere = "";
                            }
                            if (result == null) {

                                GenericSolver.SolverInterface gs = state.getSolverInterface();
                                Value fakeDOMObj = Value.makeObject(DOMFunctions.getHTMLObjectLabel("div", gs));

                                interactsWithDOM.put(fakeDOMObj, fnName);
                                state.getRegisters().set(resultReg, fakeDOMObj);
                            } else {
                                // interactsWithDOM.put(result, fnName);
                            }
                        }
                    }
                    //String erikwaznthere="";
                }
            }
            if (node instanceof CallNode || node instanceof WritePropertyNode) {
                if (node.toString().contains("write-property") && node.toString().contains("innerHTML")) {
                    String erikwazhere = "";
                    //System.out.println("\t------>>> checking write property node " + interactsWithDOM.isEmpty());
                }
                if (!interactsWithDOM.isEmpty()) {
                    if (node.toString().contains("appendChild") || node.toString().contains("innerHTML")){
                        /*System.out.println("\n\n@@@@@@@@@@@@@@@@@@@@@@ HERE @@@@@@@@@@@@@@@@@@@@@@@@@@@@");
                        System.out.println("n@@@@@@@@@@ " + node.getIndex() + " " + node.toString() + " @@@@@@@@@@@@");*/

                        State cs = (State) state;
                        for (Map.Entry<ObjectLabel, Obj> ent : cs.getStore().entrySet()){
                            //System.out.println("Stored:" + ent.getKey().toString() + " " + ent.getKey().hashCode()) ;

                            if (ent.getKey().toString().contains("HTMLDivElement")){
                                Value ihval = ent.getValue().getProperties().get("innerHTML");
                                if (ihval != null){
                                    //System.out.println("\t" + current_node );
                                    //System.out.println("\t\t" + ihval.valueHistory);
                                }

                            }
                        }

                        for (Map.Entry<Value, String> ent: interactsWithDOM.entrySet()) {
                            Value v = ent.getKey();
                            String fnName = ent.getValue();
                            for (ObjectLabel ol : v.getObjectLabels()) {
                                Obj obj = state.getObject(ol, false);
                                //System.out.println("\t\tIWDOM fn=" + fnName + "  ol=" + ol + " " + ol.hashCode() + " " + obj.getProperties().size() + " " + obj.getProperties().containsKey("innerHTML"));

                            }
                        }
                        //System.out.println("n@@@@@@@@@@@@@@@@@@@@@@ HERE @@@@@@@@@@@@@@@@@@@@@@@@@@@@\n\n");
                    }
                    state.genRelevantSourceLocs(searchFor, searchType, interactsWithDOM);
                }
                //if (s.contains(searchFor, searchType, interactsWithDOM)){
                   /* System.out.println("-------------------------------------------------------");
                    System.out.println("\t\t " + n + " " + s );
                    System.out.println("-------------------------------------------------------");*/
                //s.genRelevantSourceLocs(searchFor, searchType, interactsWithDOM);
                //}
            }
        }
    }

    @Override
    public void visitPhasePost(AnalysisPhase phase) {
        this.phase = phase;

        /*if (phase == AnalysisPhase.SCAN && analysisReachedFixedPoint.get()) {
            Set<CallNode> unreachable = newSet(assertionCallNodes);
            unreachable.removeAll(reachableAssertionCallNodes);
            if (!unreachable.isEmpty()) {
                List<String> sourceLocationStrings = unreachable.stream().map(AbstractNode::getSourceLocation).sorted().map(SourceLocation::toString).collect(Collectors.toList());
                throw new AssertionError("Some TAJS assertions were not invoked: " + String.join(", ", sourceLocationStrings));
            }
        }*/
    }
}
