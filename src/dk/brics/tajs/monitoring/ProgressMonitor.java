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
import dk.brics.tajs.flowgraph.AbstractNode;
import dk.brics.tajs.flowgraph.BasicBlock;
import dk.brics.tajs.lattice.Context;
import dk.brics.tajs.lattice.State;
import dk.brics.tajs.options.Options;
import dk.brics.tajs.solver.BlockAndContext;
import org.apache.log4j.Logger;

import java.util.Set;
import java.util.stream.Stream;

import static dk.brics.tajs.util.Collections.newSet;

/**
 * Monitor for printing progress during analysis.
 */
public class ProgressMonitor extends PhaseMonitoring<ProgressMonitor.PreScanProgressMonitor, DefaultAnalysisMonitoring> {

    private static Logger log = Logger.getLogger(ProgressMonitor.class);

    public ProgressMonitor() {
        super(new PreScanProgressMonitor(), new DefaultAnalysisMonitoring());
    }

    public static class PreScanProgressMonitor extends DefaultAnalysisMonitoring {

        private int nodeTransfers = 0;

        private long lastPrintProgress = 0;

        private long stateSize = 0;

        private long preStateSize;

        private Set<AbstractNode> visitedNonHostNodes = newSet();

        private Solver.SolverInterface c;

        public int getNodeTransfers() {
            return nodeTransfers;
        }

        public long getStateSize() {
            return stateSize;
        }

        public Set<AbstractNode> getVisitedNonHostNodes() {
            return visitedNonHostNodes;
        }@Override
        public void setSolverInterface(Solver.SolverInterface c){
            this.c = c;
        }

        @Override
        public void visitNodeTransferPre(AbstractNode n, State s) {
            nodeTransfers++;
            if (c.getFlowGraph().isUserCode(n))
                visitedNonHostNodes.add(n);
        }

        @Override
        public void visitPropagationPre(BlockAndContext<Context> from, BlockAndContext<Context> to) {
            State s = c.getAnalysisLatticeElement().getState(to);
            if (s != null)
                preStateSize = getStateSize(s);
            else
                preStateSize = 0;
        }

        @Override
        public void visitPropagationPost(BlockAndContext<Context> from, BlockAndContext<Context> to, boolean changed) {
            State s = c.getAnalysisLatticeElement().getState(to);
            if (s != null)
                stateSize += getStateSize(s) - preStateSize;
        }

        /**
         * Quick'n'dirty measurement of the "size" of an abstract state.
         */
        private int getStateSize(State s) {
            return s.getStore().values().stream().flatMap(o -> Stream.concat(o.getProperties().values().stream(),
                    Stream.of(o.getDefaultArrayProperty(), o.getDefaultNonArrayProperty(), o.getInternalPrototype(), o.getInternalValue())))
                    .mapToInt(p -> p.getAllObjectLabels().size() + p.typeSize()).sum();
        }

        @Override
        public void visitBlockTransferPre(BasicBlock b, State s) {
            if (log.isDebugEnabled()) {
                log.debug("Selecting worklist entry for block " + b.getIndex() + " at " + b.getSourceLocation());
                log.debug("Worklist: " + c.getWorklist());
                log.debug("Visiting " + b);
//    		    	addFiles.debug("Number of abstract states at this block: " + the_analysis_lattice_element.getSize(block));
                log.debug("Context: " + s.getContext());
            }
        }

        @Override
        public void visitBlockTransferPost(BasicBlock b, State s) {
            if (!log.isDebugEnabled() && log.isInfoEnabled() && !Options.get().isQuietEnabled() ) {
                long t = System.currentTimeMillis();
                if (t - lastPrintProgress > 100 && ! c.getWorklist().isEmpty()) {
                    printProgress();
                    lastPrintProgress = t;
                }
            }
        }

        private void printProgress() {
            System.out.printf("\rNode transfers: %-7d Visited/total nodes: %6d/%-6d Abstract states: %-6d Avg. state size: %-8.2f Call edges: %-6d Worklist size: %-5d          ",
                    nodeTransfers, visitedNonHostNodes.size(), c.getFlowGraph().getNumberOfUserCodeNodes(),
                    c.getAnalysisLatticeElement().getNumberOfStates(),
                    ((double)stateSize) / c.getAnalysisLatticeElement().getNumberOfStates(),
                    c.getAnalysisLatticeElement().getCallGraph().size(),
                    c.getWorklist().size());
            System.out.flush();
        }

        @Override
        public void visitIterationDone() {
            if (!log.isDebugEnabled() && log.isInfoEnabled() && !Options.get().isQuietEnabled()) {
                printProgress();
                System.out.println(); // needed due to '\r' in printProgress
            }
        }
    }
}
