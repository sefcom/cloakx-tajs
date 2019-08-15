package dk.brics.tajs.solver;

import dk.brics.tajs.flowgraph.BasicBlock;
import dk.brics.tajs.flowgraph.FlowGraph;
import dk.brics.tajs.flowgraph.Function;

import java.util.HashSet;
import java.util.Set;

public class SSyncher extends SolverSynchronizer{
    BasicBlock active = null;
    Set<BasicBlock> pending = new HashSet<>();
    public SSyncher() {
        this.turnOnSingleStep();
    }
    @Override
    public void waiting() {

        try {
            System.out.println("WAITING!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!");
            Thread.sleep(100);
        } catch (InterruptedException e) {

        }
    }
    public boolean shouldWait(){
        return (active != null);
    }

    public void unMarkActiveBlock(){
        active = null;
    }
    @Override
    public void setFlowGraph(FlowGraph g) {

    }

    @Override
    public void markActiveBlock(BasicBlock b) {
        active = b;
    }

    @Override
    public void markPendingBlock(BasicBlock b) {

    }

    @Override
    public void callEdgeAdded(Function source, Function target) {

    }
}