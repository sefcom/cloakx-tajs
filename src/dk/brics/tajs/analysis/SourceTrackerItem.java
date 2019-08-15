package dk.brics.tajs.analysis;

import dk.brics.tajs.flowgraph.AbstractNode;
import dk.brics.tajs.flowgraph.SourceLocation;

import java.util.ArrayList;
import java.util.List;

public class SourceTrackerItem {
    List<AbstractNode> nodes = new ArrayList<>();

    public SourceTrackerItem(AbstractNode node){
        nodes.add(node);

    }

    public void add(AbstractNode node){
        nodes.add(node);
    }

    public String toString(){
        StringBuffer sb = new StringBuffer();
        for (AbstractNode node : nodes){
            if (sb.length() == 0) {
                sb.append(node);
            } else {
                sb.append(",");
                sb.append(node);
            }
        }
        return sb.toString();
    }

}
