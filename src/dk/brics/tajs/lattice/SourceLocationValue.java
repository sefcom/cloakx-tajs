package dk.brics.tajs.lattice;

import dk.brics.tajs.flowgraph.SourceLocation;

import java.util.Set;

public class SourceLocationValue {
    SourceLocation sl = null;
    Value val = null;

    public SourceLocationValue(SourceLocation sl, Value val) {
        this.sl = sl;
        this.val = val;

    }

    public void updateSourceLocation(State state, Set<String> searchFor, int begin, int end){
        if (sl.isDynamic()){
            for (ObjectLabel ol2 : state.getExecutionContext().getVariableObject()) {
                Obj obj2 = state.getObject(ol2, false);
                Value evalSource = obj2.getProperties().get(sl.getStaticSourceLocation().toString());
                if (evalSource == null){
                    continue;
                }
                ReconstitutedString rs = evalSource.reconstituteString();
                // can there be more than one??
                SourceLocationValue newSLV = rs.getSourceLocation(val.getStrSafely(), begin);
                System.out.println("newSLV=" + newSLV);
                if (newSLV == null){
                    return;
                }
                if (newSLV != null && (begin > 0 || end > 0) && !searchFor.contains(newSLV.val.getStrSafely())){
                    SourceLocation.StaticLocationMaker slm = new SourceLocation.StaticLocationMaker(newSLV.sl.getLocation());
                    int beginCol = newSLV.sl.getColumnNumber();
                    int endCol = newSLV.sl.getEndColumnNumber();
                    if (this.sl.within(newSLV.sl)){
                        beginCol = beginCol + this.sl.getAdjustedColumnNumber();
                        endCol = beginCol + this.sl.getAdjustedEndColumnNumber() - this.sl.getColumnNumber();
                    }

                    /*if (begin > 0){
                        beginCol = beginCol + begin;
                    }
                    if (end > 0){
                        endCol = beginCol + end - begin;
                    }*/
                    //System.out.println("STR Point: " + Strings.escape(newSLV.val.getStrSafely()));
                    // TODO: should this deal with multilines?
                    this.sl = slm.make(newSLV.sl.getLineNumber(), beginCol, newSLV.sl.getLineNumber(), endCol);
                } else {
                    this.sl = newSLV.sl;
                }
                this.val = newSLV.val;
            }
        }
    }


    public SourceLocation getSl() {

        if (sl.isDynamic()){
            // if dynamic translate into static
            SourceLocation.StaticLocationMaker slm = new SourceLocation.StaticLocationMaker(sl.getStaticLocation());
            sl = slm.make(sl.getLineNumber(), sl.getColumnNumber(), sl.getLineNumber(), sl.getEndColumnNumber());
        }
        return sl;
    }

    public void setSl(SourceLocation sl) {
        this.sl = sl;
    }

    public Value getVal() {
        return val;
    }

    public void setVal(Value val) {
        this.val = val;
    }

    @Override
    public boolean equals(Object obj){

        if (!(obj instanceof SourceLocationValue))
            return false;
        SourceLocationValue slv = (SourceLocationValue) obj;
        return slv.sl.equals(this.sl) && slv.val.equals(this.val);

    }
}
