package dk.brics.tajs.lattice;

import dk.brics.tajs.flowgraph.SourceLocation;

import java.util.Map;
import java.util.TreeMap;

public class ReconstitutedString {

    StringBuffer str = new StringBuffer();
    TreeMap<Integer, SourceLocationValue> SLStrMap = new TreeMap<>();

    public void append(String astr, SourceLocation sl, Value val){
        if (!astr.isEmpty()){
            str.append(astr);
            SLStrMap.put((str.length()-1), new SourceLocationValue(sl, val));
        }
    }
    public int getLength(){
        return str.length();
    }
    public boolean contains(String searchVal){
        return (str.indexOf(searchVal) > -1);
    }
    public boolean containsHTML(){
        int firstopen = str.indexOf("<");
        int firstclose = str.indexOf(">");
        return firstopen > -1 && (firstopen +1) < firstclose;

    }
    public String getString(int start, int end){
        return str.substring(start, end);
    }
    public String getString(){
        return str.toString();
    }
    public SourceLocationValue getSourceLocation(int strpos){
        Map.Entry<Integer, SourceLocationValue> ent = SLStrMap.ceilingEntry(strpos);
        if (ent == null){
            return null;
        }
        SourceLocationValue slv = ent.getValue();

        return ent.getValue();
    }

    public SourceLocationValue getSourceLocation(String searchStr, int offset){
        if (str.indexOf(searchStr) > -1){
            SourceLocationValue slv = getSourceLocation(str.indexOf(searchStr) + offset);
            if (slv == null) {

                slv =   getSourceLocation(str.indexOf(searchStr));
            }
            if (slv==null){
                System.out.println("str=" + str + " searchStr" + searchStr );
            }
            return slv;
        }
        System.out.println("str=" + str + " searchStr" + searchStr );
        return null;
    }
}
