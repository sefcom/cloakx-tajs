package dk.brics.tajs.analysis.dom;

import dk.brics.tajs.analysis.HostAPIs;
import dk.brics.tajs.lattice.HostObject;

public class DynamicDOMObject implements HostObject {
    private HostAPIs api;

    private String string;


    public DynamicDOMObject(String str) {
        api = HostAPIs.CHROME_EXTENSION_APIS;
        string = str;
    }


    @Override
    public String toString() {
        return string;
    }

    @Override
    public HostAPIs getAPI() {
        return api;
    }

    public boolean equalsString(String a){
        return string.equals(a);
    }
}