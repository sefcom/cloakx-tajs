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

package dk.brics.tajs.analysis.dom;

import com.google.gson.Gson;
import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import dk.brics.tajs.analysis.Conversion;
import dk.brics.tajs.analysis.Exceptions;
import dk.brics.tajs.analysis.FunctionCalls;
import dk.brics.tajs.analysis.FunctionCalls.CallInfo;
import dk.brics.tajs.analysis.HostAPIs;
import dk.brics.tajs.analysis.InitialStateBuilder;
import dk.brics.tajs.analysis.PropVarOperations;
import dk.brics.tajs.analysis.Solver;
import dk.brics.tajs.analysis.dom.html5.MediaQueryList;
import dk.brics.tajs.analysis.dom.style.CSSStyleDeclaration;
import dk.brics.tajs.analysis.nativeobjects.JSGlobal;
import dk.brics.tajs.flowgraph.EventType;
import dk.brics.tajs.flowgraph.Function;
import dk.brics.tajs.flowgraph.jsnodes.CallNode;
import dk.brics.tajs.lattice.HostAPI;
import dk.brics.tajs.lattice.HostObject;
import dk.brics.tajs.lattice.ObjectLabel;
import dk.brics.tajs.lattice.ObjectLabel.Kind;
import dk.brics.tajs.lattice.State;
import dk.brics.tajs.lattice.Value;
import dk.brics.tajs.options.Options;
import dk.brics.tajs.unevalizer.SimpleUnevalizerAPI;
import dk.brics.tajs.unevalizer.UnevalizerAPI;
import dk.brics.tajs.util.AnalysisException;
import dk.brics.tajs.util.AnalysisLimitationException;
import jdk.nashorn.internal.ir.FunctionCall;
import org.apache.log4j.Logger;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Stream;

import static dk.brics.tajs.analysis.dom.DOMFunctions.createDOMFunction;
import static dk.brics.tajs.analysis.dom.DOMFunctions.createDOMProperty;
import static dk.brics.tajs.analysis.dom.DOMObjects.*;
import static dk.brics.tajs.analysis.dom.DOMWindow.WINDOW;
import static dk.brics.tajs.util.Collections.newSet;

/**
 * Chrome API.
 */
public class ChromeAPI {
    private static String RUNTIME_SENDMESSAGE ="chrome.runtime.sendMessage";
    private static String EXTENSION_SENDMESSAGE ="chrome.extension.sendMessage";
    private static String RUNTIME_ONMESSAGE_ADDLISTENER ="chrome.runtime.onMessage.addListener";
    private static String EXTENSION_ONMESSAGE_ADDLISTENER ="chrome.extension.onMessage.addListener";
    private static String CHROME_RUNTIME_GETURL ="chrome.runtime.getURL";
    private static String EXTENSION_GETURL ="chrome.extension.getURL";
    public static String TABS_EXECUTE_SCRIPT ="chrome.tabs.executeScript";


    private static Logger log = Logger.getLogger(ChromeAPI.class);

    public static ObjectLabel CHROME;
    public static Map<String, DynamicDOMObject> functions = new HashMap<>();

    //public static ObjectLabel CHROME_RUNTIME;

    //public static ObjectLabel CHROME_RUNTIME_ONMESSAGE;

    public static void build(Solver.SolverInterface c) {
        State s = c.getState();
        PropVarOperations pv = c.getAnalysis().getPropVarOperations();
        CHROME = ObjectLabel.make(DOMObjects.CHROME, Kind.OBJECT);
        //CHROME_RUNTIME = ObjectLabel.make(DOMObjects.CHROME_RUNTIME, Kind.OBJECT);
        //CHROME_RUNTIME_ONMESSAGE = ObjectLabel.make(DOMObjects.CHROME_RUNTIME_ONMESSAGE, Kind.OBJECT);

        s.newObject(CHROME);
        s.writeInternalPrototype(CHROME, Value.makeObject(InitialStateBuilder.OBJECT_PROTOTYPE));

        // Global connection to chrome
        createDOMProperty(WINDOW, "chrome", Value.makeObject(CHROME), c);

        /*// chrome
        createDOMProperty(CHROME, "runtime", Value.makeObject(CHROME_RUNTIME), c);
        createDOMFunction(CHROME, DOMObjects.WINDOW_CHROME_LOAD_TIMES, "loadTimes", 0, c);
        createDOMFunction(CHROME, DOMObjects.CHROME_DUMMY, "dummy", 0, c);

        // chrome runtime  ALWAYS remember to add new functions to DOMFunctions
        createDOMProperty(CHROME_RUNTIME, "onMessage", Value.makeObject(CHROME_RUNTIME_ONMESSAGE), c );
        createDOMFunction(CHROME_RUNTIME, CHROME_RUNTIME_SEND_MESSAGE, "sendMessage", 4, c);
        createDOMFunction(CHROME_RUNTIME, DOMObjects.CHROME_RUNTIME_GETURL, "getURL", 4, c);

        // chrome runtime onmessage
        createDOMFunction(CHROME_RUNTIME_ONMESSAGE, DOMObjects.CHROME_RUNTIME_ONMESSAGE_ADDLISTENER, "addListener", 4, c);
*/
        // GOT rid of dynamic property creation because not needed now that I found propagateDeadPaths()
        // erikt
        //createSyntaxFunctionsDynamically(CHROME, c);

        // DOM Registry
        DOMRegistry.registerSendMessageLabel(CHROME);
    }

    private static void createSyntaxFunctionsDynamically(ObjectLabel parent, Solver.SolverInterface context) {
        ChromeAPI cn = new ChromeAPI();
        String className = cn.getClass().getName().replace('.', '/');
        String classJar = cn.getClass().getResource("/" + className + ".class").toString();
        StringBuffer json = new StringBuffer();
        if (classJar.startsWith("jar:")) {
            try {
                InputStream in = cn.getClass().getResourceAsStream("/chrome_api.json");
                BufferedReader reader = new BufferedReader(new InputStreamReader(in));

                String contentLine = reader.readLine();
                while (contentLine != null) {
                    json.append(contentLine);
                    contentLine = reader.readLine();
                }
            } catch (IOException ioex){
                System.out.println("ERROR" + ioex);
                ioex.printStackTrace();
                throw new AnalysisException("Error with reading chromeAPI.json resource file");
            }
        } else {
            Path path = Paths.get("resources/chrome_api.json");
            try (Stream<String> lines = Files.lines(path)) {
                lines.forEach(s -> json.append(s));
            } catch (IOException ex) {
                System.out.println("ERROR" + ex);
                ex.printStackTrace();
                throw new AnalysisException("Error with reading chromeAPI.json file directly");
            }
        }
        if (json.length() > 0){
            System.out.println("JSON length = " + json.length());
            createObjectsFromJson("chrome", json.toString(), parent, context);
        }
    }

    private static void createObjectsFromJson(String parentName, String json, ObjectLabel parent, Solver.SolverInterface context) {
        JsonObject jsonObject = new JsonParser().parse(json.toString()).getAsJsonObject();
        //System.out.println(jsonObject);
        Set<Map.Entry<String, JsonElement>> set = jsonObject.entrySet();
        Iterator<Map.Entry<String, JsonElement>> iterator = set.iterator();
        State state = context.getState();
        PropVarOperations pv = context.getAnalysis().getPropVarOperations();

        while (iterator.hasNext()) {
            Map.Entry<String, JsonElement> entry = iterator.next();
            String key = entry.getKey();
            String globalKey = parentName + "." + entry.getKey();
            JsonElement value = entry.getValue();
            if (null != value) {
                DynamicDOMObject doob = new DynamicDOMObject(globalKey);
                ObjectLabel doobOL = ObjectLabel.make(doob, Kind.OBJECT);

                if (!value.isJsonPrimitive()) {
                    if (key.equals("prototype")) {
                        createObjectsFromJson(parentName, value.toString(), parent, context);
                    } else if (value.isJsonObject()) {
                        createDOMProperty(parent, key, Value.makeObject(doobOL), context);
                        createObjectsFromJson(globalKey, value.toString(), doobOL, context);
                    } else if (value.isJsonArray() && value.toString().contains(":")) {
                        JsonArray array = value.getAsJsonArray();
                        if (null != array) {
                            for (JsonElement arrElement : array) {
                                createDOMProperty(parent, key, Value.makeObject(doobOL), context);
                                createObjectsFromJson(globalKey, arrElement.toString(), doobOL, context);
                            }
                        }
                    } else if (value.isJsonArray() && !value.toString().contains(":")) {
                        throw new AnalysisException("Unexpected object type");
                    }
                } else {
                    String cmpVal = value.toString().replace("\"", "");
                    if (cmpVal.equals("function")) {
                        if (key.equals("constructor")) {
                            // in prototypes the constructor is included as function in definition, but to
                            // attach to prototype's parent, handled when key == prototype
                        } else {
                            createDOMFunction(parent, doob, key, 20, context);
                            //System.out.println(parentName + "." + key + " : '" + value.toString() + "'");
                        }
                    } else if (cmpVal.equals("string")) {
                        createDOMProperty(parent, key, Value.makeAnyStr(), context);
                    } else if (cmpVal.equals("number")) {
                        createDOMProperty(parent, key, Value.makeAnyNum(), context);
                    } else if (cmpVal.equals("boolean")) {
                        createDOMProperty(parent, key, Value.makeAnyBool(), context);
                    }
                }
            }
        }
    }

    private static Value buildCallbackValue(CallInfo call, State state) {
        Set<ObjectLabel> functionLabels = newSet();
        // arg 0 is never a callback
        for (int arg = 0; arg < call.getNumberOfArgs(); arg++) {
            Value param = FunctionCalls.readParameter(call, state, arg);
            for (ObjectLabel ol : param.getObjectLabels()) {
                if (ol.getKind() == Kind.FUNCTION) {
                    functionLabels.add(ol);
                }
            }
        }
        if (functionLabels.isEmpty()) {
            return null;
        } else {
            return Value.makeObject(functionLabels);
        }
    }
    private static void executeCallback(CallInfo call, State state, Solver.SolverInterface c) {
        Set<ObjectLabel> functionLabels = newSet();
        // arg 0 is never a callback
        for (int arg = 0; arg < call.getNumberOfArgs(); arg++) {
            Value param = FunctionCalls.readParameter(call, state, arg);
            for (ObjectLabel ol : param.getObjectLabels()) {
                if (ol.getKind() == Kind.FUNCTION) {
                    List<Value> args = new ArrayList<>();
                    // is it possible to determine the type here?
                    for (String paramname : ol.getFunction().getParameterNames()){
                        args.add(Value.makeAnyStr());
                    }
                    FunctionCalls.callFunction(new FunctionCalls.AbstractCallInfo(call.getSourceNode(), Value.makeObject(ol), args, c.getState()) {

                        @Override
                        public Value getThis() {
                            return Value.makeObject(ol);
                        }
                    }, c);

                }
            }
        }

    }
    public static Value evaluate(DynamicDOMObject nativeObject, final CallInfo call, Solver.SolverInterface c) {
        State s = c.getState();

        if (nativeObject.equalsString(RUNTIME_SENDMESSAGE) || (nativeObject.equalsString(EXTENSION_SENDMESSAGE))) {
            DOMFunctions.expectParameters(nativeObject, call, c, 1, 4);
            executeCallback(call, s, c);

            /*Value callback = buildCallbackValue(call, s);

            if (callback != null) {
                if (callback.isMaybeUndef() || callback.isMaybeNull()) {
                    Exceptions.throwTypeError(c);
                }
                List<Value> eventArgs = new ArrayList<>();
                if (call.getNumberOfArgs() == 2) {
                    eventArgs.add(FunctionCalls.readParameter(call, s, 0));
                } else if (call.getNumberOfArgs() == 3) {
                    Value p0 = FunctionCalls.readParameter(call, s, 0);
                    // if 32 in length and no { then first param must be an extension id
                    if (p0.getStrSafely() != null && p0.getStrSafely().length() == 32 && !p0.getStrSafely().contains("{")) {
                        eventArgs.add(FunctionCalls.readParameter(call, s, 1));
                    } else {
                        eventArgs.add(p0);
                    }
                } else if (call.getNumberOfArgs() == 4) {
                    eventArgs.add(FunctionCalls.readParameter(call, s, 1));
                }
                //eventArgs.add(Value.makeAnyBool());
                eventArgs.add(callback); //callback is last
                //DOMEvents.triggerEventHandler(EventType.SEND_MESSAGE, c, eventArgs);

                executeCallback(call, s, c);

            }*/

            return Value.makeNone();
        } else if (nativeObject.equalsString(RUNTIME_ONMESSAGE_ADDLISTENER) || (nativeObject.equalsString(EXTENSION_ONMESSAGE_ADDLISTENER))) {
            DOMFunctions.expectParameters(nativeObject, call, c, 1, 1);
            Value sm_listener = buildCallbackValue(call, s);

            if (sm_listener != null) {
                if (sm_listener.isMaybeUndef() || sm_listener.isMaybeNull()) {
                    Exceptions.throwTypeError(c);
                }
            }
            DOMEvents.addEventHandler(sm_listener, EventType.SEND_MESSAGE, c);
            System.out.println("adding listener " + sm_listener);

            executeCallback(call, s, c);

            return Value.makeAnyStr();
        } else if (nativeObject.equalsString(CHROME_RUNTIME_GETURL) || nativeObject.equalsString(EXTENSION_GETURL)) {
            DOMFunctions.expectParameters(nativeObject, call, c, 1, 1);

            return FunctionCalls.readParameter(call, s, 0);
        } else if (nativeObject.equalsString(TABS_EXECUTE_SCRIPT)) {
            String erikwazhere="";
            return JSGlobal.evaluate(nativeObject, call, c);
        } else {
            DOMFunctions.expectParameters(nativeObject, call, c, 0, 20);

            //if callback exists, it will be executed
            executeCallback(call, s, c);

            Value callback = buildCallbackValue(call, s);
            //DOMEvents.addEventHandler(sm_listener, EventType.SEND_MESSAGE, c);
            if(nativeObject.toString().contains("addListener")){
                if (callback != null) {
                    if (callback.isMaybeUndef() || callback.isMaybeNull()) {
                        Exceptions.throwTypeError(c);
                    }
                    List<Value> eventArgs = new ArrayList<>();
                    if (call.getNumberOfArgs() == 2) {
                        eventArgs.add(FunctionCalls.readParameter(call, s, 0));
                    } else if (call.getNumberOfArgs() == 3) {
                        Value p0 = FunctionCalls.readParameter(call, s, 0);
                        // if 32 in length and no { then first param must be an extension id
                        if (p0.getStrSafely() != null && p0.getStrSafely().length() == 32 && !p0.getStrSafely().contains("{")) {
                            eventArgs.add(FunctionCalls.readParameter(call, s, 1));
                        } else {
                            eventArgs.add(p0);
                        }
                    } else if (call.getNumberOfArgs() == 4) {
                        eventArgs.add(FunctionCalls.readParameter(call, s, 1));
                    }
                    eventArgs.add(Value.makeJSONStr());
                    eventArgs.add(callback); //callback is last
                    DOMEvents.triggerEventHandler(EventType.SEND_MESSAGE, c, eventArgs);
                }
            }

            return Value.makeAnyStr();
            //throw new AnalysisException("Unsupported Native Object: " + nativeObject);
        }
    }

}

