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

package dk.brics.tajs.analysis.dom.chrome;

import dk.brics.tajs.analysis.FunctionCalls.CallInfo;
import dk.brics.tajs.analysis.Solver;
import dk.brics.tajs.analysis.dom.ChromeAPI;
import dk.brics.tajs.analysis.dom.DOMBuilder;
import dk.brics.tajs.analysis.dom.DOMObjects;
import dk.brics.tajs.analysis.dom.DOMRegistry;
import dk.brics.tajs.analysis.dom.DOMWindow;
import dk.brics.tajs.analysis.dom.DynamicDOMObject;
import dk.brics.tajs.analysis.dom.ajax.ActiveXObject;
import dk.brics.tajs.analysis.dom.ajax.XmlHttpRequest;
import dk.brics.tajs.analysis.dom.core.DOMCharacterData;
import dk.brics.tajs.analysis.dom.core.DOMConfiguration;
import dk.brics.tajs.analysis.dom.core.DOMDocument;
import dk.brics.tajs.analysis.dom.core.DOMDocumentType;
import dk.brics.tajs.analysis.dom.core.DOMElement;
import dk.brics.tajs.analysis.dom.core.DOMImplementation;
import dk.brics.tajs.analysis.dom.core.DOMNamedNodeMap;
import dk.brics.tajs.analysis.dom.core.DOMNode;
import dk.brics.tajs.analysis.dom.core.DOMNodeList;
import dk.brics.tajs.analysis.dom.core.DOMStringList;
import dk.brics.tajs.analysis.dom.core.DOMText;
import dk.brics.tajs.analysis.dom.core.DOMTokenList;
import dk.brics.tajs.analysis.dom.event.CustomEvent;
import dk.brics.tajs.analysis.dom.event.DocumentEvent;
import dk.brics.tajs.analysis.dom.event.Event;
import dk.brics.tajs.analysis.dom.event.EventListener;
import dk.brics.tajs.analysis.dom.event.EventTarget;
import dk.brics.tajs.analysis.dom.event.KeyboardEvent;
import dk.brics.tajs.analysis.dom.event.MouseEvent;
import dk.brics.tajs.analysis.dom.event.MutationEvent;
import dk.brics.tajs.analysis.dom.event.UIEvent;
import dk.brics.tajs.analysis.dom.event.WheelEvent;
import dk.brics.tajs.analysis.dom.html.HTMLAnchorElement;
import dk.brics.tajs.analysis.dom.html.HTMLAppletElement;
import dk.brics.tajs.analysis.dom.html.HTMLAreaElement;
import dk.brics.tajs.analysis.dom.html.HTMLBRElement;
import dk.brics.tajs.analysis.dom.html.HTMLBaseElement;
import dk.brics.tajs.analysis.dom.html.HTMLBaseFontElement;
import dk.brics.tajs.analysis.dom.html.HTMLBodyElement;
import dk.brics.tajs.analysis.dom.html.HTMLButtonElement;
import dk.brics.tajs.analysis.dom.html.HTMLCollection;
import dk.brics.tajs.analysis.dom.html.HTMLDListElement;
import dk.brics.tajs.analysis.dom.html.HTMLDirectoryElement;
import dk.brics.tajs.analysis.dom.html.HTMLDivElement;
import dk.brics.tajs.analysis.dom.html.HTMLDocument;
import dk.brics.tajs.analysis.dom.html.HTMLElement;
import dk.brics.tajs.analysis.dom.html.HTMLFieldSetElement;
import dk.brics.tajs.analysis.dom.html.HTMLFontElement;
import dk.brics.tajs.analysis.dom.html.HTMLFormElement;
import dk.brics.tajs.analysis.dom.html.HTMLFrameElement;
import dk.brics.tajs.analysis.dom.html.HTMLFrameSetElement;
import dk.brics.tajs.analysis.dom.html.HTMLHRElement;
import dk.brics.tajs.analysis.dom.html.HTMLHeadElement;
import dk.brics.tajs.analysis.dom.html.HTMLHeadingElement;
import dk.brics.tajs.analysis.dom.html.HTMLHtmlElement;
import dk.brics.tajs.analysis.dom.html.HTMLIFrameElement;
import dk.brics.tajs.analysis.dom.html.HTMLImageElement;
import dk.brics.tajs.analysis.dom.html.HTMLInputElement;
import dk.brics.tajs.analysis.dom.html.HTMLIsIndexElement;
import dk.brics.tajs.analysis.dom.html.HTMLLIElement;
import dk.brics.tajs.analysis.dom.html.HTMLLabelElement;
import dk.brics.tajs.analysis.dom.html.HTMLLegendElement;
import dk.brics.tajs.analysis.dom.html.HTMLLinkElement;
import dk.brics.tajs.analysis.dom.html.HTMLMapElement;
import dk.brics.tajs.analysis.dom.html.HTMLMenuElement;
import dk.brics.tajs.analysis.dom.html.HTMLMetaElement;
import dk.brics.tajs.analysis.dom.html.HTMLModElement;
import dk.brics.tajs.analysis.dom.html.HTMLOListElement;
import dk.brics.tajs.analysis.dom.html.HTMLObjectElement;
import dk.brics.tajs.analysis.dom.html.HTMLOptGroupElement;
import dk.brics.tajs.analysis.dom.html.HTMLOptionElement;
import dk.brics.tajs.analysis.dom.html.HTMLOptionsCollection;
import dk.brics.tajs.analysis.dom.html.HTMLParagraphElement;
import dk.brics.tajs.analysis.dom.html.HTMLParamElement;
import dk.brics.tajs.analysis.dom.html.HTMLPreElement;
import dk.brics.tajs.analysis.dom.html.HTMLQuoteElement;
import dk.brics.tajs.analysis.dom.html.HTMLScriptElement;
import dk.brics.tajs.analysis.dom.html.HTMLSelectElement;
import dk.brics.tajs.analysis.dom.html.HTMLStyleElement;
import dk.brics.tajs.analysis.dom.html.HTMLTableCaptionElement;
import dk.brics.tajs.analysis.dom.html.HTMLTableCellElement;
import dk.brics.tajs.analysis.dom.html.HTMLTableColElement;
import dk.brics.tajs.analysis.dom.html.HTMLTableElement;
import dk.brics.tajs.analysis.dom.html.HTMLTableRowElement;
import dk.brics.tajs.analysis.dom.html.HTMLTableSectionElement;
import dk.brics.tajs.analysis.dom.html.HTMLTextAreaElement;
import dk.brics.tajs.analysis.dom.html.HTMLTitleElement;
import dk.brics.tajs.analysis.dom.html.HTMLUListElement;
import dk.brics.tajs.analysis.dom.html.HTMLUnknownElement;
import dk.brics.tajs.analysis.dom.html5.AudioContext;
import dk.brics.tajs.analysis.dom.html5.AudioDestinationNode;
import dk.brics.tajs.analysis.dom.html5.AudioNode;
import dk.brics.tajs.analysis.dom.html5.AudioParam;
import dk.brics.tajs.analysis.dom.html5.CanvasRenderingContext2D;
import dk.brics.tajs.analysis.dom.html5.HTMLAudioElement;
import dk.brics.tajs.analysis.dom.html5.HTMLCanvasElement;
import dk.brics.tajs.analysis.dom.html5.HTMLMediaElement;
import dk.brics.tajs.analysis.dom.html5.MutationObserver;
import dk.brics.tajs.analysis.dom.html5.OscillatorNode;
import dk.brics.tajs.analysis.dom.html5.ScriptProcessorNode;
import dk.brics.tajs.analysis.dom.html5.StorageElement;
import dk.brics.tajs.analysis.dom.html5.TimeRanges;
import dk.brics.tajs.analysis.dom.html5.WebGLRenderingContext;
import dk.brics.tajs.analysis.dom.style.CSSStyleDeclaration;
import dk.brics.tajs.lattice.HostObject;
import dk.brics.tajs.lattice.ObjectLabel;
import dk.brics.tajs.lattice.State;
import dk.brics.tajs.lattice.Str;
import dk.brics.tajs.lattice.UnknownValueResolver;
import dk.brics.tajs.lattice.Value;
import dk.brics.tajs.solver.Message.Severity;
import dk.brics.tajs.util.AnalysisException;
import dk.brics.tajs.util.Collections;
import org.apache.log4j.Logger;

import static dk.brics.tajs.analysis.InitialStateBuilder.FUNCTION_PROTOTYPE;
import static dk.brics.tajs.analysis.InitialStateBuilder.createPrimitiveFunction;

/**
 * Dispatcher and utility functions for the DOM support
 */
public class CEXFunctions {

    private static Logger log = Logger.getLogger(CEXFunctions.class);

    /*

     */

    /**
     * Read Magic Property
     */
    @SuppressWarnings("unused")
    public static void evaluateGetter(HostObject nativeObject, ObjectLabel label, String property, Solver.SolverInterface c) {
        throw new AnalysisException("Not Implemented");
    }

    /**
     * Create a new DOM property with the given name and value on the specified objectlabel.
     */
    public static void createDOMProperty(ObjectLabel label, String property, Value v, Solver.SolverInterface c) {
        c.getAnalysis().getPropVarOperations().writePropertyWithAttributes(label, property, v.setAttributes(v.isDontEnum(), v.isDontDelete(), v.isReadOnly()));
    }

    /**
     * Create a new DOM function with the given name and number of arguments on
     * the specified objectlabel.
     */
    public static void createDOMFunction(ObjectLabel label, HostObject nativeObject, String name, int args, Solver.SolverInterface c) {
        createPrimitiveFunction(label, FUNCTION_PROTOTYPE, nativeObject, name, args, c);
    }


    public static Value evaluate(DynamicDOMObject nativeObject, CallInfo call, Solver.SolverInterface c) {
        //c.getMonitoring().addMessage(call.getSourceNode(), Severity.HIGH, "TypeError, call to non-function (CEX): " + nativeObject);
        return ChromeAPI.evaluate(nativeObject, call, c);
        //return Value.makeAnyStr();
    }

    /**
     * Issues a warning if the number of parameters is not in the given interval. max is ignored if -1.
     */
    public static void expectParameters(HostObject hostobject, CallInfo call, Solver.SolverInterface c, int min, int max) {
        c.getMonitoring().visitNativeFunctionCall(call.getSourceNode(), hostobject, call.isUnknownNumberOfArgs(), call.isUnknownNumberOfArgs() ? -1 : call.getNumberOfArgs(), min, max);
        // TODO: implementations *may* throw TypeError if too many parameters to functions (p.76)
    }
}
