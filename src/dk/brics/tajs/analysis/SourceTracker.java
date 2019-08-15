package dk.brics.tajs.analysis;

import dk.brics.tajs.flowgraph.AbstractNode;
import dk.brics.tajs.flowgraph.SourceLocation;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.nio.charset.Charset;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Scanner;
import java.util.Set;

public class SourceTracker {

    // purpose:
    //     how many lines processed
    //     search for contents of nodes
    // each psudo code line is on one or more sourcelocations,
    // key is sourceLocation and psuedo code

    Map<SourceLocation, SourceTrackerItem> parsedLines = new HashMap<>();
    Set<String> fileNames = new HashSet<>();
    public SourceTracker() {
    }

    public void add(AbstractNode node) {
        SourceLocation sl = node.getSourceLocation();
        fileNames.add(sl.toUserFriendlyString(false));
        if (parsedLines.containsKey(sl)) {
            parsedLines.get(sl).add(node);
        } else {
            parsedLines.put(sl, new SourceTrackerItem(node));
        }
    }

    public void analyzeLinesParsed() {
        for (String fn : fileNames){
            String output = analyzeLinesParsed(fn);
            System.out.println( "Line Analysis for " + fn);
            System.out.println(output);
        }
    }

    public String analyzeLinesParsed(String fileName) {
        return analyzeLinesParsed(fileName, "\t","\n");
    }
    private String filterString(String code) {
        String partialFiltered = code.replaceAll("/\\*.*\\*/", "");
        String fullFiltered = partialFiltered.replaceAll("//.*(?=\\n)", "");
        return fullFiltered;
    }


    enum State { outsideComment, insideLineComment, insideblockComment, insideblockComment_noNewLineYet, insideString }

    public static String removeComments(String code) {
        State state = State.outsideComment;
        StringBuilder result = new StringBuilder();
        Scanner s = new Scanner(code);
        s.useDelimiter("");
        while (s.hasNext()) {
            String c = s.next();
            switch (state) {
                case outsideComment:
                    if (c.equals("/") && s.hasNext()) {
                        String c2 = s.next();
                        if (c2.equals("/"))
                            state = State.insideLineComment;
                        else if (c2.equals("*")) {
                            state = State.insideblockComment_noNewLineYet;
                        } else {
                            result.append(c).append(c2);
                        }
                    } else {
                        result.append(c);
                        if (c.equals("\"")) {
                            state = State.insideString;
                        }
                    }
                    break;
                case insideString:
                    result.append(c);
                    if (c.equals("\"")) {
                        state = State.outsideComment;
                    } else if (c.equals("\\") && s.hasNext()) {
                        result.append(s.next());
                    }
                    break;
                case insideLineComment:
                    if (c.equals("\n")) {
                        state = State.outsideComment;
                        result.append("\n");
                    }
                    break;
                case insideblockComment_noNewLineYet:
                    if (c.equals("\n")) {
                        result.append("\n");
                        state = State.insideblockComment;
                    }
                case insideblockComment:
                    while (c.equals("*") && s.hasNext()) {
                        String c2 = s.next();
                        if (c2.equals("/")) {
                            state = State.outsideComment;
                            break;
                        }
                    }
            }
        }
        s.close();
        return result.toString();
    }

    static String readFile(String path, Charset encoding) throws IOException {
        byte[] encoded = Files.readAllBytes(Paths.get(path));
        return new String(encoded, encoding);
    }


    public String analyzeLinesParsed(String fileName, String prepend, String postpend) {
        StringBuffer outSB = new StringBuffer();
        try {
            String line = "";
            File f = new File(fileName);
            if (fileName.substring(fileName.lastIndexOf(".") + 1).equals("js")){
                String code = readFile(fileName, Charset.defaultCharset());

                code = removeComments(code);

                String codeList[] = code.split("\n");

                for (int codePtr=0; codePtr < codeList.length; codePtr++){
                    int lineNumber = codePtr +1;
                    line = codeList[codePtr];
                    line.trim();
                    line.replace("\t","t");
                    if (line.length() > 2){
                        boolean found = false;
                        for (Map.Entry<SourceLocation, SourceTrackerItem> ent : parsedLines.entrySet()){

                            SourceLocation sl = ent.getKey();
                            if (sl.getLineNumber() <= lineNumber && lineNumber <= sl.getEndLineNumber() && sl.toUserFriendlyString(false).equals(fileName)){
                                found = true;
                            }

                        }
                        if (!found) {
                            outSB.append(prepend);
                            outSB.append(lineNumber);
                            outSB.append("  ");
                            outSB.append(line);
                            outSB.append(postpend);
                        }
                    }

                }
            }



        } catch (FileNotFoundException ex) {
            System.out.println("Unable to open file '" + fileName + "'");
        } catch (IOException ex) {
            System.out.println("Error reading file '" + fileName + "'");
        }

        return outSB.toString();
    }
}
