package dk.brics.tajs.util;

import com.google.gson.Gson;
import com.google.gson.GsonBuilder;
import dk.brics.tajs.flowgraph.SourceLocation;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.Writer;
import java.net.URISyntaxException;
import java.net.URL;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

public class TotalsLog {

    static Set<URL> fileSet = new HashSet<>();
    static File sourceFile = null;
    static String searchFor ="";
    static Analysis analysis = new Analysis();

    public static void addFiles(URL file) throws URISyntaxException{
        fileSet.add(file);
        sourceFile = new File(file.toURI());
    }

    public static void addFiles(List<URL> files) throws URISyntaxException{
        sourceFile = new File(files.get(0).toURI());
        TotalsLog.fileSet.addAll(files);
    }

    private static String filesToString() {
        StringBuilder logSB = new StringBuilder("[");
        for (URL path : fileSet) {
            logSB.append(path.getPath()).append(",");
        }
        logSB.deleteCharAt(logSB.length() - 1);
        logSB.append("]");
        return logSB.toString();
    }

    public static String writeOutTotals() {
        StringBuffer outSB = new StringBuffer();
        try {
            outSB.append(filesToString());
            outSB.append(",");
            outSB.append(analysis.toString());
            outSB.append("\n");

            File f = new File("totals");
            Writer writer = new FileWriter(f.getAbsolutePath() + ".dat", true);
            writer.write(outSB.toString());
            writer.close();
        } catch (IOException ioe) {
            System.out.println(ioe);
            ioe.printStackTrace();
        }
        return outSB.toString();
    }

    public static void setAnalysisTotals(Integer analyzedFuncs, Integer partiallyAnalyzedFuncs, Integer totalFuncs,
                                         Integer analyzedBlocks, Integer totalBlocks) {
        analysis.analyzedFuncs = analyzedFuncs;
        analysis.partiallyAnalyzedFuncs = partiallyAnalyzedFuncs;
        analysis.unAnalyzedFuncs = totalFuncs - analyzedFuncs - partiallyAnalyzedFuncs;
        analysis.totalFuncs = totalFuncs;
        analysis.analyzedBlocks = analyzedBlocks;
        analysis.totalBlocks = totalBlocks;
        analysis.unAnalyzedBlocks = totalBlocks - analyzedBlocks;
    }

    public static void addSearchFor(String searchFor_in) {
        searchFor = searchFor_in;
    }

    private static class Analysis {

        String type = "Mod_Analyzed";

        Integer analyzedFuncs = 0, partiallyAnalyzedFuncs = 0, unAnalyzedFuncs = 0, totalFuncs = 0, analyzedBlocks = 0, unAnalyzedBlocks = 0, totalBlocks = 0;

        public String toString() {
            String outTots = "";
            outTots += type + "," + analyzedFuncs + "," + partiallyAnalyzedFuncs + "," + unAnalyzedFuncs + "," + totalFuncs + ",";
            outTots += analyzedBlocks + "," + unAnalyzedBlocks + "," + totalBlocks;
            return outTots;
        }
    }

    private static class ResultsInfo {

        Map<String, List<SourceLocation>> matches = null;

        List<String> files = new ArrayList<String>();

        Analysis analysis = TotalsLog.analysis;
        String searchFor = TotalsLog.searchFor;
        String message = "";
        public ResultsInfo(String message_in) {
            message = message_in;
        }
        public ResultsInfo(Map<String, List<SourceLocation>> matches) {
            this.matches = matches;
            for (URL path : TotalsLog.fileSet) {
                files.add(path.getPath().toString());
            }
        }
    }
    public static void report(String errorMessage) {
        ResultsInfo resultsInfo = new ResultsInfo(errorMessage);
        writeReport(resultsInfo);
    }

    public static void report(Map<String, List<SourceLocation>> all) {
        ResultsInfo resultsInfo = new ResultsInfo(all);
        writeReport(resultsInfo);
    }
    private static void writeReport(ResultsInfo resultsInfo){
        try {

            Writer writer = new FileWriter(sourceFile.getAbsolutePath() + ".json");
            Gson gson = new GsonBuilder().create();
            String json = gson.toJson(resultsInfo, resultsInfo.getClass());
            writer.write(json);
            writer.close();
            Gson gsonPP = new GsonBuilder().setPrettyPrinting().create();
            System.out.println(gsonPP.toJson(resultsInfo, resultsInfo.getClass()));
            System.out.println("JSON written out to " + sourceFile.getAbsolutePath() + ".json");
        } catch (IOException ioe) {
            ioe.printStackTrace();
        }
    }
}
