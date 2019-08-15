package dk.brics.tajs.util;

public class Colorize {
    private static final String BOLD_RED = "\033[1;31m";

    private static final String BOLD_GREEN = "\033[1;32m";
    private static final String NONE = "\033[0m\033[49m";

    public static String green(String input){
        return BOLD_GREEN + input + NONE;
    }
    public static String red(String input){
        return BOLD_RED + input + NONE;
    }

}
