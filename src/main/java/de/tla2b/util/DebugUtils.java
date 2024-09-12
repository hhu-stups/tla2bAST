package de.tla2b.util;

public class DebugUtils {
    private static boolean debugOn;
    
	public static void setDebugMode(boolean newDebugOn) {
		debugOn = newDebugOn;
	}

	public static void printDebugMsg(String Msg) {
		if(debugOn) {
		   System.out.println(Msg);
		}
	}

	public static void printMsg(String Msg) {
	    // TODO: turn off using silent flag
		System.out.println(Msg);
	}

}
