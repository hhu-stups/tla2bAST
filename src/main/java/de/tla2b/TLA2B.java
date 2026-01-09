package de.tla2b;

import de.tla2b.exceptions.TLA2BFrontEndException;
import de.tla2b.exceptions.NotImplementedException;
import de.tla2b.exceptions.TLA2BException;
import de.tla2bAst.Translator;
import org.apache.commons.cli.*;
import de.tla2b.util.DebugUtils;

import static de.tla2b.global.TranslationGlobals.VERSION_NUMBER;

public class TLA2B {
	public final static String VERSION = "version";
	public final static String VERBOSE = "verbose";

	private String mainFile;

	public void handleParameter(String[] args) {
		DefaultParser parser = new DefaultParser();
		Options options = getCommandlineOptions();
		try {
			CommandLine line = parser.parse(options, args);
			String[] remainingArgs = line.getArgs();
			DebugUtils.setDebugMode(line.hasOption(VERBOSE));
			if (line.hasOption(VERSION)) {
				System.out.println("TLA2B version: " + VERSION_NUMBER);
			}
			if (remainingArgs.length != 1) {
				System.out.println("Error: expected a module file.");
				HelpFormatter formatter = new HelpFormatter();
				formatter.printHelp("java -jar TLA2B.jar [file]", options);
				System.exit(-1);
			} else {
				mainFile = remainingArgs[0];
			}
		} catch (ParseException e) {
			System.out.println(e.getMessage());
			HelpFormatter formatter = new HelpFormatter();
			formatter.printHelp("java -jar TLA2B.jar [file]", options);
			System.exit(-1);
		}

	}

	public static void main(String[] args) {
		// To indicate an error we use the exit code -1
		TLA2B tla2b = new TLA2B();
		tla2b.handleParameter(args);

		Translator translator = null;
		try {
			translator = new Translator(tla2b.mainFile);
		} catch (TLA2BFrontEndException e) {
			System.exit(-1);
		}
		try {
			translator.translate();
		} catch (NotImplementedException e) {
			System.err.print("**** Translation Error ****\n");
			System.err.print("Not implemented:\n");
			System.err.println(e.getMessage());
			System.exit(-1);
		} catch (TLA2BException e) {
			System.err.print("**** Translation Error ****\n");
			System.err.println(e.getMessage());
			//e.printStackTrace();
			System.exit(-1);
		}
		translator.createMachineFile();
		translator.createProbFile();
	}

	private static Options getCommandlineOptions() {
		Options options = new Options();
		options.addOption(VERSION, false, "prints the current version of TLA2B");
		options.addOption(VERBOSE, false, "makes output more verbose");

		Option config = Option.builder("config")
			.argName("file")
			.hasArg()
			.desc("config file")
			.build();
		options.addOption(config);
		return options;
	}
}
