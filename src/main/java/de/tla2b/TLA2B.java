/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package de.tla2b;

import org.apache.commons.cli.CommandLine;
import org.apache.commons.cli.HelpFormatter;
import org.apache.commons.cli.Option;
import org.apache.commons.cli.OptionBuilder;
import org.apache.commons.cli.Options;
import org.apache.commons.cli.ParseException;
import org.apache.commons.cli.PosixParser;

import de.tla2b.exceptions.FrontEndException;
import de.tla2b.exceptions.NotImplementedException;
import de.tla2b.exceptions.TLA2BException;
import de.tla2b.global.TranslationGlobals;
import de.tla2bAst.Translator;



public class TLA2B implements TranslationGlobals {
	public final static String VERSION = "version";

	private String mainFile;

	private static boolean error = false;

	public static boolean hasError() {
		return error;
	}

	public void handleParameter(String[] args) {
		PosixParser parser = new PosixParser();
		Options options = getCommandlineOptions();
		try {
			CommandLine line = parser.parse(options, args);
			String[] remainingArgs = line.getArgs();
			if (remainingArgs.length != 1) {
				System.err.println("Error: expected a module file.");
				System.exit(-1);
			} else {
				mainFile = remainingArgs[0];
			}
			if (line.hasOption(VERSION)) {
				System.out.println("TLA2B version: " + VERSION_NUMBER);
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
		} catch (FrontEndException e) {
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

	@SuppressWarnings("static-access")
	private static Options getCommandlineOptions() {
		Options options = new Options();
		options.addOption(VERSION, false, "prints the current version of TLA2B");
		
		Option config = OptionBuilder
				.withArgName("file")
				.hasArg()
				.withDescription(
						"config file")
						.create("config");
		options.addOption(config);
		return options;
	}
}
