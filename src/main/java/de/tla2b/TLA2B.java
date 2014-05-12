/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package de.tla2b;


import de.tla2b.exceptions.FrontEndException;
import de.tla2b.exceptions.NotImplementedException;
import de.tla2b.exceptions.TLA2BException;
import de.tla2b.global.TranslationGlobals;
import de.tla2bAst.Translator;

public class TLA2B implements TranslationGlobals {
	private String mainFile;

	private static boolean error = false;

	public static boolean hasError() {
		return error;
	}

	public void handleParameter(String[] args) {
		int i;
		for (i = 0; (i < args.length) && (args[i].charAt(0) == '-'); i++) {
			if (args[i].equals("-version")) {
				System.out.println("TLA2B version " + VERSION);
				System.exit(-1);
			} else {
				System.err.println("Illegal switch: " + args[i]);
				System.exit(-1);
			}
		}

		if (i == args.length) {
			System.err.println("Error: expected a module file.");
			System.exit(-1);
		}
		mainFile = args[i];
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
			System.exit(-1);
		}
		//translator.createMachineFile();
		translator.createProbFile();
	}


}
