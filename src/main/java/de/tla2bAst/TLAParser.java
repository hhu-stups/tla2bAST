package de.tla2bAst;

import tla2sany.drivers.FrontEndException;
import tla2sany.drivers.SANY;
import tla2sany.modanalyzer.SpecObj;
import tla2sany.semantic.ModuleNode;
import util.FilenameToStream;
import util.ToolIO;

public class TLAParser {

	private FilenameToStream filenameToStream;
	
	public TLAParser(FilenameToStream filenameToStream) {
		this.filenameToStream = filenameToStream;
	}
	
	public  ModuleNode parseModule(String moduleName) throws de.tla2b.exceptions.FrontEndException {
		SpecObj spec = new SpecObj(moduleName, filenameToStream);
		try {
			SANY.frontEndMain(spec, moduleName, ToolIO.out);
		} catch (FrontEndException e) {
			// Error in Frontend, should never happens
			return null;
		}

		if (spec.parseErrors.isFailure()) {
			throw new de.tla2b.exceptions.FrontEndException(
					allMessagesToString(ToolIO.getAllMessages())
							+ spec.parseErrors, spec);
		}

		if (spec.semanticErrors.isFailure()) {
			throw new de.tla2b.exceptions.FrontEndException(
			// allMessagesToString(ToolIO.getAllMessages())
					"" + spec.semanticErrors, spec);
		}

		// RootModule
		ModuleNode n = spec.getExternalModuleTable().rootModule;
		if (spec.getInitErrors().isFailure()) {
			System.err.println(spec.getInitErrors());
			return null;
		}

		if (n == null) { // Parse Error
			// System.out.println("Rootmodule null");
			throw new de.tla2b.exceptions.FrontEndException(
					allMessagesToString(ToolIO.getAllMessages()), spec);
		}

		return n;
	}
	
	public static String allMessagesToString(String[] allMessages) {
		StringBuilder sb = new StringBuilder();
		for (int i = 0; i < allMessages.length - 1; i++) {
			sb.append(allMessages[i] + "\n");
		}
		return sb.toString();
	}
}
