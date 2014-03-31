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
	
	public  ModuleNode parseModule(String moduleName) {
		SpecObj spec = new SpecObj(moduleName, filenameToStream);
		try {
			SANY.frontEndMain(spec, moduleName, ToolIO.out);
		} catch (FrontEndException e) {
			// Error in Frontend, should never happens
			return null;
		}

		if (spec.parseErrors.isFailure()) {
		}

		if (spec.semanticErrors.isFailure()) {
		}

		// RootModule
		ModuleNode n = spec.getExternalModuleTable().rootModule;
		if (spec.getInitErrors().isFailure()) {
			System.err.println(spec.getInitErrors());
			return null;
		}

		if (n == null) { // Parse Error
		}
		return n;
	}
}
