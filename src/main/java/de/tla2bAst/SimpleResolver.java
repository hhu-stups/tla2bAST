package de.tla2bAst;

import java.io.File;

import util.FilenameToStream;

public class SimpleResolver implements FilenameToStream {

	public boolean isStandardModule(String arg0) {
		return false;
	}

	public File resolve(String arg0, boolean arg1) {

		File file = new File(arg0);
		return file;
	}

}