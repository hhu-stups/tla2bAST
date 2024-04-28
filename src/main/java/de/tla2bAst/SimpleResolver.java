package de.tla2bAst;

import util.FilenameToStream;

import java.io.File;

public class SimpleResolver implements FilenameToStream {

	private File file;

	public boolean isStandardModule(String arg0) {
		return false;
	}

	public File resolve(String arg0, boolean arg1) {

		file = new File(arg0);
		return file;
	}

	public String getFullPath() {
		return file.getAbsolutePath();
	}

}
