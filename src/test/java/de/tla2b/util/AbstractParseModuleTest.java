package de.tla2b.util;

import java.io.File;
import java.util.ArrayList;

public abstract class AbstractParseModuleTest {
	private static final String TLA_SUFFIX = ".tla";

	protected static ArrayList<File> getModulesRecursively(String path) {
		File root = new File(path);
		File[] list = root.listFiles();
		
		ArrayList<File> files = new ArrayList<File>();
		if (list == null)
			return files;

		for (File f : list) {
			if (f.isDirectory()) {
				files.addAll(getModulesRecursively(f.getAbsolutePath()));
			} else if (f.getName().endsWith(TLA_SUFFIX)) {
				files.add(f);
			}
		}
		return files;
	}
}
