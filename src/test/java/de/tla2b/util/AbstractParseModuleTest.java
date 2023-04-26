package de.tla2b.util;

import java.io.File;
import java.util.ArrayList;

import de.tla2b.util.PolySuite.Configuration;


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

	protected static Configuration getConfiguration2(String path) {
		final ArrayList<File> allModules = getModulesRecursively(path);

		return new Configuration() {
			public int size() {
				return allModules.size();
			}

			public File getTestValue(int index) {
				return allModules.get(index);
			}

			public String getTestName(int index) {
				return allModules.get(index).getName();
			}

			public Object getExpectedValue(int index) {
				return 1;
			}
		};
	}


}
