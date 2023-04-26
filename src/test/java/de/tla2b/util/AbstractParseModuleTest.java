package de.tla2b.util;

import java.io.File;
import java.util.ArrayList;
import java.util.Arrays;

import de.tla2b.util.PolySuite.Configuration;


public abstract class AbstractParseModuleTest {
	private static final String TLA_SUFFIX = ".tla";

	protected static File[] getModules(String path) {
		final File dir = new File(path);
		return dir.listFiles((d, name) -> name.endsWith(TLA_SUFFIX));
	}

	protected static File[] getModulesRecursively(String path) {
		return walk(path).toArray(new File[0]);
	}

	private static ArrayList<File> walk(String path) {
		File root = new File(path);
		File[] list = root.listFiles();
		
		ArrayList<File> files = new ArrayList<File>();
		if (list == null)
			return files;

		for (File f : list) {
			if (f.isDirectory()) {
				files.addAll(walk(f.getAbsolutePath()));
			} else if (f.getName().endsWith(TLA_SUFFIX)) {
				files.add(f);
			}
		}
		return files;
	}

	protected static Configuration getConfiguration2(String path) {
		final ArrayList<Object> expectedValues = new ArrayList<Object>();
		File[] modules = getModulesRecursively(path);
		final ArrayList<File> allModules = new ArrayList<File>(Arrays.asList(modules));
		for (int i = 0; i < modules.length; i++) {
			expectedValues.add(1);
		}

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
				return expectedValues.get(index);
			}
		};
	}


}
