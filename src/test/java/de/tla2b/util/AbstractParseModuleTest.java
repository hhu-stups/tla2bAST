package de.tla2b.util;

import java.io.File;
import java.io.FilenameFilter;
import java.util.ArrayList;
import java.util.Arrays;

import de.tla2b.util.PolySuite.Configuration;


public abstract class AbstractParseModuleTest {
	private static final String[] SUFFIX = { ".tla" };
	
	private static final class ModuleFilenameFilter implements FilenameFilter {
	

		public boolean accept(final File dir, final String name) {
			for (int i = 0; i < SUFFIX.length; i++) {
				if (name.endsWith(SUFFIX[i])) {
					return true;
				}
			}
			return false;
		}
	}

	protected static File[] getModules(String path) {
		final File dir = new File(path);
		return dir.listFiles(new ModuleFilenameFilter());
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
				
			} else {
				String name =f.getName();
					for (int i = 0; i < SUFFIX.length; i++) {
						if (name.endsWith(SUFFIX[i])) {
							files.add(f);
						}
					}
			}
		}
		return files;
	}

	protected static Configuration getConfiguration2(ArrayList<String> list) {
		final ArrayList<File> allModules = new ArrayList<File>();

		final ArrayList<Object> expectedValues = new ArrayList<Object>();
		for (String path : list) {
			File[] modules = getModulesRecursively(path);
			allModules.addAll(Arrays.asList(modules));
			for (int i = 0; i < modules.length; i++) {
				expectedValues.add(1);
			}
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
