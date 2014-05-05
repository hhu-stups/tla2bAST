package de.tla2b.util;

import java.io.File;
import java.io.FilenameFilter;
import java.io.IOException;
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

	protected static File[] getModulesRecursively(String path, ArrayList<String> ignoreList) {
		File[] files = walk(path, ignoreList).toArray(new File[0]);
		return files;
	}

	private static ArrayList<File> walk(String path, ArrayList<String> ignoreList) {
		File root = new File(path);
		File[] list = root.listFiles();
		
		ArrayList<File> files = new ArrayList<File>();
		if (list == null)
			return files;

		for (File f : list) {
			if (f.isDirectory()) {
				boolean visitDir = true;
				for (String string : ignoreList) {
					File ignore = new File(string);
					try {
						if(f.getCanonicalPath().equals(ignore.getCanonicalPath())){
							visitDir = false;
						}
					} catch (IOException e) {
						visitDir = false;
					}
				}
				if(visitDir){
					files.addAll(walk(f.getAbsolutePath(),ignoreList));
				}
				
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

	protected static Configuration getConfiguration2(ArrayList<String> list, ArrayList<String> ignoreList) {
		final ArrayList<File> allModules = new ArrayList<File>();

		final ArrayList<Object> expectedValues = new ArrayList<Object>();
		for (String path : list) {
			File[] modules = getModulesRecursively(path, ignoreList);
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