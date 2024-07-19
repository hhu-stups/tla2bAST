package de.tla2b.util;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.IOException;

public class FileUtils {

	public static String removeExtension(String filePath) {
		File f = new File(filePath);

		// if it's a directory, don't remove the extension
		if (f.isDirectory())
			return filePath;

		String name = f.getName();

		// Now we know it's a file - don't need to do any special hidden
		// checking or contains() checking because of:
		final int lastPeriodPos = name.lastIndexOf('.');
		if (lastPeriodPos <= 0) {
			// No period after first character - return name as it was passed in
			return filePath;
		} else {
			// Remove the last period and everything after it
			File renamed = new File(f.getParent(), name.substring(0,
				lastPeriodPos));
			return renamed.getPath();
		}
	}

	public static String fileToString(String fileName) throws IOException {
		StringBuilder res = new StringBuilder();
		BufferedReader in = new BufferedReader(new FileReader(fileName));
		String str;
		while ((str = in.readLine()) != null) {
			res.append(str).append("\n");
		}
		in.close();
		return res.toString();
	}


}
