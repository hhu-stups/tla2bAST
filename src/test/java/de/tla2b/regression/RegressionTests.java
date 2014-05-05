package de.tla2b.regression;

import static de.tla2b.util.TestUtil.runModule;

import java.io.File;
import java.util.ArrayList;

import org.junit.Test;
import org.junit.runner.RunWith;

import de.tla2b.util.AbstractParseModuleTest;
import de.tla2b.util.PolySuite;
import de.tla2b.util.PolySuite.Config;
import de.tla2b.util.PolySuite.Configuration;

@RunWith(PolySuite.class)
public class RegressionTests extends AbstractParseModuleTest{
	private final File moduleFile;

	public RegressionTests(File machine, Object result) {
		this.moduleFile = machine;
	}

	@Test
	public void testRunTLC() throws Exception {
		//String[] a = new String[] { moduleFile.getPath() };
		System.out.println(moduleFile.getPath());
		runModule(moduleFile.getPath());
	}

	@Config
	public static Configuration getConfig() {
		final ArrayList<String> list = new ArrayList<String>();
		final ArrayList<String> ignoreList = new ArrayList<String>();
		
		list.add("./src/test/resources/examples"); 
		ignoreList.add("./src/test/resources/testing/");
		return getConfiguration2(list, ignoreList);
	}
}
