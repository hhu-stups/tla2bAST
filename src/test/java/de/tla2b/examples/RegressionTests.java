package de.tla2b.examples;

import static de.tla2b.util.TestUtil.load_TLA_File;

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
		load_TLA_File(moduleFile.getPath());
	}

	@Config
	public static Configuration getConfig() {
		final ArrayList<String> list = new ArrayList<String>();
		final ArrayList<String> ignoreList = new ArrayList<String>();
		list.add("./src/test/resources/regression"); 
		return getConfiguration2(list, ignoreList);
	}
}
