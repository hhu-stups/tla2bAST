package de.tla2b.examples;

import java.io.File;

import de.tla2b.util.AbstractParseModuleTest;
import de.tla2b.util.PolySuite;
import de.tla2b.util.PolySuite.Config;
import de.tla2b.util.PolySuite.Configuration;
import de.tla2b.util.TestUtil;

import org.junit.Test;
import org.junit.runner.RunWith;

@RunWith(PolySuite.class)
public class RegressionTests extends AbstractParseModuleTest {
	private final File moduleFile;

	public RegressionTests(File machine, Object result) {
		this.moduleFile = machine;
	}

	@Test
	public void testRunTLC() throws Exception {
		TestUtil.loadTlaFile(moduleFile.getPath());
	}

	@Config
	public static Configuration getConfig() {
		return getConfiguration2("./src/test/resources/regression");
	}
}
