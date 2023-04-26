package de.tla2b.examples;

import java.io.File;
import java.util.List;

import de.tla2b.util.AbstractParseModuleTest;
import de.tla2b.util.TestUtil;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;

@RunWith(Parameterized.class)
public class RegressionTests extends AbstractParseModuleTest {
	private final File moduleFile;

	public RegressionTests(File machine) {
		this.moduleFile = machine;
	}

	@Test
	public void testRunTLC() throws Exception {
		TestUtil.loadTlaFile(moduleFile.getPath());
	}

	@Parameterized.Parameters(name = "{0}")
	public static List<File> getConfig() {
		return getModulesRecursively("./src/test/resources/regression");
	}
}
