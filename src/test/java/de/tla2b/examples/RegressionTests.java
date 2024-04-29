package de.tla2b.examples;

import de.tla2b.util.TestUtil;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;

import java.io.File;
import java.util.List;

@RunWith(Parameterized.class)
public class RegressionTests {
	private final File moduleFile;

	public RegressionTests(File machine) {
		this.moduleFile = machine;
	}

	@Parameterized.Parameters(name = "{0}")
	public static List<File> getConfig() {
		return TestUtil.getModulesRecursively("./src/test/resources/regression");
	}

	@Test
	public void testRunTLC() throws Exception {
		TestUtil.loadTlaFile(moduleFile.getPath());
	}
}
