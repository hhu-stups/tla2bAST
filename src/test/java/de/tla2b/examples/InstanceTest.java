package de.tla2b.examples;

import static de.tla2b.util.TestUtil.runModule;

import org.junit.Ignore;
import org.junit.Test;

public class InstanceTest {

	
	@Test
	public void testInstanceNoName() throws Exception {
		String file = "src/test/resources/examples/instance/Counter/InstanceNoName.tla";
		runModule(file);
	}
	
	@Ignore
	@Test
	public void testInstance() throws Exception {
		String file = "src/test/resources/examples/instance/Counter/OneInstanced.tla";
		runModule(file);
	}
}
