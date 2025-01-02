package de.tla2b.examples;

import org.junit.Ignore;
import org.junit.Test;

import static de.tla2b.util.TestUtil.runModule;

public class InstanceTest {

	@Test
	public void testInstanceNoName() throws Exception {
		String file = "src/test/resources/examples/instance/Counter/InstanceNoName.tla";
		runModule(file);
	}

	@Test
	public void testConstantSubstitution1() throws Exception {
		String file = "src/test/resources/examples/instance/constantSubstitution/InstanceOpArg3.tla";
		runModule(file);
	}

	@Test
	public void testConstantSubstitution2() throws Exception {
		String file = "src/test/resources/examples/instance/constantSubstitution/InstanceValue2.tla";
		runModule(file);
	}

	@Test
	public void testModConstantAssignment() throws Exception {
		String file = "src/test/resources/examples/instance/Counter/ModConstantAssignment.tla";
		runModule(file);
	}

	@Test
	public void testOneInstanced() throws Exception {
		String file = "src/test/resources/examples/instance/Counter/OneInstanced.tla";
		runModule(file);
	}

	@Test
	public void testTwoInstanced() throws Exception {
		String file = "src/test/resources/examples/instance/Counter/TwoInstanced.tla";
		runModule(file);
	}

	@Test
	public void testLetInstanced() throws Exception {
		String file = "src/test/resources/examples/instance/let/InstanceLet.tla";
		runModule(file);
	}

	@Test
	public void testOpArgInstanced() throws Exception {
		String file = "src/test/resources/examples/instance/OpArg/OpArgInstanced.tla";
		runModule(file);
	}

	@Ignore
	@Test
	public void testSimpleTwoInstanced() throws Exception {
		// TODO: implement in Typechecker
		String file = "src/test/resources/examples/instance/twoInstanced/first.tla";
		runModule(file);
	}
}
