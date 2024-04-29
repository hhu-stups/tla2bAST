package de.tla2b.examples;

import org.junit.Ignore;
import org.junit.Test;

import static de.tla2b.util.TestUtil.runModule;

public class MCTest {

	@Test
	public void testSimpleMC() throws Exception {
		String file = "src/test/resources/MCTests/simple/MC.tla";
		runModule(file);
	}

	@Test
	public void testInvariantMC() throws Exception {
		String file = "src/test/resources/MCTests/Invariant/MC.tla";
		runModule(file);
	}

	@Test
	public void testConstantSetupMC() throws Exception {
		String file = "src/test/resources/MCTests/constantsetup/MC.tla";
		runModule(file);
	}

	@Test
	public void testModelValuesMC() throws Exception {
		String file = "src/test/resources/MCTests/modelvalues/MC.tla";
		runModule(file);
	}

	@Test
	public void testDieHardMC() throws Exception {
		String file = "src/test/resources/MCTests/DieHard/MC.tla";
		runModule(file);
	}

	@Test
	public void testSimpleAllocatorMC() throws Exception {
		String file = "src/test/resources/MCTests/SimpleAllocator/MC.tla";
		runModule(file);
	}

	@Test
	public void testMCDieHarder() throws Exception {
		String file = "src/test/resources/MCTests/MCDieHarder/MCDieHarder.tla";
		runModule(file);
	}

	@Test
	public void testDieHarder() throws Exception {
		String file = "src/test/resources/MCTests/DieHarder/MC.tla";
		runModule(file);
	}


	@Ignore
	@Test
	public void testCarTalkPuzzle() throws Exception {
		String file = "src/test/resources/MCTests/CarTalkPuzzle/MC.tla";
		runModule(file);
	}

	@Ignore
	@Test
	public void testCarTalkPuzzleModel2() throws Exception {
		String file = "src/test/resources/MCTests/CarTalkPuzzle/Model2/MC.tla";
		runModule(file);
	}

	@Ignore
	@Test
	public void testRecursiveFunction() throws Exception {
		String file = "src/test/resources/examples/RecursiveFunction/RecursiveFunction.tla";
		runModule(file);
	}

	@Test
	public void testQueens() throws Exception {
		String file = "src/test/resources/MCTests/Queens/MC.tla";
		runModule(file);
	}

	@Test
	public void testMacroTest() throws Exception {
		String file = "src/test/resources/renamer/MacroTest/MacroTest.tla";
		runModule(file);
	}

}
