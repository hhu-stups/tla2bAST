package de.tla2b.examples;

import org.junit.Ignore;
import org.junit.Test;

import static de.tla2b.util.TestUtil.runModule;

public class MCTest {

	@Test
	public void testClub() throws Exception {
		String file = "src/test/resources/examples/Club/Club.tla";
		runModule(file);
	}

	@Test
	public void testSimpleMC() throws Exception {
		String file = "src/test/resources/MCTests/simple/MC.tla";
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
	
	
	@Test
	public void testChannel() throws Exception {
		String file = "src/test/resources/examples/Channel/Channel.tla";
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
	
	@Test
	public void testSequences() throws Exception {
		String file = "src/test/resources/examples/MySequence/MySequence.tla";
		runModule(file);
	}
	
	@Ignore
	@Test
	public void testRecursiveFunciton() throws Exception {
		String file = "src/test/resources/examples/RecursiveFunction/RecursiveFunction.tla";
		runModule(file);
	}
	
	@Test
	public void testQueens() throws Exception {
		String file = "src/test/resources/MCTests/Queens/MC.tla";
		runModule(file);
	}
	
	@Test
	public void testSumAndProduct() throws Exception {
		String file = "src/test/resources/examples/SumAndProduct/SumAndProductTransition.tla";
		runModule(file);
	}
	
	@Test
	public void testMacroTest() throws Exception {
		String file = "src/test/resources/renamer/MacroTest/MacroTest.tla";
		runModule(file);
	}
	
	@Test
	public void testSumAndProductConstraint() throws Exception {
		String file = "src/test/resources/examples/SumAndProduct/SumAndProductConstraint.tla";
		runModule(file);
	}
	
	@Test
	public void testuf50_02() throws Exception {
		String file = "src/test/resources/examples/uf50_02/uf50_02.tla";
		runModule(file);
	}
	
	@Test
	public void testRecursiveFunction() throws Exception {
		String file = "src/test/resources/examples/RecursiveFunction/RecursiveFunction.tla";
		runModule(file);
	}
}
