package de.tla2b.examples;

import org.junit.Test;
import static de.tla2b.util.TestUtil.runModule;


public class ForDistribution {

	
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
	
}
