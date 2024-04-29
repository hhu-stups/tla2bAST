package de.tla2b.prettyprintb.standardmodules;

import org.junit.Test;

import static de.tla2b.util.TestUtil.compare;


public class ModuleFiniteSetsTest {

	@Test
	public void testIsFiniteSet() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "EXTENDS FiniteSets \n"
			+ "ASSUME IsFiniteSet({1,2,3}) \n"
			+ "=================================";
		final String expected = "MACHINE Testing\n"
			+ "PROPERTIES {1,2,3} : FIN({1,2,3}) \n" + "END";
		compare(expected, module);
	}

	@Test
	public void testIsFiniteSet2() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "EXTENDS FiniteSets, Naturals \n"
			+ "ASSUME IsFiniteSet(Nat) \n"
			+ "=================================";
		final String expected = "MACHINE Testing\n"
			+ "PROPERTIES NATURAL : FIN(NATURAL) \n" + "END";
		compare(expected, module);
	}

	@Test
	public void testCardinality() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "EXTENDS FiniteSets, Naturals \n"
			+ "ASSUME Cardinality({1,2,3}) = 3 \n"
			+ "=================================";
		final String expected = "MACHINE Testing\n"
			+ "PROPERTIES card({1,2,3}) = 3 \n" + "END";
		compare(expected, module);
	}

}
