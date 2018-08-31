package de.tla2b.prettyprintb;

import static de.tla2b.util.TestUtil.compare;

import org.junit.Test;

public class DefinitionsTest {
	
	@Test
	public void testMakePredicate() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "foo == TRUE \n"
				+ "ASSUME foo\n"
				+ "=================================";

		final String expected = "MACHINE Testing\n"
				+ "DEFINITIONS foo == TRUE;"
				+ "PROPERTIES foo = TRUE\n"
				+ "END";
		compare(expected, module);
	}
	
	@Test
	public void testPredicate() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "foo == TRUE = TRUE \n"
				+ "ASSUME foo\n"
				+ "=================================";

		final String expected = "MACHINE Testing\n"
				+ "DEFINITIONS foo == TRUE= TRUE;"
				+ "PROPERTIES foo\n"
				+ "END";
		compare(expected, module);
	}
	
	@Test
	public void testGoalDefinition() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "VARIABLES x, y \n"
				+ "Init == x = 1 /\\ y = 1 \n"
				+ "GOAL == 1=1 \n"
				+ "=================================";
		
		final String expected = "MACHINE Testing\n"
				+ "DEFINITIONS GOAL == 1 = 1;"
				+ "VARIABLES x, y\n"
				+ "INVARIANT x : INTEGER & y : INTEGER \n"
				+ "INITIALISATION  x, y:(x = 1 & y = 1) \n"
				+ "END";
		compare(expected, module);
	}
}
