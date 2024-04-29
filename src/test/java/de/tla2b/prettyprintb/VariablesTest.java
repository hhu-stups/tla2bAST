package de.tla2b.prettyprintb;

import org.junit.Test;

import static de.tla2b.util.TestUtil.compare;

public class VariablesTest {

	@Test
	public void testVariables() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "EXTENDS Naturals \n"
			+ "VARIABLES x, y \n"
			+ "Init == x = 1 /\\ y = 1 \n"
			+ "=================================";

		final String expected = "MACHINE Testing\n"
			+ "VARIABLES x, y\n"
			+ "INVARIANT x : INTEGER & y : INTEGER \n"
			+ "INITIALISATION  x, y:(x = 1 & y = 1) \n"
			+ "END";
		compare(expected, module);
	}

}
