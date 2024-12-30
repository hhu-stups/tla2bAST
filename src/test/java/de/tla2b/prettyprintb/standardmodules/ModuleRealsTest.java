package de.tla2b.prettyprintb.standardmodules;

import org.junit.Test;

import static de.tla2b.util.TestUtil.compare;

public class ModuleRealsTest {

	// Arithmetic operator: /
	@Test
	public void testArithmeticOperators() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "EXTENDS Reals \n"
			+ "ASSUME 1.0 / 2.0 = 0.5 \n"
			+ "=================================";
		final String expected = "MACHINE Testing\n"
			+ "PROPERTIES 1.0 / 2.0 = 0.5 \n"
			+ "END";
		compare(expected, module);
	}

}
