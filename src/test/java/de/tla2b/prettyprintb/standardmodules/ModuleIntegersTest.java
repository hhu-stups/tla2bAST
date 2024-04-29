package de.tla2b.prettyprintb.standardmodules;

import org.junit.Test;

import static de.tla2b.util.TestUtil.compare;

public class ModuleIntegersTest {

	@Test
	public void testUnaryMinus() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "EXTENDS Integers \n"
			+ "ASSUME 1 - 2 = -1 \n"
			+ "=================================";
		final String expected = "MACHINE Testing\n"
			+ "PROPERTIES 1 - 2 = -1 \n"
			+ "END";
		compare(expected, module);
	}

	@Test
	public void testInt() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "EXTENDS Integers \n"
			+ "ASSUME -1 \\in Int \n"
			+ "=================================";
		final String expected = "MACHINE Testing\n"
			+ "PROPERTIES -1 : INTEGER \n"
			+ "END";
		compare(expected, module);
	}
}
