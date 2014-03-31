package de.tla2b.prettyprintb;

import static de.tla2b.util.TestUtil.compare;

import org.junit.Test;

public class SimpleModulesTest {

	
	@Test
	public void testSimpleModule() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "=================================";

		final String expected = "MACHINE Testing\n"
				+ "END";
		compare(expected, module);
	}

}
