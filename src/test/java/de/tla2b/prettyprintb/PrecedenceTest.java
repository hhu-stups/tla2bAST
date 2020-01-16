package de.tla2b.prettyprintb;

import static de.tla2b.util.TestUtil.compare;

import org.junit.Test;

public class PrecedenceTest {

	@Test
	public void testPrecedence() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "ASSUME 1 + (2 * 3) = 7 \n"
				+ "=================================";
		final String expected = "MACHINE Testing\n"
				+ "PROPERTIES 1 + 2 * 3 = 7 \n" + "END";
		compare(expected, module);
	}

	
	@Test
	public void testPrecedence2() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "ASSUME (1 + 2) * 3 = 9 \n"
				+ "=================================";

		final String expected = "MACHINE Testing\n"
				+ "PROPERTIES (1 + 2) * 3 = 9 \n" + "END";
		compare(expected, module);
	}
	
	@Test
	public void testPrecedence3() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "ASSUME (1 + 2) + 3 = 6 \n"
				+ "=================================";
		final String expected = "MACHINE Testing\n"
				+ "PROPERTIES 1 + 2 + 3 = 6 \n" + "END";
		compare(expected, module);
	}
	
	@Test
	public void testPrecedence4() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "ASSUME 1 + (2 + 3) = 6 \n"
				+ "=================================";
		final String expected = "MACHINE Testing\n"
				+ "PROPERTIES 1 + (2 + 3) = 6 \n" + "END";
		compare(expected, module);
	}

}
