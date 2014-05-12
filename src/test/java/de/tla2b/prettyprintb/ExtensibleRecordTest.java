package de.tla2b.prettyprintb;

import static de.tla2b.util.TestUtil.compare;

import org.junit.Test;

public class ExtensibleRecordTest {

	@Test
	public void testRecord1() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "ASSUME [a |-> 1] = [b |-> TRUE, a |-> 4] \n"
				+ "=================================";

		final String expected = "MACHINE Testing\n"
				+ "PROPERTIES rec(b:{}, a:{(TRUE,1)}) = rec(b:{(TRUE,TRUE)}, a:{(TRUE,4)}) \n"
				+ "END";
		compare(expected, module);
	}

	@Test
	public void testRecord2() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "ASSUME [a |-> 1] = [b |-> TRUE] \n"
				+ "=================================";

		final String expected = "MACHINE Testing\n"
				+ "PROPERTIES rec(b:{}, a:{(TRUE,1)}) = rec(b:{(TRUE,TRUE)}, a:{}) \n"
				+ "END";
		compare(expected, module);
	}

	@Test
	public void testSelect() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k \n"
				+ "ASSUME k = [a |-> 1] /\\ k # [b |-> 1] /\\ k.a = 1 \n"
				+ "=================================";

		final String expected = "MACHINE Testing\n"
				+ "ABSTRACT_CONSTANTS k \n"
				+ "PROPERTIES k : struct(b:POW(BOOL * INTEGER), a:POW(BOOL * INTEGER)) & ((k = rec(b:{}, a:{(TRUE,1)}) & k /= rec(b:{(TRUE,1)}, a:{})) & (k'a)(TRUE) = 1) \n"
				+ "END";
		compare(expected, module);
	}

	@Test
	public void testSelect2() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "ASSUME [a |-> 1].b = TRUE \n"
				+ "=================================";

		final String expected = "MACHINE Testing\n"
				+ "PROPERTIES (rec(a:{(TRUE,1)}, b:{})'b)(TRUE) = TRUE \n"
				+ "END";
		compare(expected, module);
	}
	
	@Test
	public void testStructExpansion() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "ASSUME [a: {2}] = [a : {1}, b : BOOLEAN] \n"
				+ "=================================";

		final String expected = "MACHINE Testing\n"
				+ "PROPERTIES struct(a:POW(BOOL * {2}), b:POW(BOOL * BOOL)) = struct(a:POW(BOOL * {1}), b:POW(BOOL * BOOL)) \n"
				+ "END";
		compare(expected, module);
	}
	
	@Test
	public void testRecExpansion2() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k \n"
				+ "ASSUME k = [a |-> 1] /\\ TRUE = k.b \n"
				+ "=================================";

		final String expected = "MACHINE Testing\n"
				+ "ABSTRACT_CONSTANTS k \n"
				+ "PROPERTIES k : struct(a:POW(BOOL * INTEGER), b:POW(BOOL * BOOL)) & (k = rec(a:{(TRUE,1)}, b:{}) & TRUE = (k'b)(TRUE)) \n"
				+ "END";
		compare(expected, module);
	}
	
}
