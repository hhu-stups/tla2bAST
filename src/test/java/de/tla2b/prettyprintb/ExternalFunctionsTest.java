package de.tla2b.prettyprintb;

import org.junit.Test;

import static de.tla2b.util.TestUtil.compare;

public class ExternalFunctionsTest {


	@Test
	public void testAssert() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "EXTENDS TLC \n"
			+ "ASSUME Assert(TRUE, \"abc\") \n"
			+ "=================================";

		final String expected = "MACHINE Testing\n"
			+ "DEFINITIONS "
			+ "ASSERT_TRUE(P, Msg) == btrue; \n"
			+ "EXTERNAL_PREDICATE_ASSERT_TRUE == BOOL * STRING; \n"
			+ "PROPERTIES ASSERT_TRUE(TRUE, \"abc\") \n"
			+ "END";
		compare(expected, module);
	}
}
