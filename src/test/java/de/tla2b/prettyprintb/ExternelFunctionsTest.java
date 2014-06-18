package de.tla2b.prettyprintb;

import static de.tla2b.util.TestUtil.compare;

import org.junit.Test;

public class ExternelFunctionsTest {

	
	@Test
	public void testAssert() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS TLC \n"
				+ "ASSUME Assert(TRUE, \"abc\") \n"
				+ "=================================";

		final String expected = "MACHINE Testing\n"
				+ "DEFINITIONS "
				+ "ASSERT_TRUE(P, Msg) == 1 = 1; \n"
				+ "EXTERNAL_PREDICATE_ASSERT_TRUE == BOOL * STRING; \n"
				+ "PROPERTIES ASSERT_TRUE(TRUE, \"abc\") \n" 
				+ "END";
		compare(expected, module);
	}
}
