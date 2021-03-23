package de.tla2b.prettyprintb;

import static de.tla2b.util.TestUtil.compare;

import org.junit.Test;

public class UnchangedVariableTest {

	
	@Test
	public void testUnchangedOnTopLevel() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "VARIABLES x, y \n"
				+ "Init == x = 1 /\\ y = 1 \n"
				+ "Next == x < 2 /\\ x' = 1 /\\ UNCHANGED y\n"
				+ "=================================";
		
		final String expected = "MACHINE Testing\n"
				+ "VARIABLES x, y\n"
				+ "INVARIANT x : INTEGER & y : INTEGER \n"
				+ "INITIALISATION  x, y:(x = 1 & y = 1) \n"
				+ "OPERATIONS Next = SELECT x < 2 & TRUE = TRUE & TRUE = TRUE THEN x:= 1 END \n"
				+ "END";
		compare(expected, module);
	}
}
