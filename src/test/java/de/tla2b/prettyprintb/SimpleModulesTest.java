package de.tla2b.prettyprintb;

import org.junit.Test;

import static de.tla2b.util.TestUtil.compare;

public class SimpleModulesTest {


	@Test
	public void testSimpleModule() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "=================================";

		final String expected = "MACHINE Testing\n"
			+ "END";
		compare(expected, module);
	}

	@Test
	public void testSingleOperator() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "EXTENDS Naturals\n"
			+ "add(a,b) == a + b \n"
			+ "ASSUME add(1,3) = 4 \n"
			+ "=================================";

		final String expected = "MACHINE Testing\n"
			+ "DEFINITIONS add(a,b) == a + b \n"
			+ "PROPERTIES add(1,3) = 4\n"
			+ "END";
		compare(expected, module);
	}

	@Test
	public void testVariables() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "EXTENDS Naturals\n"
			+ "VARIABLES x \n"
			+ "Init == x = 1\n"
			+ "e1 == x'= 1 \n"
			+ "e2 == x'= 2 \n"
			+ "Next == e1 \\/ e2 \n"
			+ "=================================";

		final String expected = "MACHINE Testing\n"
			+ "VARIABLES x \n"
			+ "INVARIANT x : INTEGER \n"
			+ "INITIALISATION x :(x = 1) \n"
			+ "OPERATIONS \n"
			+ "e1 = BEGIN x := 1 END; \n"
			+ "e2 = BEGIN x := 2 END \n"
			+ "END";
		compare(expected, module);
	}

	@Test
	public void testVariables2() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "EXTENDS Naturals\n"
			+ "VARIABLES x \n"
			+ "Init == x = 1\n"
			+ "e1 == /\\ 1= 2 /\\ x'+ 1= 1 \n"
			+ "e2 == x = 1 /\\ x'= 2 \n"
			+ "Next == e1 \\/ e2 \n"
			+ "=================================";

		final String expected = "MACHINE Testing\n"
			+ "VARIABLES x \n"
			+ "INVARIANT x : INTEGER \n"
			+ "INITIALISATION x :(x = 1) \n"
			+ "OPERATIONS \n"
			+ "e1 = ANY x_n WHERE 1 = 2 & x_n : INTEGER & x_n + 1 = 1 THEN x := x_n END; \n"
			+ "e2 = SELECT x = 1 THEN x := 2 END \n"
			+ "END";
		compare(expected, module);
	}

}
