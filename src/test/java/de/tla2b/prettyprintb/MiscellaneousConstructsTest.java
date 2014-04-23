package de.tla2b.prettyprintb;

import static de.tla2b.util.TestUtil.compare;

import org.junit.Test;

public class MiscellaneousConstructsTest {

	@Test
	public void testSimpleLet() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "ASSUME LET foo(a) == a + a IN 4 = foo(2)\n"
				+ "=================================";

		final String expected = "MACHINE Testing\n"
				+ "PROPERTIES 4 = 2 + 2 \n" + "END";
		compare(expected, module);
	}
	
	@Test
	public void testLet2Definitions() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "ASSUME LET foo(a) == a + a bar(b) == b * b IN bar(2) = foo(2)\n"
				+ "=================================";

		final String expected = "MACHINE Testing\n"
				+ "PROPERTIES 2 * 2 = 2 + 2 \n" + "END";
		compare(expected, module);
	}
	
	@Test
	public void testNestedLet() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "ASSUME LET foo(a) == LET bar(b) == b * b IN bar(a+1) IN 9 = foo(2)\n"
				+ "=================================";

		final String expected = "MACHINE Testing\n"
				+ "PROPERTIES 9 = (2 + 1) * (2 + 1) \n" + "END";
		compare(expected, module);
	}
	
	@Test
	public void testSimpleCase() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "ASSUME 2 = CASE 1 = 1 -> 2 \n"
				+ "=================================";

		final String expected = "MACHINE Testing\n"
				+ "DEFINITIONS CHOOSE(X) == \"a member of X\"; EXTERNAL_FUNCTION_CHOOSE(T) == POW(T) --> T;"
				+ "PROPERTIES 2 = CHOOSE({t_ | 1=1 & t_ = 2}) \n" + "END";
		compare(expected, module);
	}
	
	@Test
	public void testCase2Conditions() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "ASSUME 2 = CASE 1 = 1 -> 2 [] 1 = 2 -> 3\n"
				+ "=================================";

		final String expected = "MACHINE Testing\n"
				+ "DEFINITIONS CHOOSE(X) == \"a member of X\"; EXTERNAL_FUNCTION_CHOOSE(T) == POW(T) --> T;"
				+ "PROPERTIES 2 = CHOOSE({t_ | (1 = 1 & t_ = 2) or (1 = 2 & t_ = 3)}) \n" + "END";
		compare(expected, module);
	}
	
	@Test
	public void testCaseOtherCondition() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "ASSUME 4 = CASE 1 = 2 -> 2 [] 1 = 3 -> 3 [] OTHER -> 4\n"
				+ "=================================";

		final String expected = "MACHINE Testing\n"
				+ "DEFINITIONS CHOOSE(X) == \"a member of X\"; EXTERNAL_FUNCTION_CHOOSE(T) == POW(T) --> T;"
				+ "PROPERTIES 4 = CHOOSE({t_ | ((1 = 2 & t_ = 2) or (1 = 3 & t_ = 3)) or (not(1 = 2 or 1 = 3) & t_ = 4)}) \n" + "END";
		compare(expected, module);
	}
	
	@Test
	public void testCasePredicate() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "ASSUME CASE 1 = 2 -> TRUE [] TRUE -> 1=1\n"
				+ "=================================";

		final String expected = "MACHINE Testing\n"
				+ "DEFINITIONS CHOOSE(X) == \"a member of X\"; EXTERNAL_FUNCTION_CHOOSE(T) == POW(T) --> T;"
				+ "PROPERTIES CHOOSE({t_ | (1 = 2 & t_ = TRUE) or (TRUE = TRUE & t_ = bool(1 = 1))}) = TRUE \n" + "END";
		compare(expected, module);
	}
	
	
	@Test
	public void testUnboundedChoose() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "ASSUME (CHOOSE x : x = 1) = 1\n"
				+ "=================================";

		final String expected = "MACHINE Testing\n"
				+ "DEFINITIONS CHOOSE(X) == \"a member of X\"; EXTERNAL_FUNCTION_CHOOSE(T) == POW(T) --> T;"
				+ "PROPERTIES CHOOSE({x | x = 1}) = 1 \n" + "END";
		compare(expected, module);
	}
	
	@Test
	public void testUnboundedChoosePredicate() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "ASSUME (CHOOSE x : x = TRUE)\n"
				+ "=================================";

		final String expected = "MACHINE Testing\n"
				+ "DEFINITIONS CHOOSE(X) == \"a member of X\"; EXTERNAL_FUNCTION_CHOOSE(T) == POW(T) --> T;"
				+ "PROPERTIES CHOOSE({x | x = TRUE}) = TRUE \n" + "END";
		compare(expected, module);
	}
	
	@Test
	public void testBoundedChoose() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "ASSUME (CHOOSE x \\in {1}: TRUE) = 1\n"
				+ "=================================";

		final String expected = "MACHINE Testing\n"
				+ "DEFINITIONS CHOOSE(X) == \"a member of X\"; EXTERNAL_FUNCTION_CHOOSE(T) == POW(T) --> T;"
				+ "PROPERTIES CHOOSE({x | x : {1} & TRUE = TRUE}) = 1 \n" + "END";
		compare(expected, module);
	}
	
	@Test
	public void testBoundedChoosePredicate() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "ASSUME (CHOOSE x \\in {TRUE}: TRUE) = TRUE\n"
				+ "=================================";

		final String expected = "MACHINE Testing\n"
				+ "DEFINITIONS CHOOSE(X) == \"a member of X\"; EXTERNAL_FUNCTION_CHOOSE(T) == POW(T) --> T;"
				+ "PROPERTIES CHOOSE({x | x : {TRUE} & TRUE = TRUE}) = TRUE \n" + "END";
		compare(expected, module);
	}
}
