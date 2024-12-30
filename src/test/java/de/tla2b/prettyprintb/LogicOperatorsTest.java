package de.tla2b.prettyprintb;

import org.junit.Test;

import static de.tla2b.util.TestUtil.compare;

public class LogicOperatorsTest {

	@Test
	public void testEquality() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "CONSTANTS k\n"
			+ "ASSUME k = (2 # 1)\n"
			+ "=================================";

		final String expected = "MACHINE Testing\n" + "CONSTANTS k\n"
			+ "PROPERTIES k : BOOL & k = bool(2 /= 1)\n" + "END";
		compare(expected, module);
	}

	@Test
	public void testEquality2() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "CONSTANTS k\n"
			+ "ASSUME k = TRUE\n"
			+ "=================================";

		final String expected = "MACHINE Testing\n" + "CONSTANTS k\n"
			+ "PROPERTIES k : BOOL & k = TRUE \n" + "END";
		compare(expected, module);
	}

	@Test
	public void testEquality3() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "ASSUME TRUE\n" + "=================================";
		final String expected = "MACHINE Testing\n"
			+ "PROPERTIES TRUE = TRUE \n" + "END";
		compare(expected, module);
	}

	/*
	 * Logic Operators: \neg, \lnot, \land, \cl, \lor, \dl, \equiv, =&gt;
	 */
	@Test
	public void testAnd() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "CONSTANTS k\n"
			+ "ASSUME k = (FALSE \\land TRUE) \n"
			+ "=================================";
		final String expected = "MACHINE Testing\n"
			+ "CONSTANTS k\n"
			+ "PROPERTIES k : BOOL & k = bool(FALSE = TRUE & TRUE = TRUE) \n"
			+ "END";
		compare(expected, module);
	}

	@Test
	public void testAnd2() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "ASSUME TRUE /\\ (TRUE \\/ FALSE) \n"
			+ "=================================";

		final String expected = "MACHINE Testing\n"
			+ "PROPERTIES TRUE = TRUE & (TRUE = TRUE or FALSE = TRUE) \n"
			+ "END";
		compare(expected, module);
	}

	/*
	 * Negation: ~, \neg, \lnot
	 */
	@Test
	public void testNegation() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "ASSUME \\lnot TRUE \n" + "=================================";

		final String expected = "MACHINE Testing\n"
			+ "PROPERTIES not(TRUE = TRUE) \n" + "END";
		compare(expected, module);
	}

	@Test
	public void testNegation2() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS a,b \n"
				+ "ASSUME a \\in BOOLEAN /\\ b = ~a \n"
				+ "=================================";

		final String expected = "MACHINE Testing\n"
				+ "CONSTANTS a, b \n"
				+ "PROPERTIES a : BOOL & b : BOOL & (a : BOOL & b = bool(not(a = TRUE))) \n" + "END";
		compare(expected, module);
	}

	/*
	 * Implication and Equivalence: =>, \equiv
	 */

	@Test
	public void testImplication() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "ASSUME TRUE /\\ (TRUE => FALSE) \n"
			+ "=================================";

		final String expected = "MACHINE Testing\n"
			+ "PROPERTIES TRUE = TRUE & (TRUE = TRUE => FALSE = TRUE) \n"
			+ "END";
		compare(expected, module);
	}

	@Test
	public void testEquivalence() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "ASSUME TRUE /\\ (TRUE <=> FALSE) \n"
			+ "=================================";

		final String expected = "MACHINE Testing\n"
			+ "PROPERTIES TRUE = TRUE & (TRUE = TRUE <=> FALSE = TRUE) \n"
			+ "END";
		compare(expected, module);
	}

	/*
	 * Quantification: \A x \in S : P or \E x \in S : P
	 */
	@Test
	public void testUniversalQuantifier() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "ASSUME \\A x,y \\in {1,2} : x = 0 \n"
			+ "=================================";
		final String expected = "MACHINE Testing\n"
			+ "PROPERTIES !x,y.(x : {1, 2} & y : {1, 2} => x = 0) \n"
			+ "END";
		compare(expected, module);
	}

	@Test
	public void testExistentialQuantifier() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "ASSUME \\E x,y \\in {1,2} : x = 0 \n"
			+ "=================================";
		final String expected = "MACHINE Testing\n"
			+ "PROPERTIES #x,y.(x : {1, 2} & y : {1, 2} & x = 0) \n"
			+ "END";
		compare(expected, module);
	}

	@Test
	public void testExistentialQuantifierSequence() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "ASSUME \\E <<x>> \\in {<<1>>} : x = 1 \n"
			+ "=================================";
		final String expected = "MACHINE Testing\n"
			+ "PROPERTIES #x.([x] : {[1]} & x = 1) \n"
			+ "END";
		compare(expected, module);
	}

	@Test
	public void testExistentialQuantifierTuple() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "ASSUME \\E <<a,b>> \\in {<<1,TRUE>>} : a = 1 /\\ b = TRUE  \n"
			+ "=================================";
		final String expected = "MACHINE Testing\n"
			+ "PROPERTIES #(a,b).((a,b) : {(1,TRUE)} & (a = 1 & b = TRUE)) \n"
			+ "END";
		compare(expected, module);
	}

	@Test
	public void testExistentialQuantifierAll() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "ASSUME \\E <<a,b>> \\in {<<1,TRUE>>}, <<c>> \\in {<<3>>}, d,e \\in {TRUE}:  a= 1 /\\ b = TRUE /\\ c = 3 /\\ d = TRUE /\\ e  \n"
			+ "=================================";
		final String expected = "MACHINE Testing\n"
			+ "PROPERTIES #(a,b,c,d,e).(((((a,b) : {(1,TRUE)} & [c] : {[3]}) & d : {TRUE}) & e : {TRUE}) & ((((a = 1 & b = TRUE) & c = 3) & d = TRUE) & e = TRUE)) \n"
			+ "END";
		compare(expected, module);
	}

	@Test
	public void testQuantifier() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "EXTENDS Naturals, Sequences \n"
			+ "CONSTANTS S \n"
			+ "ASSUME S = {1,2,3} /\\  \\E u \\in Seq(S) : \\A s \\in S : \\E n \\in 1..Len(u) : u[n] = s \n"
			+ "=================================";

		final String expected = "MACHINE Testing\n"
			+ "CONSTANTS S\n"
			+ "PROPERTIES S : POW(INTEGER) & (S = {1, 2, 3} & #u.(u : seq(S) & !s.(s : S => #n.(n : 1 .. size(u) & u(n) = s)))) \n"
			+ "END";
		compare(expected, module);
	}

}
