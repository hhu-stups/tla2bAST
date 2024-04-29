package de.tla2b.prettyprintb;

import org.junit.Ignore;
import org.junit.Test;

import static de.tla2b.util.TestUtil.compare;

public class FunctionTest {

	@Test
	public void testFunctionConstructor() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "CONSTANTS k\n"
			+ "ASSUME k = [x \\in {1} |-> TRUE = TRUE] \n"
			+ "=================================";

		final String expected = "MACHINE Testing\n"
			+ "CONSTANTS k\n"
			+ "PROPERTIES k :  INTEGER +-> BOOL & k = %x.(x : {1}| bool(TRUE = TRUE)) \n"
			+ "END";
		compare(expected, module);
	}

	@Test
	public void testFunctionConstructor2() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "CONSTANTS k\n"
			+ "ASSUME k = [x,y \\in {1,2} |-> 1] \n"
			+ "=================================";

		final String expected = "MACHINE Testing\n"
			+ "CONSTANTS k\n"
			+ "PROPERTIES k : INTEGER * INTEGER +-> INTEGER & k = %x,y.(x : {1,2} & y : {1,2}| 1) \n"
			+ "END";
		compare(expected, module);
	}

	@Test
	public void testFunctionConstructor3() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "CONSTANTS k\n"
			+ "ASSUME k = [x \\in {1}, y \\in BOOLEAN |-> 1] \n"
			+ "=================================";

		final String expected = "MACHINE Testing\n"
			+ "CONSTANTS k\n"
			+ "PROPERTIES k : INTEGER * BOOL +-> INTEGER & k = %x,y.(x : {1} & y : BOOL| 1) \n"
			+ "END";
		compare(expected, module);
	}

	@Test
	public void testFunctionConstructor4() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "EXTENDS Naturals \n"
			+ "CONSTANTS k\n"
			+ "ASSUME k = [<<x,y>> \\in {1} \\X {2} |-> x + y] \n"
			+ "=================================";

		final String expected = "MACHINE Testing\n"
			+ "CONSTANTS k\n"
			+ "PROPERTIES k : INTEGER * INTEGER +-> INTEGER & k = %(x, y).((x,y) : {1} * {2} | x + y) \n"
			+ "END";
		compare(expected, module);
	}

	@Test
	public void testFunctionConstructorTuple() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "EXTENDS Naturals \n"
			+ "CONSTANTS k\n"
			+ "ASSUME k = [a \\in {1}, <<b,c>> \\in {2} \\X {3} |-> a + b + c] \n"
			+ "=================================";

		final String expected = "MACHINE Testing\n"
			+ "CONSTANTS k\n"
			+ "PROPERTIES k : INTEGER * (INTEGER * INTEGER) +-> INTEGER  & k = %(a, bc).(a : {1} & bc : {2} * {3} | (a + prj1(INTEGER, INTEGER)(bc)) + prj2(INTEGER, INTEGER)(bc)) \n"
			+ "END";
		compare(expected, module);
	}

	@Test
	public void testFunctionConstructorSequence() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "EXTENDS Naturals \n"
			+ "CONSTANTS k\n"
			+ "ASSUME k = [<<a>> \\in {<<1>>}, <<b,c>> \\in {2} \\X {3} |-> a + b + c] \n"
			+ "=================================";

		final String expected = "MACHINE Testing\n"
			+ "CONSTANTS k\n"
			+ "PROPERTIES k : (INTEGER +-> INTEGER) * (INTEGER * INTEGER) +-> INTEGER  & k = %(a, bc).(a : {[1]} & bc : {2} * {3} | (a(1) + prj1(INTEGER, INTEGER)(bc)) + prj2(INTEGER, INTEGER)(bc)) \n"
			+ "END";
		compare(expected, module);
	}

	/*
	 * recursive Function
	 */

	@Ignore
	@Test
	public void testRecursiveFunction() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "EXTENDS Naturals \n"
			+ "CONSTANTS k, k2, k3 \n"
			+ "fact[n \\in {1,2}] == IF n = 0 THEN 1 ELSE n+ fact[n-1] \n"
			+ "ASSUME k = fact /\\ fact[k2] = k3 \n"
			+ "=================================";

		final String expected = "MACHINE Testing\n"
			+ "CONSTANTS k,k2,k3\n"
			+ "PROPERTIES k : POW(INTEGER*INTEGER) & k2 : INTEGER & k3 : INTEGER \n"
			+ " & k = fact & fact(k2) = k3 \n"
			+ "DEFINITIONS IF_THEN_ELSE(P, a, b) == (%t_.(t_=TRUE & P = TRUE | a )\\/%t_.(t_=TRUE & not(P= TRUE) | b ))(TRUE); \n"
			+ "fact == %n.(n : {1, 2}| IF_THEN_ELSE(bool(n = 0), 1, n + fact(n - 1))) \n"
			+ "END";
		compare(expected, module);
	}

	/*
	 * Function call
	 */
	@Test
	public void testFunctionCall() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "EXTENDS Naturals \n"
			+ "ASSUME [x,y \\in {1,2} |-> x+y] [1,2] = 3 \n"
			+ "=================================";

		final String expected = "MACHINE Testing\n"
			+ "PROPERTIES %x,y.(x : {1,2} & y : {1,2}| x + y) (1, 2) = 3 \n"
			+ "END";
		compare(expected, module);
	}

	@Test
	public void testFunctionCall2() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "ASSUME[x \\in {1} |-> TRUE][1] \n"
			+ "=================================";

		final String expected = "MACHINE Testing\n"
			+ "PROPERTIES %x.(x : {1}| TRUE)(1) = TRUE\n" + "END";
		compare(expected, module);
	}

	@Test
	public void testDomain() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "ASSUME DOMAIN[x \\in {1} |-> x] = {1} \n"
			+ "=================================";

		final String expected = "MACHINE Testing\n"
			+ "PROPERTIES dom(%x.(x : {1}| x)) = {1}" + "END";
		compare(expected, module);
	}

	@Test
	public void testSetOfFunction() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "CONSTANTS k \n"
			+ "ASSUME k = [BOOLEAN -> {1}] \n"
			+ "=================================";

		final String expected = "MACHINE Testing\n" + "CONSTANTS k\n"
			+ "PROPERTIES k : POW(BOOL +-> INTEGER) &  k = BOOL --> {1}"
			+ "END";
		compare(expected, module);
	}


}
