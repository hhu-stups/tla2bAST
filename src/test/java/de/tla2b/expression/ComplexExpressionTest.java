/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package de.tla2b.expression;

import org.junit.Test;

import static de.tla2b.util.TestUtil.compareExpr;

public class ComplexExpressionTest {

	@Test
	public void testExcept() throws Exception {
		compareExpr("a = %u.(u : {3, 4, 5}| u + 1) & x = a <+ {3 |-> 1}",
				"a = [u \\in {3,4,5}|-> u + 1] /\\ x = [a EXCEPT ![3] = 1]");
	}

	@Test
	public void testLetIn() throws Exception {
		compareExpr("1 + 1", "LET foo == 1 IN foo + foo");
	}

	@Test
	public void testLetDefWithArgs() throws Exception {
		compareExpr("2 * 4", "LET foo(x,y) == x * y IN foo(2,4) ");
	}

	@Test
	public void testLetTwoDefs() throws Exception {
		compareExpr("1 + 2", "LET foo == 1 bar == 2 IN foo + bar ");
	}

	@Test
	public void testPrime() throws Exception {
		compareExpr("x_n = 1", "x' = 1");
	}

	@Test
	public void testFunction() throws Exception {
		compareExpr("%n.(n : {1}| 1)(1)", "LET f[n \\in {1}] == 1 IN f[1]");
	}

	@Test
	public void testQuantifier() throws Exception {
		compareExpr(
				"#x,z,y.(x : NATURAL & z : NATURAL & y : NATURAL & x = y)",
				"\\E x,z \\in Nat, y \\in Nat: x = y");
	}

	@Test
	public void testFunctions() throws Exception {
		compareExpr("(%x.(x : 1 .. 10| x * x) <+ {3 |-> 6})(3)", "LET"
				+ " f[x \\in 1..10] == x*x\n" + " h == [f EXCEPT ![3] = 6]\n"
				+ "IN h[3]");
	}

	@Test
	public void testRecord() throws Exception {
		compareExpr("rec(a:rec(a:1, b:TRUE)'a + rec(a:1, b:TRUE)'a, b:rec(a:1, b:TRUE)'b)",
				"[[a|->1, b |->TRUE] EXCEPT !.a= @+@]");
	}

	@Test
	public void testRecord2() throws Exception {
		compareExpr("r = rec(a:rec(x:1, y:TRUE), b:1) & r2 = rec(a:rec(x:2, y:(r'a)'y), b:r'b)",
				"r = [a |-> [x|->1,y|->TRUE], b |-> 1] "
						+ "/\\ r2 = [r EXCEPT !.a.x = 2]");
	}

}
