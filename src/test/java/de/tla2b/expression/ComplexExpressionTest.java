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
	public void testLetPredicate() throws Exception {
		compareExpr("1=1 & 1 = 1", "LET foo == 1 = 1 IN foo /\\ foo");
	}

	@Test
	public void testLetParameterPredicate() throws Exception {
		compareExpr("1=1 & 1 = 2", "LET foo(a,b) == a = b IN foo(1,1) /\\ foo(1,2)");
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
	public void testLetTwoDefsReal() throws Exception {
		compareExpr("1.0 + 2.0", "LET foo == 1.0 bar == 2.0 IN foo + bar ");
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

	@Test
	public void testConstraint1() throws Exception {
		compareExpr("x**3 - 20*x**2 + 7*x = 14388",
			"x^3 - 20*x^2 + 7*x = 14388");
	}

	@Test
	public void testConstraintCHOOSE() throws Exception {
		compareExpr("CHOOSE({x|x:0..100 & x**3 - 20*x**2 + 7*x = 14388})",
			"CHOOSE x \\in 0..100: x^3 - 20*x^2 + 7*x = 14388");
	}

	@Test
	public void testConstraintCHOOSENested() throws Exception {
		compareExpr("CHOOSE({y|y : 0 .. 100 & y = CHOOSE({x|x : 0 .. 100 & x ** 3 - 20 * x ** 2 + 7 * x = 14388})})",
			"CHOOSE y \\in 0..100: y = CHOOSE x \\in 0..100: x^3 - 20*x^2 + 7*x = 14388");
	}
	// Note that for:  CHOOSE x \in 0..100: x = CHOOSE x \in 0..100: x^3 - 20*x^2 + 7*x = 14388
	//   we get an error: Multiply-defined symbol 'x': this definition or declaration conflicts

	@Test
	public void testRelParFunSet() throws Exception {
		compareExpr("{f|f:POW(INTEGER*BOOL) & card(UNION(x).(x:f|{prj1(INTEGER,BOOL)(x)}))=card(f)}",
			"{f \\in SUBSET (Int \\times BOOLEAN): Cardinality({ x[1] :x \\in f}) = Cardinality(f)}");
	}
}
