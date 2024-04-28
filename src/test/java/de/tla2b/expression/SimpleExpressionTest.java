package de.tla2b.expression;

import org.junit.Test;

import static de.tla2b.util.TestUtil.compareExpr;

public class SimpleExpressionTest {

	@Test
	public void testSimpleExpression() throws Exception {
		compareExpr("1 + 2", "1 + 2");
	}

	@Test
	public void testSimplePredicate() throws Exception {
		compareExpr("1 = 1", "1 = 1");
	}

	@Test
	public void testSimplePredicate2() throws Exception {
		compareExpr("1 < 1", "1 < 1");
	}

	@Test
	public void testModulIntegers() throws Exception {
		compareExpr("-1 : INTEGER", "-1 \\in Int");
	}

	@Test
	public void testModulReals() throws Exception {
		compareExpr("1.0 : REAL", "1.0 \\in Real");
	}

	@Test
	public void testRealDivisionExpression() throws Exception {
		compareExpr("1.0 / 2.0", "1.0 / 2.0");
	}

	@Test
	public void testExist() throws Exception {
		compareExpr("#a.(a : {1} & 2 > 1)", "\\E a \\in {1}: 2 > 1");
	}

	@Test
	public void testIfThenElse() throws Exception {
		compareExpr(
				"IF 1 = 1 THEN 1 ELSE 2 END", //"(%t_.( t_ = 0 & 1 = 1 | 1 )\\/%t_.( t_ = 0 & not(1 = 1) | 2 ))(0)",
				"IF 1 = 1 THEN 1 ELSE 2");
	}

	@Test
	public void testTRUE() throws Exception {
		compareExpr("TRUE", "TRUE");
	}
}
