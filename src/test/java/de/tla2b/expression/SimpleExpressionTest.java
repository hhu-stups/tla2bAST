/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package de.tla2b.expression;

import org.junit.Test;

import static de.tla2b.util.TestUtil.compareExpr;

public class SimpleExpressionTest {

	@Test
	public void testSimpleExpr() throws Exception {
		compareExpr("1 + 2", "1 + 2");
	}

	@Test
	public void testModulIntegers() throws Exception {
		compareExpr("bool(-1 : INTEGER)", "-1 \\in Int");
	}

	@Test
	public void testExist() throws Exception {
		compareExpr("bool(#a.(a : {1} & 2 > 1))", "\\E a \\in {1}: 2 > 1");
	}

	@Test
	public void testIfThenElse() throws Exception {
		compareExpr(
				"(%t_.( t_ = 0 & 1 = 1 | 1 )\\/%t_.( t_ = 0 & not(1 = 1) | 2 ))(0)",
				"IF 1 = 1 THEN 1 ELSE 2");
	}

	@Test
	public void testTRUE() throws Exception {
		compareExpr("TRUE", "TRUE");
	}
}