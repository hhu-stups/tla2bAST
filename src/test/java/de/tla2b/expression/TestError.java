/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package de.tla2b.expression;

import static de.tla2b.util.TestUtil.compareExpr;

import org.junit.Test;

public class TestError {

	@Test(expected = Exception.class)
	public void testParseError() throws Exception {
		compareExpr(null, "a =");
	}

	@Test(expected = Exception.class)
	public void testSemanticError() throws Exception {
		compareExpr(null, "a(1)");
	}

	@Test(expected = Exception.class)
	public void testTypeError() throws Exception {
		compareExpr(null, "1 = TRUE");
	}
}
