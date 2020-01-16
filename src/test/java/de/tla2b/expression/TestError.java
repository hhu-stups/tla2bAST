package de.tla2b.expression;

import static de.tla2b.util.TestUtil.compareExpr;

import org.junit.Test;

import de.tla2b.exceptions.ExpressionTranslationException;

public class TestError {

	@Test(expected = ExpressionTranslationException.class)
	public void testParseError() throws Exception {
		compareExpr(null, "a =");
	}

	@Test(expected = ExpressionTranslationException.class)
	public void testSemanticError() throws Exception {
		compareExpr(null, "a(1)");
	}

	@Test(expected = ExpressionTranslationException.class)
	public void testTypeError() throws Exception {
		compareExpr(null, "1 = TRUE");
	}
}
