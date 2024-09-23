package de.tla2b.expression;

import de.tla2b.exceptions.ExpressionTranslationException;
import org.junit.Test;

import static de.tla2b.util.TestUtil.compareExprIncludingModel;

public class ModuleAndExpressionTest {

	@Test
	public void testCon() throws Exception {
		String module = "---- MODULE Testing ----\n"
			+ "CONSTANTS k \n"
			+ "ASSUME k = 4"
			+ "===============";
		compareExprIncludingModel("k = 1", "k = 1", module);
	}

	@Test(expected = ExpressionTranslationException.class)
	public void testTypeError() throws Exception {
		String module = "---- MODULE Testing ----\n"
			+ "CONSTANTS k \n"
			+ "ASSUME k = 4"
			+ "===============";
		compareExprIncludingModel(null, "k = TRUE", module);
	}

	@Test
	public void testReals() throws Exception {
		String module = "---- MODULE Testing ----\n"
			+ "EXTENDS Reals\n"
			+ "CONSTANTS k, t1, t2 \n"
			+ "ASSUME k = 2.0 /\\ t1 = k*k /\\ t2 = (k < 5.0)"
			+ "===============";
		compareExprIncludingModel("t2 = TRUE", "t2 = TRUE", module);
	}
}
