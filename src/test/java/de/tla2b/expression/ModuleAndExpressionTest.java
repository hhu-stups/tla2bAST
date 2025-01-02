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

	@Test
	public void testVar() throws Exception {
		String module = "---- MODULE Testing ----\n"
				+ "VARIABLES v \n"
				+ "Init == v = 4.0 \n"
				+ "Next == v' = 5.0"
				+ "===============";
		compareExprIncludingModel("v = 4.0", "v = 4.0", module);
	}

	@Test(expected = ExpressionTranslationException.class)
	public void testConTypeError() throws Exception {
		String module = "---- MODULE Testing ----\n"
			+ "CONSTANTS k \n"
			+ "ASSUME k = 4"
			+ "===============";
		compareExprIncludingModel(null, "k = TRUE", module);
	}

	@Test(expected = ExpressionTranslationException.class)
	public void testVarTypeError() throws Exception {
		String module = "---- MODULE Testing ----\n"
				+ "VARIABLES v \n"
				+ "Init == v = 4.0 \n"
				+ "Next == v' = 5.0"
				+ "===============";
		compareExprIncludingModel(null, "v = TRUE", module);
	}

	@Test
	public void testConAdditionalFreeVariable() throws Exception {
		String module = "---- MODULE Testing ----\n"
				+ "CONSTANTS k \n"
				+ "ASSUME k = 4"
				+ "===============";
		compareExprIncludingModel("k = s", "k = s", module);
	}

	@Test
	public void testVarAdditionalFreeVariable() throws Exception {
		String module = "---- MODULE Testing ----\n"
				+ "VARIABLES v \n"
				+ "Init == v = 4.0 \n"
				+ "Next == v' = 5.0"
				+ "===============";
		compareExprIncludingModel("v = s", "v = s", module);
	}

	@Test(expected = ExpressionTranslationException.class)
	public void testAdditionalFreeVariableError() throws Exception {
		String module = "---- MODULE Testing ----\n"
				+ "CONSTANTS k \n"
				+ "ASSUME k = 4"
				+ "===============";
		compareExprIncludingModel(null, "s = TRUE /\\ k = s", module);
	}

	@Test
	public void testWithDefinitions() throws Exception {
		String module = "---- MODULE Testing ----\n"
				+ "EXTENDS Naturals \n"
				+ "CONSTANTS k \n"
				+ "ASSUME k = 4 \n"
				+ "InnerDef(b) == b*5 \n"
				+ "HelpDef(a,b) == a+InnerDef(b) \n"
				+ "Init == 1 = HelpDef(1,1) \n" // to get defs into translated B definitions
				+ "===============";
		compareExprIncludingModel("HelpDef(k,k)", "HelpDef(k,k)", module);
	}

	@Test
	public void testWithDefinitionsAndFreeVariables() throws Exception {
		String module = "---- MODULE Testing ----\n"
				+ "EXTENDS Naturals \n"
				+ "CONSTANTS k \n"
				+ "ASSUME k = 4 \n"
				+ "InnerDef(b) == b*5 \n"
				+ "HelpDef(a,b) == a+InnerDef(b) \n"
				+ "SecondDef(x) == x \n"
				+ "Init == 1.0 = SecondDef(1.0) /\\ 1 = HelpDef(1,1) \n" // to get defs into translated B definitions
				+ "===============";
		compareExprIncludingModel("s = 5 & t = 10 & w : REAL & v = HelpDef(s,t) & w = SecondDef(s)",
				"s = 5 /\\ t = 10 /\\ w \\in Real /\\ v = HelpDef(s,t) /\\ w = SecondDef(s)", module);
	}

	@Test(expected = ExpressionTranslationException.class)
	public void testWithDefinitionError() throws Exception {
		String module = "---- MODULE Testing ----\n"
				+ "EXTENDS Reals \n"
				+ "CONSTANTS k \n"
				+ "ASSUME k = 4.0 \n"
				+ "HelpDef(a,b) == 0.3*a+2.7*b \n"
				+ "Init == 1.0 = HelpDef(1.0,1.0) \n" // to get defs into translated B definitions
				+ "===============";
		compareExprIncludingModel(null, "s \\in Int /\\ HelpDef(k,s)", module);
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
