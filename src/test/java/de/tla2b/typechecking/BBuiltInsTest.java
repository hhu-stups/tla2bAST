package de.tla2b.typechecking;

import de.tla2b.exceptions.TLA2BException;
import de.tla2b.exceptions.TypeErrorException;
import de.tla2b.util.TestTypeChecker;
import de.tla2b.util.TestUtil;
import org.junit.Test;

import static org.junit.Assert.assertEquals;


public class BBuiltInsTest {


	/*
	 * BOOLEAN
	 */
	@Test
	public void testBoolean() throws TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "CONSTANTS k \n"
			+ "ASSUME k = BOOLEAN \n"
			+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("POW(BOOL)", t.getConstantType("k"));
	}

	@Test(expected = TypeErrorException.class)
	public void testBooleanException() throws TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "CONSTANTS k \n"
			+ "ASSUME 1 \\in BOOLEAN \n"
			+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("POW(BOOL)", t.getConstantType("k"));
	}

	@Test
	public void testNestedBooleanDefinitions() throws Exception {
		String module = "---- MODULE Testing ----\n"
				+ "EXTENDS Naturals \n"
				+ "InnerDef(b) == b>5 \n"
				+ "HelpDef(a,b) == a<7 /\\ InnerDef(b) \n"
				+ "Init == TRUE = HelpDef(3,4) \n"
				+ "===============";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("BOOL", t.getDefinitionType("HelpDef"));
		assertEquals("BOOL", t.getDefinitionType("InnerDef"));
	}

	/*
	 * String
	 */
	@Test
	public void testString() throws TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "CONSTANTS k \n"
			+ "ASSUME k = STRING \n"
			+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("POW(STRING)", t.getConstantType("k"));
	}

	@Test(expected = TypeErrorException.class)
	public void testUnifyErrorString() throws TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "CONSTANTS k \n"
			+ "ASSUME 1 = STRING \n"
			+ "=================================";
		TestUtil.typeCheckString(module);
	}

	/*
	 * Bool value: TRUE, FALSE
	 */
	@Test
	public void testBoolValue() throws TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "CONSTANTS k \n"
			+ "ASSUME k = TRUE \n"
			+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("BOOL", t.getConstantType("k"));
	}

	@Test(expected = TypeErrorException.class)
	public void testUnifyErrorBoolValue() throws TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "ASSUME 1 = TRUE \n"
			+ "=================================";
		TestUtil.typeCheckString(module);
	}


}
