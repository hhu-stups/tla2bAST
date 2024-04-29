package de.tla2b.typechecking.standardmodules;

import de.tla2b.exceptions.TLA2BException;
import de.tla2b.exceptions.TypeErrorException;
import de.tla2b.util.TestTypeChecker;
import de.tla2b.util.TestUtil;
import org.junit.Test;

import static org.junit.Assert.assertEquals;


public class TestModuleReals {

	/*
	 * Real
	 */
	@Test
	public void unifyReal() throws TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "EXTENDS Reals \n"
			+ "CONSTANTS k \n"
			+ "ASSUME k = Real \n" + "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("POW(REAL)", t.getConstantType("k"));
	}

	@Test(expected = TypeErrorException.class)
	public void unifyErrorReal() throws TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "EXTENDS Reals \n"
			+ "ASSUME TRUE \\in Real \n"
			+ "=================================";

		TestUtil.typeCheckString(module);
	}

	/*
	 * unary minus: -x
	 */
	@Test
	public void unifyUnaryMinusReal() throws TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "EXTENDS Reals \n"
			+ "CONSTANTS k \n"
			+ "ASSUME k = -1.0 \n" + "=================================";

		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("REAL", t.getConstantType("k"));
	}

	@Test(expected = TypeErrorException.class)
	public void unifyUnaryMinusRealError() throws TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "EXTENDS Reals \n"
			+ "ASSUME -1 = -1.0 \n" + "=================================";

		TestUtil.typeCheckString(module);
	}

	@Test(expected = TypeErrorException.class)
	public void unifyErrorUnaryMinusReal() throws TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "EXTENDS Reals \n"
			+ "ASSUME TRUE = -1.0 \n"
			+ "=================================";
		TestUtil.typeCheckString(module);
	}

	@Test(expected = TypeErrorException.class)
	public void testRelationalOperatorsException1() throws
		TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "EXTENDS Reals \n"
			+ "CONSTANTS k, k2 \n"
			+ "ASSUME 1.0 = (2 > 1) \n" + "=================================";
		TestUtil.typeCheckString(module);
	}

	@Test(expected = TypeErrorException.class)
	public void testRelationalOperatorsException2() throws
		TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "EXTENDS Reals \n"
			+ "CONSTANTS k, k2 \n"
			+ "ASSUME 1.0 = (2.0 > 1) \n" + "=================================";
		TestUtil.typeCheckString(module);
	}

	@Test(expected = TypeErrorException.class)
	public void testRelationalOperatorsException3() throws
		TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "EXTENDS Reals \n"
			+ "CONSTANTS k, k2 \n"
			+ "ASSUME 1.0 = (2.0 > 1.0) \n" + "=================================";
		TestUtil.typeCheckString(module);
	}

	@Test
	public void testArithmeticOperators() throws TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "EXTENDS Reals \n"
			+ "ASSUME 2.0 = 1.0 + 1.0 \n"
			+ "=================================";
		TestUtil.typeCheckString(module);
	}

	@Test(expected = TypeErrorException.class)
	public void testArithmeticOperatorsException1() throws TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "EXTENDS Reals \n"
			+ "ASSUME TRUE = 1.0 + 1.0 \n"
			+ "=================================";
		TestUtil.typeCheckString(module);
	}

	@Test(expected = TypeErrorException.class)
	public void testArithmeticOperatorsException2() throws TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "EXTENDS Reals \n"
			+ "ASSUME 2.0 = 1.0 + 1 \n"
			+ "=================================";
		TestUtil.typeCheckString(module);
	}

	@Test(expected = TypeErrorException.class)
	public void testArithmeticOperatorsException3() throws TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "EXTENDS Reals \n"
			+ "ASSUME 2 = 1.0 + 1.0 \n"
			+ "=================================";
		TestUtil.typeCheckString(module);
	}

	@Test
	public void testRealDivision() throws TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "EXTENDS Reals \n"
			+ "CONSTANTS k \n"
			+ "ASSUME k = 1.0 / 1.0 \n"
			+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("REAL", t.getConstantType("k"));
	}

	/*
	 * Interval operator: x .. y
	 */
	@Test(expected = TypeErrorException.class)
	public void testDotDotReal() throws TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "EXTENDS Reals \n"
			+ "CONSTANTS k \n"
			+ "ASSUME k = 1.0 .. 3.0 \n"
			+ "=================================";
		TestUtil.typeCheckString(module);
	}
}
