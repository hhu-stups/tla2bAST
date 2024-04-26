package de.tla2b.typechecking.standardmodules;

import static org.junit.Assert.assertEquals;

import org.junit.Test;

import de.tla2b.exceptions.FrontEndException;
import de.tla2b.exceptions.TLA2BException;
import de.tla2b.exceptions.TypeErrorException;
import de.tla2b.util.TestTypeChecker;
import de.tla2b.util.TestUtil;


public class TestModuleNaturals {

	/*
	 * Relational operators: >, <, <=, >=
	 */
	@Test
	public void testRelationalOperators() throws
		TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "CONSTANTS k, k2, k3 \n"
				+ "ASSUME k = (k2 > k3) \n"
				+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("BOOL", t.getConstantType("k"));
		assertEquals("INTEGER", t.getConstantType("k2"));
		assertEquals("INTEGER", t.getConstantType("k2"));
	}

	@Test(expected = TypeErrorException.class)
	public void testRelationalOperatorsException() throws
		TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "CONSTANTS k, k2 \n"
				+ "ASSUME 1 = (2 > 1) \n" + "=================================";
		TestUtil.typeCheckString(module);
	}

	/*
	 * Arithmetic operator: +, -, *, /, mod, exp
	 */
	@Test
	public void testArithmeticOperators() throws
		TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "CONSTANTS k, k2, k3 \n"
				+ "ASSUME k = k2 + k3 \n" + "=================================";

		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("INTEGER", t.getConstantType("k"));
		assertEquals("INTEGER", t.getConstantType("k2"));
		assertEquals("INTEGER", t.getConstantType("k3"));
	}

	@Test(expected = TypeErrorException.class)
	public void testArithmeticOperatorsException() throws
		TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "CONSTANTS k, k2 \n"
				+ "ASSUME TRUE = 1 + 1 \n"
				+ "=================================";
		TestUtil.typeCheckString(module);
	}

	/*
	 * Interval operator: x .. y
	 */

	@Test
	public void testDotDot() throws TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "CONSTANTS k, k2, k3 \n"
				+ "ASSUME k = k2 .. k3 \n"
				+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("POW(INTEGER)", t.getConstantType("k"));
		assertEquals("INTEGER", t.getConstantType("k2"));
		assertEquals("INTEGER", t.getConstantType("k3"));
	}

	@Test(expected = TypeErrorException.class)
	public void testDotDotException() throws TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "CONSTANTS  k2, k3 \n"
				+ "ASSUME TRUE \\in  k2 .. k3 \n"
				+ "=================================";
		TestUtil.typeCheckString(module);
	}

	/*
	 * Nat
	 */
	@Test
	public void testNat() throws TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "CONSTANTS k \n"
				+ "ASSUME k = Nat \n" + "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("POW(INTEGER)", t.getConstantType("k"));
	}

	@Test(expected = TypeErrorException.class)
	public void unifyErrorNat() throws TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "ASSUME TRUE \\in Nat \n"
				+ "=================================";
		TestUtil.typeCheckString(module);
	}

}
