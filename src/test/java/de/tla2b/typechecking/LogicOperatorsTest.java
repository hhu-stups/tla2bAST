package de.tla2b.typechecking;

import static org.junit.Assert.*;

import org.junit.Test;

import de.tla2b.exceptions.TLA2BException;
import de.tla2b.exceptions.TypeErrorException;
import de.tla2b.util.TestTypeChecker;
import de.tla2b.util.TestUtil;


public class LogicOperatorsTest {
	
	/*
	 * equality and disequality: =, #,
	 */
	@Test
	public void testEquality() throws TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2\n"
				+ "ASSUME k = (k2 = 1)\n"
				+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("BOOL", t.getConstantType("k"));
		assertEquals("INTEGER", t.getConstantType("k2"));
	}
	
	@Test (expected = TypeErrorException.class)
	public void testEqualityError() throws TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "ASSUME 1 = TRUE\n"
				+ "=================================";
		TestUtil.typeCheckString(module);
	}
	@Test (expected = TypeErrorException.class)
	public void testEqualityError2() throws TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "ASSUME 1 = (1=1)\n"
				+ "=================================";
		TestUtil.typeCheckString(module);
	}
	
	
	
	/*
	 * Logic Operators: \neg, \lnot, \land, \cl, \lor, \dl, \equiv, =>
	 */
	@Test
	public void testLogicOperators() throws TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2, k3\n"
				+ "ASSUME k = (k2 \\land k3) \n"
				+ "=================================";
		
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("BOOL", t.getConstantType("k"));
		assertEquals("BOOL", t.getConstantType("k2"));
		assertEquals("BOOL", t.getConstantType("k3"));
	}
	
	@Test (expected = TypeErrorException.class)
	public void testLogicOperatorsError() throws TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2, k3\n"
				+ "ASSUME 1 = (k2 \\land k3) \n"
				+ "=================================";
		TestUtil.typeCheckString(module);
	}
	
	/*
	 * Quantification: \A x \in S : P or \E x \in S : P.  
	 */

	
	@Test 
	public void testQuantification() throws TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2, S\n"
				+ "ASSUME k = (\\A x \\in S : x = k2) /\\ k2 = 1 \n"
				+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("BOOL", t.getConstantType("k"));
		assertEquals("INTEGER", t.getConstantType("k2"));
		assertEquals("POW(INTEGER)", t.getConstantType("S"));
	}
	
	@Test(expected = TypeErrorException.class)
	public void testQuantificationException() throws TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "ASSUME \\A <<x,y>> \\in {1} : TRUE \n"
				+ "=================================";
		TestUtil.typeCheckString(module);
	}
}
