package de.tla2b.typechecking.standardmodules;

import de.tla2b.exceptions.TLA2BException;
import de.tla2b.util.TestTypeChecker;
import de.tla2b.util.TestUtil;
import org.junit.Test;

import static org.junit.Assert.assertEquals;


public class TestModuleTLC {

	/*
	 * a :> b : The function [x \in {a} |-> b]
	 */
	@Test
	public void testSingleton() throws TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "EXTENDS Naturals, TLC \n"
			+ "CONSTANTS k \n"
			+ "ASSUME k = 1 :> 2 \n"
			+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("POW(INTEGER*INTEGER)", t.getConstantType("k"));
	}

	/*
	 * func1 @@ func2 : Function merge. If two functions share the same key, uses the value from func1 (NOT func2).
	 */
	@Test
	public void testMerge() throws TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "EXTENDS Naturals, TLC \n"
			+ "CONSTANTS k1, k2, k3 \n"
			+ "ASSUME k1 = 1 :> 2 /\\ k2 = 1 :> 3 /\\ k3 = k1 @@ k2 \n"
			+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("POW(INTEGER*INTEGER)", t.getConstantType("k1"));
		assertEquals("POW(INTEGER*INTEGER)", t.getConstantType("k2"));
		assertEquals("POW(INTEGER*INTEGER)", t.getConstantType("k3"));
	}

	/*
	 * Combination of the previous operators to override one value of a function
	 */
	@Test
	public void testOverride() throws TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "EXTENDS Naturals, TLC \n"
			+ "CONSTANTS k1, k2 \n"
			+ "FuncAssign(f, d, e) ==  d :> e @@ f \n"
			+ "ASSUME k1 = 1 :> 2 /\\ k2 = FuncAssign(k1, 1, 3) \n"
			+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("POW(INTEGER*INTEGER)", t.getConstantType("k1"));
		assertEquals("POW(INTEGER*INTEGER)", t.getConstantType("k2"));
	}
}
