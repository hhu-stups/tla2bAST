/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package de.tla2b.prettyprintb.standardmodules;

import static de.tla2b.util.TestUtil.compare;
import static org.junit.Assert.assertEquals;

import org.junit.Test;

import de.tla2b.util.TestUtil;


public class TestModuleNaturals {

	/**********************************************************************
	 *  >, <, <=, >=
	 **********************************************************************/
	
	@Test
	public void testCompareOperators() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "ASSUME 1 < 2 /\\ 2 > 1 /\\ 1 <= 1 /\\ 1 >= 1 \n"
				+ "=================================";
		final String expected = "MACHINE Testing\n"
				+ "PROPERTIES 1 < 2 & 2 > 1 & 1 <= 1 & 1 >= 1 \n" + "END";
		compare(expected, module);
	}

	@Test
	public void testCompareOperators2() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "ASSUME (1 < 2) = (2 > 1) /\\ (1 <= 1) = (1 >= 1) \n"
				+ "=================================";

		final String expected = "MACHINE Testing\n"
				+ "PROPERTIES bool(1 < 2) = bool(2 > 1) & bool(1 <= 1) = bool(1 >= 1) \n"
				+ "END";
		compare(expected, module);
	}

	/**********************************************************************
	 * Arithmetic operator: +, -, *, \div, %, ^
	 **********************************************************************/
	@Test
	public void testArithmeticOperators() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "ASSUME 1 + 2 = 4-1 /\\ 1 * 2 = 4 \\div 2 /\\  1 ^ 1 = 1 \n"
				+ "=================================";
		final String expected = "MACHINE Testing\n"
				+ "PROPERTIES 1 + 2 = 4 - 1 & 1 * 2 = 4 / 2 & 1 ** 1 = 1 \n"
				+ "END";
		compare(expected, module);
	}

	/**********************************************************************
	 * Interval operator: x .. y 
	 **********************************************************************/
	@Test
	public void testDotDot() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "ASSUME 1 \\in 1 .. 2 \n"
				+ "=================================";
		final String expected = "MACHINE Testing\n"
				+ "PROPERTIES 1 : 1..2 \n"
				+ "END";
		compare(expected, module);
	}

	@Test
	public void testNat() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "ASSUME 1 \\in Nat \n"
				+ "=================================";
		final String expected = "MACHINE Testing\n"
				+ "PROPERTIES 1 : NATURAL \n"
				+ "END";
		compare(expected, module);
	}
	
	@Test
	public void testMod() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals, Integers \n"
				+ "ASSUME -3 % 2 = 1 \n"
				+ "=================================";
		final String expected = "MACHINE Testing\n"
				+ "PROPERTIES -3 - 2 * (-3 / 2) = 1 \n"
				+ "END";
		compare(expected, module);
	}
	
}
