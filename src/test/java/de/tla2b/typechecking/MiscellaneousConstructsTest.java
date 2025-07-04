package de.tla2b.typechecking;

import de.tla2b.exceptions.TLA2BException;
import de.tla2b.util.TestTypeChecker;
import de.tla2b.util.TestUtil;
import org.junit.Test;

import static org.junit.Assert.assertEquals;


public class MiscellaneousConstructsTest {

	/*
	 * IF THEN ELSE
	 */
	@Test
	public void testIfThenElse() throws TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "CONSTANTS k, k2, k3, k4 \n"
			+ "ASSUME k = (IF k2 THEN k3 ELSE k4) /\\ k4 = 1  \n"
			+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("INTEGER", t.getConstantType("k"));
		assertEquals("BOOL", t.getConstantType("k2"));
		assertEquals("INTEGER", t.getConstantType("k3"));
		assertEquals("INTEGER", t.getConstantType("k4"));
	}


	/*
	 * IF THEN ELSE
	 */
	@Test
	public void testCase() throws TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "CONSTANTS k, k2, k3, e1, e2 \n"
			+ "ASSUME k = (CASE k2 -> e1 [] k3 -> e2) /\\ e2 = 1  \n"
			+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("INTEGER", t.getConstantType("k"));
		assertEquals("BOOL", t.getConstantType("k2"));
		assertEquals("BOOL", t.getConstantType("k3"));
		assertEquals("INTEGER", t.getConstantType("e1"));
		assertEquals("INTEGER", t.getConstantType("e2"));
	}

	@Test
	public void testCase2() throws TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "CONSTANTS k, k2, k3, e1, e2, e3 \n"
			+ "ASSUME k = (CASE k2 -> e1 [] k3 -> e2 [] OTHER -> e3) /\\ e2 = 1  \n"
			+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("INTEGER", t.getConstantType("k"));
		assertEquals("BOOL", t.getConstantType("k2"));
		assertEquals("BOOL", t.getConstantType("k3"));
		assertEquals("INTEGER", t.getConstantType("e1"));
		assertEquals("INTEGER", t.getConstantType("e2"));
		assertEquals("INTEGER", t.getConstantType("e3"));
	}

	/*
	 * LET d == exp IN e
	 */
	@Test
	public void testLetIn() throws TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "CONSTANTS k, k2, k3 \n"
			+ "ASSUME k = (LET d == k2 IN d = k3) /\\ k2 = 1  \n"
			+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("BOOL", t.getConstantType("k"));
		assertEquals("INTEGER", t.getConstantType("k2"));
		assertEquals("INTEGER", t.getConstantType("k3"));
	}

	@Test
	public void testLetIn2() throws TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "CONSTANTS k, k2, k3 \n"
			+ "ASSUME k = (LET d == k2 d2 == k3 IN d = d2) /\\ k2 = 1  \n"
			+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("BOOL", t.getConstantType("k"));
		assertEquals("INTEGER", t.getConstantType("k2"));
		assertEquals("INTEGER", t.getConstantType("k3"));
	}

	@Test
	public void testLetIn3() throws TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "CONSTANTS k, k2, k3, k4 \n"
			+ "ASSUME k = (LET d(a,b) == a=k2/\\b=k3 IN d(1,k4)) /\\ k4 = TRUE  \n"
			+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("BOOL", t.getConstantType("k"));
		assertEquals("INTEGER", t.getConstantType("k2"));
		assertEquals("BOOL", t.getConstantType("k3"));
		assertEquals("BOOL", t.getConstantType("k4"));
	}

	@Test
	public void testBoundedChoose() throws TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "CONSTANTS k \n"
			+ "ASSUME k = CHOOSE x \\in {1}: TRUE  \n"
			+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("INTEGER", t.getConstantType("k"));
	}

	@Test
	public void testUnboundedChoose() throws TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "CONSTANTS k \n"
			+ "ASSUME k = CHOOSE x : x = 1  \n"
			+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("INTEGER", t.getConstantType("k"));
	}

	@Test
	public void testUnboundedChooseTuple() throws TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "CONSTANTS k \n"
			+ "ASSUME k = CHOOSE <<a,b>> : <<a,b>> = <<1,TRUE>>  \n"
			+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("INTEGER*BOOL", t.getConstantType("k"));
	}

	@Test
	public void testBoundedChooseTuple() throws TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "CONSTANTS k \n"
			+ "ASSUME k = CHOOSE <<a,b>> \\in {<<1,TRUE>>}: TRUE  \n"
			+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("INTEGER*BOOL", t.getConstantType("k"));
	}

	@Test
	public void testRelParFuncEleOf() throws TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "EXTENDS FiniteSets, Integers \n"
			+ "CONSTANTS k \n"
			+ "RelParFuncEleOf(S, T) == {f \\in SUBSET (S \\times T): Cardinality({ x[1] :x \\in f}) = Cardinality(f)} \n"
			+ "ASSUME k \\in RelParFuncEleOf(Int, BOOLEAN) \n"
			+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("POW(INTEGER*BOOL)", t.getConstantType("k"));
	}
}
