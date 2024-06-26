package de.tla2b.typechecking;

import de.tla2b.exceptions.TLA2BException;
import de.tla2b.exceptions.TypeErrorException;
import de.tla2b.util.TestTypeChecker;
import de.tla2b.util.TestUtil;
import org.junit.Test;

import static org.junit.Assert.assertEquals;

public class SetTest {

	/*
	 * Set Enumeration: {1,2,3}
	 */

	@Test
	public void testSetEnumeration() throws TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "CONSTANTS k, k2, k3\n"
			+ "ASSUME k = {k2, k3} /\\ k3 = 1\n"
			+ "=================================";

		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("POW(INTEGER)", t.getConstantType("k"));
		assertEquals("INTEGER", t.getConstantType("k2"));
		assertEquals("INTEGER", t.getConstantType("k3"));

	}

	@Test
	public void testSetEnumeration2() throws TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "CONSTANTS k, k2, k3\n"
			+ "ASSUME k = {k2, k3} /\\ k = {1}\n"
			+ "=================================";

		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("POW(INTEGER)", t.getConstantType("k"));
		assertEquals("INTEGER", t.getConstantType("k2"));
		assertEquals("INTEGER", t.getConstantType("k3"));
	}

	@Test
	public void testSetEnumeration3() throws TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "CONSTANTS k, k2, k3\n"
			+ "ASSUME k = {k2,{k3}} /\\ k3 = 1\n"
			+ "=================================";

		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("POW(POW(INTEGER))", t.getConstantType("k"));
		assertEquals("POW(INTEGER)", t.getConstantType("k2"));
		assertEquals("INTEGER", t.getConstantType("k3"));
	}

	@Test
	public void testSetEnumeration4() throws TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "CONSTANTS k, k2\n"
			+ "ASSUME k = {{1},{k2}}\n"
			+ "=================================";

		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("POW(POW(INTEGER))", t.getConstantType("k"));
		assertEquals("INTEGER", t.getConstantType("k2"));
	}

	@Test(expected = TypeErrorException.class)
	public void testSetEnumerationException() throws
		TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "CONSTANTS k, k2\n"
			+ "ASSUME k = {1, TRUE}\n"
			+ "=================================";

		TestUtil.typeCheckString(module);
	}

	@Test(expected = TypeErrorException.class)
	public void testSetEnumerationException2() throws
		TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "CONSTANTS k, k2\n"
			+ "ASSUME 1 = {1, 2}\n"
			+ "=================================";
		TestUtil.typeCheckString(module);
	}

	/*
	 * Element of: \in, \notin
	 */
	@Test
	public void testElementOfSet() throws TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "CONSTANTS k, k2\n"
			+ "ASSUME k \\in {k2} /\\ k2 = 1 \n"
			+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("INTEGER", t.getConstantType("k"));
		assertEquals("INTEGER", t.getConstantType("k2"));
	}

	@Test
	public void testElementOfSet2() throws TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "CONSTANTS k, k2\n"
			+ "ASSUME k \\in {k2} /\\ k = 1 \n"
			+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("INTEGER", t.getConstantType("k"));
		assertEquals("INTEGER", t.getConstantType("k2"));
	}

	@Test
	public void testElementOfSet3() throws TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "CONSTANTS k \n"
			+ "ASSUME k \\in {<<TRUE>>}\n"
			+ "=================================";

		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("POW(INTEGER*BOOL)", t.getConstantType("k"));
	}

	@Test(expected = TypeErrorException.class)
	public void testElementOfSetError() throws
		TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "ASSUME 1 = (1 \\in {1}) \n"
			+ "=================================";
		TestUtil.typeCheckString(module);
	}

	@Test(expected = TypeErrorException.class)
	public void testElementOfSetError2() throws
		TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "ASSUME 1 \\in 1 \n" + "=================================";
		TestUtil.typeCheckString(module);
	}

	/*
	 * set operators like difference, union, intersection
	 */
	@Test
	public void testSetOperators() throws TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "CONSTANTS k, k2, k3\n"
			+ "ASSUME k = (k2 \\cup k3) /\\ k3 = {1} \n"
			+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("POW(INTEGER)", t.getConstantType("k"));
		assertEquals("POW(INTEGER)", t.getConstantType("k2"));
		assertEquals("POW(INTEGER)", t.getConstantType("k3"));
	}

	@Test
	public void testSetOperators2() throws TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "CONSTANTS k, k2\n"
			+ "ASSUME k = (k \\cup k2) /\\ k2 = {1} \n"
			+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("POW(INTEGER)", t.getConstantType("k"));
		assertEquals("POW(INTEGER)", t.getConstantType("k2"));
	}

	@Test(expected = TypeErrorException.class)
	public void testSetOperatorsException() throws
		TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "CONSTANTS k, k2\n"
			+ "ASSUME 1 = k \\cup k2 \n"
			+ "=================================";
		TestUtil.typeCheckString(module);
	}

	@Test(expected = TypeErrorException.class)
	public void testSetOperatorsException2() throws
		TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "CONSTANTS k\n"
			+ "ASSUME k = {1} \\cup {TRUE} \n"
			+ "=================================";
		TestUtil.typeCheckString(module);
	}

	/*
	 * set constructor: {x \in S : p}.
	 */
	@Test
	public void testSubsetOf() throws TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "CONSTANTS k, S\n"
			+ "ASSUME k = {x \\in S : x = 1} \n"
			+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("POW(INTEGER)", t.getConstantType("k"));
		assertEquals("POW(INTEGER)", t.getConstantType("S"));
	}

	@Test
	public void testSubsetOf2() throws TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "CONSTANTS k, k2\n"
			+ "ASSUME k = {x \\in {TRUE} : x = k2} \n"
			+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("POW(BOOL)", t.getConstantType("k"));
		assertEquals("BOOL", t.getConstantType("k2"));
	}

	@Test
	public void testSubsetOf3() throws TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "CONSTANTS k, S, k2\n"
			+ "ASSUME k = {x \\in S : x = k2} /\\ k2 = TRUE \n"
			+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("POW(BOOL)", t.getConstantType("k"));
		assertEquals("POW(BOOL)", t.getConstantType("S"));
		assertEquals("BOOL", t.getConstantType("k2"));
	}

	@Test
	public void testSubsetOf4() throws TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "CONSTANTS k, S\n"
			+ "ASSUME k = {x \\in S : TRUE} /\\ k = {TRUE} \n"
			+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("POW(BOOL)", t.getConstantType("k"));
		assertEquals("POW(BOOL)", t.getConstantType("S"));
	}

	@Test(expected = TypeErrorException.class)
	public void testSubsetOfException() throws
		TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "CONSTANTS k\n"
			+ "ASSUME k = {<<x,y>> \\in {TRUE} : TRUE} \n"
			+ "=================================";
		TestUtil.typeCheckString(module);
	}

	@Test(expected = TypeErrorException.class)
	public void testSubsetOfException2() throws
		TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "CONSTANTS k\n"
			+ "ASSUME k = {x \\in 1 : TRUE} \n"
			+ "=================================";
		TestUtil.typeCheckString(module);
	}

	@Test(expected = TypeErrorException.class)
	public void testSubsetOfException3() throws
		TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "CONSTANTS k\n"
			+ "ASSUME k = {x \\in {} : 1 = 1} \n"
			+ "=================================";
		TestUtil.typeCheckString(module);
	}

	@Test
	public void testSubsetOfTuple() throws
		TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "CONSTANTS k\n"
			+ "ASSUME k = {<<x,y>> \\in {1} \\times {TRUE} : TRUE} \n"
			+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("POW(INTEGER*BOOL)", t.getConstantType("k"));
	}

	@Test
	public void testSubsetOfTuple2() throws
		TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "CONSTANTS k, S, S2\n"
			+ "ASSUME k = {<<x,y>> \\in S \\times S2 : x = 1 /\\ y = TRUE} \n"
			+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("POW(INTEGER*BOOL)", t.getConstantType("k"));
		assertEquals("POW(INTEGER)", t.getConstantType("S"));
		assertEquals("POW(BOOL)", t.getConstantType("S2"));
	}

	@Test
	public void testSubsetOfTuple3() throws
		TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "CONSTANTS k, S\n"
			+ "ASSUME k = {<<x,y>> \\in S : x = 1 /\\ y = TRUE} \n"
			+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("POW(INTEGER*BOOL)", t.getConstantType("k"));
		assertEquals("POW(INTEGER*BOOL)", t.getConstantType("S"));
	}

	/*
	 * set constructor: {e : x \in S}
	 */
	@Test
	public void testSetOfAll() throws TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "CONSTANTS k, S, k2\n"
			+ "ASSUME k = {x = k2 : x \\in S} /\\ k2 = 1  \n"
			+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("POW(BOOL)", t.getConstantType("k"));
		assertEquals("POW(INTEGER)", t.getConstantType("S"));
		assertEquals("INTEGER", t.getConstantType("k2"));
	}

	@Test
	public void testSetOfAll2() throws TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "CONSTANTS k, S\n"
			+ "ASSUME k = {{x} : x \\in S} /\\ S = {1}  \n"
			+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("POW(POW(INTEGER))", t.getConstantType("k"));
		assertEquals("POW(INTEGER)", t.getConstantType("S"));
	}

	@Test
	public void testSetOfAll3() throws TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "CONSTANTS k, S, k2\n"
			+ "ASSUME k = { x = y /\\ y = k2 : x,y \\in S} /\\ k2 = 1 \n"
			+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("POW(BOOL)", t.getConstantType("k"));
		assertEquals("POW(INTEGER)", t.getConstantType("S"));
		assertEquals("INTEGER", t.getConstantType("k2"));
	}

	@Test
	public void testSetOfAll4() throws TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "CONSTANTS k, S, S2, k2, k3\n"
			+ "ASSUME k = { x = k2 /\\ y /\\ z = k3 : x \\in S, y,z \\in S2 } /\\ k2 = TRUE \n"
			+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("POW(BOOL)", t.getConstantType("k"));
		assertEquals("POW(BOOL)", t.getConstantType("S"));
		assertEquals("BOOL", t.getConstantType("k2"));
		assertEquals("BOOL", t.getConstantType("k3"));
	}

	@Test(expected = TypeErrorException.class)
	public void testSetOfAllException() throws
		TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "CONSTANTS k, S\n"
			+ "ASSUME 1 = {x : x \\in S} \n"
			+ "=================================";
		TestUtil.typeCheckString(module);
	}

	@Test(expected = TypeErrorException.class)
	public void testSetOfAllException2() throws
		TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "CONSTANTS k, S\n"
			+ "ASSUME k = {x : x \\in 1} \n"
			+ "=================================";
		TestUtil.typeCheckString(module);
	}

	@Test(expected = TypeErrorException.class)
	public void testSetOfAllException3() throws
		TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "CONSTANTS k, S\n"
			+ "ASSUME k = {x : <<x,y>> \\in S} \n"
			+ "=================================";
		TestUtil.typeCheckString(module);
	}

	/*
	 * SUBSET: conforms POW in B
	 */
	@Test
	public void testSubset() throws TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "CONSTANTS k, k2 \n"
			+ "ASSUME k = SUBSET k2 /\\ k2 = 1 \n"
			+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("POW(INTEGER)", t.getConstantType("k"));
		assertEquals("INTEGER", t.getConstantType("k2"));
	}

	@Test
	public void testSubset2() throws TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "CONSTANTS k, k2 \n"
			+ "ASSUME k = SUBSET k2 /\\ k = {1} \n"
			+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("POW(INTEGER)", t.getConstantType("k"));
		assertEquals("INTEGER", t.getConstantType("k2"));
	}

	@Test(expected = TypeErrorException.class)
	public void testSubsetException() throws TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "CONSTANTS k \n"
			+ "ASSUME 1 = SUBSET k \n"
			+ "=================================";
		TestUtil.typeCheckString(module);
	}

	/*
	 * UNION
	 */
	@Test
	public void testUnion() throws TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "CONSTANTS k, k2 \n"
			+ "ASSUME k = UNION k2 /\\ k = {1} \n"
			+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("POW(INTEGER)", t.getConstantType("k"));
		assertEquals("POW(POW(INTEGER))", t.getConstantType("k2"));
	}

	@Test
	public void testUnion2() throws TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "CONSTANTS k, k2 \n"
			+ "ASSUME k = UNION k2 /\\ k2 = {{1},{2}} \n"
			+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("POW(INTEGER)", t.getConstantType("k"));
		assertEquals("POW(POW(INTEGER))", t.getConstantType("k2"));
	}

	@Test(expected = TypeErrorException.class)
	public void testUnionException() throws TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "CONSTANTS k, k2 \n"
			+ "ASSUME k = UNION k2 /\\ k = 1 \n"
			+ "=================================";
		TestUtil.typeCheckString(module);
	}

	@Test(expected = TypeErrorException.class)
	public void testUnionException2() throws TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "CONSTANTS k, k2 \n"
			+ "ASSUME k = UNION k2 /\\ k2 = {1,2} \n"
			+ "=================================";
		TestUtil.typeCheckString(module);
	}

	/*
	 * Subseteq: subset or equal
	 */
	@Test
	public void testSubseteq() throws TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "CONSTANTS k, k2, k3 \n"
			+ "ASSUME k = (k2 \\subseteq k3) /\\ k3 = {1}  \n"
			+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("BOOL", t.getConstantType("k"));
		assertEquals("POW(INTEGER)", t.getConstantType("k2"));
		assertEquals("POW(INTEGER)", t.getConstantType("k3"));
	}

	@Test(expected = TypeErrorException.class)
	public void testSubseteqException() throws
		TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "CONSTANTS k, k2 \n"
			+ "ASSUME k = (k2 \\subseteq 1)  \n"
			+ "=================================";
		TestUtil.typeCheckString(module);
	}

	@Test(expected = TypeErrorException.class)
	public void testSubseteqException2() throws
		TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "CONSTANTS k, k2 \n"
			+ "ASSUME 1 = (k \\subseteq k2)  \n"
			+ "=================================";
		TestUtil.typeCheckString(module);
	}

}
