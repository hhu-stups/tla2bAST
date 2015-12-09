/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package de.tla2b.prettyprintb;

import static de.tla2b.util.TestUtil.compare;

import org.junit.Test;

public class SetsTest {

	@Test
	public void testSetEnumeration() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k\n"
				+ "ASSUME k = {1,2,3}\n"
				+ "=================================";

		final String expected = "MACHINE Testing\n" + "CONSTANTS k\n"
				+ "PROPERTIES k : POW(INTEGER) & k = {1,2,3} \n" + "END";
		compare(expected, module);
	}

	@Test
	public void testSetEnumeration2() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k\n"
				+ "ASSUME k = {TRUE, 1 = 1}\n"
				+ "=================================";

		final String expected = "MACHINE Testing\n" + "CONSTANTS k\n"
				+ "PROPERTIES k : POW(BOOL) & k = {TRUE, bool(1=1)} \n" + "END";
		compare(expected, module);
	}

	/**********************************************************************
	 * Element of: \in, \notin
	 **********************************************************************/
	@Test
	public void testMemberOf() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "ASSUME TRUE \\in BOOLEAN \n"
				+ "=================================";

		final String expected = "MACHINE Testing\n"
				+ "PROPERTIES TRUE : BOOL \n" + "END";
		compare(expected, module);
	}

	@Test
	public void testMemberOf2() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "ASSUME 1 \\in {1,2,3} \n"
				+ "=================================";
		final String expected = "MACHINE Testing\n"
				+ "PROPERTIES 1 : {1,2,3} \n" + "END";
		compare(expected, module);
	}

	@Test
	public void testNotMemberOf() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "ASSUME 1 \\notin {} \n"
				+ "=================================";
		final String expected = "MACHINE Testing\n" + "PROPERTIES 1 /: {} \n"
				+ "END";
		compare(expected, module);
	}

	/**********************************************************************
	 * set operators like difference, union, intersection: \setdiff, \cup, \cap
	 **********************************************************************/
	@Test
	public void testSetDifference() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "ASSUME {1} = {1,2} \\ {1} \n"
				+ "=================================";

		final String expected = "MACHINE Testing\n"
				+ "PROPERTIES {1} = {1,2} - {1} \n" + "END";
		compare(expected, module);
	}

	@Test
	public void testCup() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "ASSUME {1,2} = {1} \\cup {2} \n"
				+ "=================================";

		final String expected = "MACHINE Testing\n"
				+ "PROPERTIES {1,2} = {1} \\/ {2} \n" + "END";
		compare(expected, module);
		}

	@Test
	public void testCap() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "ASSUME {1} = {1,2} \\cap {2} \n"
				+ "=================================";

		final String expected = "MACHINE Testing\n"
				+ "PROPERTIES {1} = {1,2} /\\ {2} \n" + "END";
		compare(expected, module);
	}

	/**********************************************************************
	 * Subseteq: subset or equal
	 **********************************************************************/
	@Test
	public void testSubsteq() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "ASSUME TRUE = ({1} \\subseteq {1,2}) \n"
				+ "=================================";

		final String expected = "MACHINE Testing\n"
				+ "PROPERTIES TRUE = bool({1} <: {1,2}) \n" + "END";
		compare(expected, module);
	}

	/**********************************************************************
	 * SUBSET: conforms POW in B
	 **********************************************************************/
	@Test
	public void testSubset() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "ASSUME {{},{1}} = SUBSET {1,2} \n"
				+ "=================================";

		final String expected = "MACHINE Testing\n"
				+ "PROPERTIES {{},{1}} = POW({1,2}) \n" + "END";
		compare(expected, module);
	}

	/**********************************************************************
	 * UNION
	 **********************************************************************/
	@Test
	public void testUnion() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "ASSUME UNION {{1},{2}} = {1,2} \n"
				+ "=================================";

		final String expected = "MACHINE Testing\n"
				+ "PROPERTIES union({{1},{2}}) = {1,2} \n" + "END";
		compare(expected, module);
	}
	 
	/**********************************************************************
	* Set Constructor
	 **********************************************************************/
	@Test
	public void testConstructor1() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "ASSUME {x \\in {1,2} : x = 1} = {1} \n"
				+ "=================================";

		final String expected = "MACHINE Testing\n"
				+ "PROPERTIES {x | x : {1,2} & x = 1} = {1} \n" + "END";
		compare(expected, module);
	}
	
	@Test
	public void testConstructor1Tuple() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "ASSUME {<<a,b>> \\in {<<1,2>>} : a = 1 /\\ b = 2} = {<<1,2>>} \n"
				+ "=================================";

		final String expected = "MACHINE Testing\n"
				+ "PROPERTIES {a,b | (a,b) : {(1,2)} & (a = 1 & b = 2)} = {(1,2)} \n" + "END";
		compare(expected, module);
	}
	
	@Test
	public void testConstructor1Tuple3Elements() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "ASSUME {<<a,b,c>> \\in {<<1,2,3>>} : a = 1 /\\ b = 2} = {<<1,2,3>>} \n"
				+ "=================================";

		final String expected = "MACHINE Testing\n"
				+ "PROPERTIES {a,b,c | (a,b,c) : {(1,2,3)} & (a = 1 & b = 2)} = {(1,2,3)} \n" + "END";
		compare(expected, module);
	}


	@Test
	public void testConstructor2Simple() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "ASSUME  {x + x :  x \\in {1}} = {2} \n"
				+ "=================================";
		final String expected = "MACHINE Testing\n"
				+ "PROPERTIES UNION(x).(x : {1}| {x + x}) = {2} \n"
				+ "END";
		compare(expected, module);
	}
	
	@Test
	public void testConstructor2() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "ASSUME  {x + y:  x \\in {1}, y \\in {2} } = {3} \n"
				+ "=================================";
		final String expected = "MACHINE Testing\n"
				+ "PROPERTIES UNION(x,y).(x : {1} & y : {2} | {x+y}) = {3} \n"
				+ "END";
		compare(expected, module);
	}
	
	@Test
	public void testConstructor2Tuple() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "ASSUME  {x + y:  <<x,y>> \\in {<<1,2>>}} = {3} \n"
				+ "=================================";
		final String expected = "MACHINE Testing\n"
				+ "PROPERTIES UNION(x,y).((x|->y) : {(1|->2)} | {x + y}) = {3} \n"
				+ "END";
		compare(expected, module);
	}
}
