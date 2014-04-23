/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package de.tla2b.prettyprintb;

import static de.tla2b.util.TestUtil.compare;

import org.junit.Ignore;
import org.junit.Test;

import util.ToolIO;

public class RecordTest {
	static {
		ToolIO.setMode(ToolIO.TOOL);
	}

	/**********************************************************************
	 * Set of Records: [L1 : e1, L2 : e2]
	 **********************************************************************/
	@Test
	public void testStruct() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k \n"
				+ "ASSUME k = [a : {1}, b : BOOLEAN] \n"
				+ "=================================";

		final String expected = "MACHINE Testing\n"
				+ "ABSTRACT_CONSTANTS k\n"
				+ "PROPERTIES k : POW(struct(a:INTEGER, b:BOOL)) & k = struct(a : {1}, b : BOOL) \n"
				+ "END";
		compare(expected, module);
	}
	
	
	@Test
	public void testStructExpansion() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "ASSUME [a: {2}] = [a : {1}, b : BOOLEAN] \n"
				+ "=================================";

		final String expected = "MACHINE Testing\n"
				+ "PROPERTIES struct(a : {2},b : BOOL) = struct(a : {1},b : BOOL) \n"
				+ "END";
		compare(expected, module);
	}

	/**********************************************************************
	 * Record: [L1 |-> e1, L2 |-> e2]
	 **********************************************************************/
	@Test
	public void testRecord() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k \n"
				+ "ASSUME k = [a |-> 1, b |-> TRUE] \n"
				+ "=================================";

		final String expected = "MACHINE Testing\n"
				+ "ABSTRACT_CONSTANTS k\n"
				+ "PROPERTIES k : struct(a:INTEGER, b:BOOL) & k = rec(a : 1, b : TRUE) \n"
				+ "END";
		compare(expected, module);
	}
	
	
	@Ignore
	@Test
	public void testRecordExpansion() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "ASSUME [a|-> 2] = [a |-> 1, b |-> \"abc\"] \n"
				+ "=================================";

		final String expected = "MACHINE Testing\n"
				+ "PROPERTIES rec(a : 2,b : \"\") = rec(a : 1,b : \"abc\") \n"
				+ "END";
		compare(expected, module);
	}

	/**********************************************************************
	 * Record Select: r.c
	 **********************************************************************/
	@Test
	public void testRecordSelect() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "ASSUME [a |-> 1, b |-> TRUE].a = 1 \n"
				+ "=================================";

		final String expected = "MACHINE Testing\n"
				+ "PROPERTIES rec(a : 1, b : TRUE)'a = 1\n"
				+ "END";
		compare(expected, module);
	}
	
	@Test
	public void testRecordSelect2() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k \n"
				+ "ASSUME k = [a |-> 1, b |-> TRUE] /\\ k.b \n"
				+ "=================================";

		final String expected = "MACHINE Testing\n"
				+ "ABSTRACT_CONSTANTS k\n"
				+ "PROPERTIES k : struct(a:INTEGER, b:BOOL) & (k = rec(a : 1, b : TRUE) & k'b = TRUE) \n"
				+ "END";
		compare(expected, module);
	}

	/**********************************************************************
	 * Record Except
	 **********************************************************************/
	@Test
	public void testRecordExcept() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k, k2 \n"
				+ "ASSUME k = [a |-> 1, b |-> TRUE] /\\ k2 = [k EXCEPT !.a = 2] \n"
				+ "=================================";
		final String expected = "MACHINE Testing\n"
				+ "ABSTRACT_CONSTANTS k, k2\n"
				+ "PROPERTIES k : struct(a:INTEGER, b:BOOL) & k2 : struct(a:INTEGER, b:BOOL) & (k = rec(a : 1, b : TRUE) & k2 = rec(a : 2, b : k'b)) \n"
				+ "END";
		compare(expected, module);
	}

	/**********************************************************************
	 * Record Except @
	 **********************************************************************/
	@Test
	public void testRecordExceptAt() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "CONSTANTS k, k2 \n"
				+ "ASSUME k = [a |-> 1, b |-> TRUE] /\\ k2 = [k EXCEPT !.a = @ + 1] \n"
				+ "=================================";

		final String expected = "MACHINE Testing\n"
				+ "ABSTRACT_CONSTANTS k, k2\n"
				+ "PROPERTIES k : struct(a:INTEGER, b:BOOL) & k2 : struct(a:INTEGER, b:BOOL) & (k = rec(a : 1, b : TRUE) & k2 = rec(a : k'a + 1, b : k'b)) \n"
				+ "END";
		compare(expected, module);
	}

}
