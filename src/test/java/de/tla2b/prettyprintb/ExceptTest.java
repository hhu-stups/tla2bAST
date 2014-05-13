package de.tla2b.prettyprintb;

import static de.tla2b.util.TestUtil.compare;
import static org.junit.Assert.assertEquals;

import org.junit.Ignore;
import org.junit.Test;

import util.ToolIO;
import de.tla2b.util.TestUtil;

public class ExceptTest {

	@Test
	public void testFunctionExcept() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k \n"
				+ "ASSUME k = [k EXCEPT ![TRUE] = 0, ![FALSE] = 0]  \n"
				+ "=================================";

		final String expected = "MACHINE Testing\n" + "ABSTRACT_CONSTANTS k\n"
				+ "PROPERTIES " + " k : BOOL +-> INTEGER "
				+ "& k = k <+ {TRUE |-> 0, FALSE |-> 0}" + "END";
		compare(expected, module);
	}

	@Test
	public void testFunctionExcept2() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k \n"
				+ "ASSUME k = [k EXCEPT ![TRUE] = 0, ![FALSE] = 0]  \n"
				+ "=================================";

		final String expected = "MACHINE Testing\n" + "ABSTRACT_CONSTANTS k\n"
				+ "PROPERTIES " + " k : BOOL +-> INTEGER "
				+ "& k = k <+ {TRUE |-> 0, FALSE |-> 0}" + "END";
		compare(expected, module);

	}

	@Test
	public void testFunctionExceptAt() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "CONSTANTS k \n"
				+ "ASSUME k = [x \\in {1,2} |-> x] /\\ [k EXCEPT ![1] = @ + 1][1] = 2 \n"
				+ "=================================";

		final String expected = "MACHINE Testing\n"
				+ "ABSTRACT_CONSTANTS k \n"
				+ "PROPERTIES k : INTEGER +-> INTEGER & (k = %x.(x : {1, 2}| x) & (k <+ {1 |-> k(1) + 1})(1) = 2)\n"
				+ "END";
		compare(expected, module);
	}

	@Ignore
	@Test
	public void testFunctionExceptAt2() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "CONSTANTS k, k2 \n"
				+ "ASSUME k = [x,y \\in {1,2} |-> x+y] /\\ k2 = [k EXCEPT ![1,1] = @ + 4] \n"
				+ "=================================";

		final String expected = "MACHINE Testing\n"
				+ "ABSTRACT_CONSTANTS k, k2\n"
				+ "PROPERTIES  k : POW(INTEGER*INTEGER*INTEGER) "
				+ "&  k2 : POW(INTEGER*INTEGER*INTEGER) "
				+ "& k = %x,y.(x : {1, 2} & y : {1, 2}| x + y) "
				+ "& k2 = k <+ {(1, 1) |-> k(1, 1) + 4} \n" + "END";
	}
}
