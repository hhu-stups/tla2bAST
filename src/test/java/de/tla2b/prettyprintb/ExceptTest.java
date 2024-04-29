package de.tla2b.prettyprintb;

import org.junit.Ignore;
import org.junit.Test;
import util.ToolIO;

import static de.tla2b.util.TestUtil.compare;

public class ExceptTest {

	@Test
	public void testFunctionExcept() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "CONSTANTS k \n"
			+ "ASSUME k = [k EXCEPT ![TRUE] = 0, ![FALSE] = 0]  \n"
			+ "=================================";

		final String expected = "MACHINE Testing\n" + "CONSTANTS k\n"
			+ "PROPERTIES "
			+ "k : BOOL +-> INTEGER & k = (k <+ {(TRUE,0)}) <+ {(FALSE,0)} \n "
			+ "END";
		compare(expected, module);
	}

	@Test
	public void testFunctionExcept2() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "EXTENDS Naturals \n"
			+ "CONSTANTS k, k2 \n"
			+ "ASSUME k = [i \\in {3} |-> i] /\\ k2 = [k EXCEPT ![3] = @+1, ![3] = @+1]  \n"
			+ "=================================";

		final String expected = "MACHINE Testing\n"
			+ "CONSTANTS k, k2\n"
			+ "PROPERTIES "
			+ "(k : INTEGER +-> INTEGER & k2 : INTEGER +-> INTEGER) & (k = %(i).(i : {3} | i) & k2 = (k <+ {(3,k(3) + 1)}) <+ {(3,(k <+ {(3,k(3) + 1)})(3) + 1)}) \n "
			+ "END";
		compare(expected, module);
	}

	@Test
	public void testFunctionAt() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "EXTENDS Naturals \n"
			+ "CONSTANTS k \n"
			+ "ASSUME k = [i \\in {3,4} |-> i] /\\ k # [k EXCEPT ![3] = @ + 1]  \n"
			+ "=================================";

		final String expected = "MACHINE Testing\n" + "CONSTANTS k\n"
			+ "PROPERTIES "
			+ "k : INTEGER +-> INTEGER & (k = %(i).(i : {3, 4} | i) & k /= k <+ {(3,k(3) + 1)}) \n"
			+ "END";
		compare(expected, module);
	}

	@Test
	public void testFunctionTuple() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "EXTENDS Naturals \n"
			+ "CONSTANTS k \n"
			+ "ASSUME k = [i \\in {3,4}, j \\in {5,6} |-> i+j] /\\ k # [k EXCEPT ![3,5] = 1]  \n"
			+ "=================================";

		final String expected = "MACHINE Testing\n" + "CONSTANTS k\n"
			+ "PROPERTIES "
			+ "k : INTEGER * INTEGER +-> INTEGER & (k = %(i, j).(i : {3, 4} & j : {5, 6} | i + j) & k /= k <+ {((3,5),1)}) \n"
			+ "END";
		compare(expected, module);
	}

	@Test
	public void testNestedFunctionAt() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "EXTENDS Naturals \n"
			+ "CONSTANTS k \n"
			+ "ASSUME k = [i \\in {TRUE} |-> <<5,6>>] /\\ k # [k EXCEPT ![TRUE][2] = @ + 1]  \n"
			+ "=================================";

		final String expected = "MACHINE Testing\n" + "CONSTANTS k\n"
			+ "PROPERTIES "
			+ "k : BOOL +-> (INTEGER +-> INTEGER) & (k = %(i).(i : {TRUE} | [5,6]) & k /= k <+ {(TRUE,k(TRUE) <+ {(2,(k(TRUE))(2) + 1)})}) \n"
			+ "END";
		compare(expected, module);
	}

	@Test
	public void testRecordExcept() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "CONSTANTS k \n"
			+ "ASSUME k = [a |-> 1, b |-> TRUE] /\\ k /= [k EXCEPT !.a = 2, !.b = FALSE]  \n"
			+ "=================================";

		final String expected = "MACHINE Testing\n" + "CONSTANTS k\n"
			+ "PROPERTIES "
			+ "k : struct(a:INTEGER, b:BOOL) & (k = rec(a:1, b:TRUE) & k /= rec(a:rec(a:2, b:k'b)'a, b:FALSE)) \n"
			+ "END";
		compare(expected, module);

	}

	@Test
	public void testRecordAt() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "EXTENDS Naturals \n"
			+ "CONSTANTS k, k2 \n"
			+ "ASSUME k = [a |-> 1, b |-> 1] /\\ k2 = [k EXCEPT !.b = @ + 1, !.b = @ + 1]  \n"
			+ "=================================";

		final String expected = "MACHINE Testing\n" + "CONSTANTS k, k2\n"
			+ "PROPERTIES "
			+ "(k : struct(a:INTEGER, b:INTEGER) & k2 : struct(a:INTEGER, b:INTEGER)) & (k = rec(a:1, b:1) & k2 = rec(a:rec(a:k'a, b:k'b + 1)'a, b:rec(a:k'a, b:k'b + 1)'b + 1)) \n"
			+ "END";
		compare(expected, module);

	}

	@Test
	public void testNestedRecordAt() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "EXTENDS Naturals \n"
			+ "CONSTANTS k \n"
			+ "ASSUME k = [a |-> [b |-> 1]] /\\ k /= [k EXCEPT !.a.b = @ + 1]  \n"
			+ "=================================";

		final String expected = "MACHINE Testing\n" + "CONSTANTS k\n"
			+ "PROPERTIES "
			+ "k : struct(a:struct(b:INTEGER)) & (k = rec(a:rec(b:1)) & k /= rec(a:rec(b:(k'a)'b + 1))) \n"
			+ "END";
		compare(expected, module);

	}

	@Test
	public void testRecordFunctionExcept() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "CONSTANTS k \n"
			+ "ASSUME k = [a |-> <<3>>] /\\ k /= [k EXCEPT !.a[1] = 4]  \n"
			+ "=================================";

		final String expected = "MACHINE Testing\n" + "CONSTANTS k\n"
			+ "PROPERTIES "
			+ "k : struct(a:INTEGER +-> INTEGER) & (k = rec(a:[3]) & k /= rec(a:k'a <+ {(1,4)})) \n"
			+ "END";
		compare(expected, module);

	}

	@Test
	public void testRecordFunctionAt() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "EXTENDS Naturals \n"
			+ "CONSTANTS k \n"
			+ "ASSUME k = [a |-> <<3>>] /\\ k /= [k EXCEPT !.a[1] = @ + 1]  \n"
			+ "=================================";

		final String expected = "MACHINE Testing\n" + "CONSTANTS k\n"
			+ "PROPERTIES "
			+ "k : struct(a:INTEGER +-> INTEGER) & (k = rec(a:[3]) & k /= rec(a:k'a <+ {(1,(k'a)(1) + 1)})) \n"
			+ "END";
		compare(expected, module);

	}

	@Test
	public void testFunctionRecordExcept() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "CONSTANTS k \n"
			+ "ASSUME k = [i \\in {3,4} |->[a |-> i, b |-> TRUE ] ] /\\ k /= [k EXCEPT ![3].b = FALSE]  \n"
			+ "=================================";

		final String expected = "MACHINE Testing\n" + "CONSTANTS k\n"
			+ "PROPERTIES "
			+ "k : INTEGER +-> struct(a:INTEGER, b:BOOL) & (k = %(i).(i : {3, 4} | rec(a:i, b:TRUE)) & k /= k <+ {(3,rec(a:k(3)'a, b:FALSE))}) \n"
			+ "END";
		compare(expected, module);

	}

	@Test
	public void testFunctionRecordAt() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "EXTENDS Naturals \n"
			+ "CONSTANTS k \n"
			+ "ASSUME k = [i \\in {3,4} |->[a |-> i, b |-> TRUE ] ] /\\ k /= [k EXCEPT ![3].a = @ + 1]  \n"
			+ "=================================";

		final String expected = "MACHINE Testing\n" + "CONSTANTS k\n"
			+ "PROPERTIES "
			+ "k : INTEGER +-> struct(a:INTEGER, b:BOOL) & (k = %(i).(i : {3, 4} | rec(a:i, b:TRUE)) & k /= k <+ {(3,rec(a:k(3)'a + 1, b:k(3)'b))}) \n"
			+ "END";
		compare(expected, module);

	}

	@Test
	public void testRecordExceptNested() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "CONSTANTS k \n"
			+ "ASSUME k = [a |-> [b |-> 1, c |-> 2]] /\\ k /= [k EXCEPT !.a.b = 2]  \n"
			+ "=================================";

		final String expected = "MACHINE Testing\n" + "CONSTANTS k\n"
			+ "PROPERTIES "
			+ "k : struct(a:struct(b:INTEGER, c:INTEGER)) & (k = rec(a:rec(b:1, c:2)) & k /= rec(a:rec(b:2, c:(k'a)'c))) \n"
			+ "END";
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
			+ "CONSTANTS k \n"
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

		final String expected = "MACHINE Testing\n" + "CONSTANTS k, k2\n"
			+ "PROPERTIES  k : POW(INTEGER*INTEGER*INTEGER) "
			+ "&  k2 : POW(INTEGER*INTEGER*INTEGER) "
			+ "& k = %x,y.(x : {1, 2} & y : {1, 2}| x + y) "
			+ "& k2 = k <+ {(1, 1) |-> k(1, 1) + 4} \n" + "END";
		compare(expected, module);
	}

	@Test
	public void testFunctionExcept9() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "EXTENDS Naturals \n"
			+ "CONSTANTS k \n"
			+ "ASSUME k = [i \\in {3,4} |-> <<i, 7>>] /\\ [k EXCEPT ![4] = <<4, 8>>] # [k EXCEPT ![4][2] = 9] \n"
			+ "=================================";

		final String expected = "MACHINE Testing\n" + "CONSTANTS k\n"
			+ "PROPERTIES "
			+ "k : INTEGER +-> (INTEGER +-> INTEGER) & (k = %(i).(i : {3, 4} | [i,7]) & k <+ {(4,[4,8])} /= k <+ {(4,k(4) <+ {(2,9)})}) \n"
			+ "END";
		compare(expected, module);
	}

	@Test
	public void testFunctionExceptNested() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "EXTENDS Naturals \n"
			+ "CONSTANTS k \n"
			+ "ASSUME k = [i \\in {3,4} |-> <<i, 7>>] /\\ k # [k EXCEPT ![4][2] = 8] \n"
			+ "=================================";

		final String expected = "MACHINE Testing\n" + "CONSTANTS k\n"
			+ "PROPERTIES "
			+ "k : INTEGER +-> (INTEGER +-> INTEGER) & (k = %(i).(i : {3, 4} | [i,7]) & k /= k <+ {(4,k(4) <+ {(2,8)})}) \n"
			+ "END";
		compare(expected, module);
	}

	@Test
	public void testFunctionExceptNested2() throws Exception {
		ToolIO.reset();
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "EXTENDS Naturals \n"
			+ "CONSTANTS k \n"
			+ "ASSUME k = [i \\in {3,4} |-> << <<8>> >>] /\\ k # [k EXCEPT ![4][1][1] = 7] \n"
			+ "=================================";

		final String expected = "MACHINE Testing\n" + "CONSTANTS k\n"
			+ "PROPERTIES "
			+ "k : INTEGER +-> (INTEGER +-> (INTEGER +-> INTEGER)) & (k = %(i).(i : {3, 4} | [[8]]) & k /= k <+ {(4,k(4) <+ {(1,(k(4))(1) <+ {(1,7)})})}) \n"
			+ "END";
		compare(expected, module);
	}
}
