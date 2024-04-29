package de.tla2b.prettyprintb;

import org.junit.Ignore;
import org.junit.Test;

import static de.tla2b.util.TestUtil.compare;

public class TupleTest {

	@Test
	public void testTuple() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "ASSUME <<TRUE,1,TRUE>> /= <<TRUE,1,TRUE>>\n"
			+ "=================================";

		final String expected = "MACHINE Testing\n"
			+ "PROPERTIES (TRUE,1,TRUE) /= (TRUE,1,TRUE) \n" + "END";
		compare(expected, module);
	}

	@Test
	public void testCartesianProduct() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "ASSUME <<TRUE,1>> \\in BOOLEAN \\X {1} \n"
			+ "=================================";

		final String expected = "MACHINE Testing\n"
			+ "PROPERTIES (TRUE,1) : BOOL*{1} \n" + "END";
		compare(expected, module);
	}

	@Test
	public void testCartesianProduct2() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "CONSTANTS k \n"
			+ "ASSUME k = BOOLEAN \\X ({1} \\X BOOLEAN) \n"
			+ "=================================";

		final String expected = "MACHINE Testing\n"
			+ "CONSTANTS k\n"
			+ "PROPERTIES k : POW(BOOL * (INTEGER * BOOL)) & k = BOOL*({1}*BOOL) \n"
			+ "END";
		compare(expected, module);
	}

	@Test
	public void testTupleFunctionCall() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "ASSUME 1 = <<1,TRUE>>[1] \n"
			+ "=================================";

		final String expected = "MACHINE Testing\n"
			+ "PROPERTIES 1 = prj1(INTEGER, BOOL)((1,TRUE)) \n" + "END";
		compare(expected, module);
	}

	@Test
	public void testTupleFunctionCall2() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "ASSUME TRUE = <<1,TRUE>>[2] \n"
			+ "=================================";

		final String expected = "MACHINE Testing\n"
			+ "PROPERTIES TRUE = prj2(INTEGER, BOOL)((1,TRUE)) \n" + "END";
		compare(expected, module);
	}

	@Test
	public void testTupleFunctionCall3() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "ASSUME 1 = <<1,TRUE,1>>[3] \n"
			+ "=================================";

		final String expected = "MACHINE Testing\n"
			+ "PROPERTIES 1 = prj2(INTEGER * BOOL, INTEGER)((1,TRUE,1)) \n"
			+ "END";
		compare(expected, module);
	}

	@Test
	public void testTupleFunctionCall4() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "ASSUME 1 = <<1,TRUE,1>>[1] \n"
			+ "=================================";

		final String expected = "MACHINE Testing\n"
			+ "PROPERTIES 1 = prj1(INTEGER, BOOL)((prj1(INTEGER * BOOL, INTEGER)((1,TRUE,1)))) \n"
			+ "END";
		compare(expected, module);
	}

	@Test
	public void testTupleFunctionCall5() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "ASSUME 1 = <<1,TRUE,2>>[1] \n"
			+ "=================================";

		final String expected = "MACHINE Testing\n"
			+ "PROPERTIES 1 = prj1(INTEGER, BOOL)((prj1(INTEGER * BOOL, INTEGER)((1,TRUE,2)))) \n"
			+ "END";
		compare(expected, module);
	}

	@Test
	public void testTupleFunctionCall6() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "ASSUME 1 = <<1,TRUE,2,FALSE>>[1] \n"
			+ "=================================";

		final String expected = "MACHINE Testing\n"
			+ "PROPERTIES 1 = prj1(INTEGER, BOOL)((prj1(INTEGER * BOOL, INTEGER)((prj1((INTEGER * BOOL) * INTEGER, BOOL)((1,TRUE,2,FALSE)))))) \n"
			+ "END";
		compare(expected, module);
	}

	@Test
	public void testDomainOfTuple() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "ASSUME {1,2,3} = DOMAIN <<\"a\", \"b\", \"c\">> \n"
			+ "=================================";

		final String expected = "MACHINE Testing\n"
			+ "PROPERTIES {1, 2, 3} = dom([\"a\", \"b\", \"c\"]) \n"
			+ "END";
		compare(expected, module);
	}

	@Test
	public void testTupleCartesianProduct() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "ASSUME {<<1, 4>>, <<2,3>>} \\notin SUBSET ({1,2} \\X {3,4}) \n"
			+ "=================================";

		final String expected = "MACHINE Testing\n"
			+ "PROPERTIES {(1,4), (2,3)} /: POW({1, 2} * {3, 4}) \n"
			+ "END";
		compare(expected, module);
	}

	@Ignore
	@Test
	public void testAtTuple() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "EXTENDS Naturals \n"
			+ "CONSTANTS k, k2 \n"
			+ "ASSUME k =[i \\in Nat |-> <<1, \"s\">>] /\\ k2 = [ k EXCEPT ![22] = <<@[1],\"d\">>] \n"
			+ "=================================";

		final String expected = "MACHINE Testing\n"
			+ "CONSTANTS k, k2 \n"
			+ "PROPERTIES \n"
			+ "(k : INTEGER +-> INTEGER * STRING & k2 : INTEGER +-> INTEGER * STRING)"
			+ " & (k = %(i).(i : NATURAL | (1,\"s\")) & k2 = k <+ {(22,( prj1(INTEGER,STRING)(k(22)),\"d\") )}) \n"
			+ "END";
		compare(expected, module);
	}


}
