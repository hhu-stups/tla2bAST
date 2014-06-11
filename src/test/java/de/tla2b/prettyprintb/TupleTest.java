/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package de.tla2b.prettyprintb;

import static de.tla2b.util.TestUtil.compare;
import org.junit.Test;

public class TupleTest {

	@Test
	public void testTuple() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "ASSUME <<TRUE,1,TRUE>> /= <<TRUE,2,TRUE>>\n"
				+ "=================================";

		final String expected = "MACHINE Testing\n"
				+ "PROPERTIES (TRUE,1,TRUE) /= (TRUE,2,TRUE) \n" + "END";
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

}
