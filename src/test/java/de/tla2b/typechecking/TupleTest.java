package de.tla2b.typechecking;

import de.tla2b.exceptions.TLA2BException;
import de.tla2b.exceptions.TypeErrorException;
import de.tla2b.util.TestTypeChecker;
import de.tla2b.util.TestUtil;
import org.junit.Test;

import static org.junit.Assert.assertEquals;


public class TupleTest {

	@Test
	public void testSimpleTuple() throws TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "EXTENDS Naturals \n"
			+ "CONSTANTS k \n"
			+ "ASSUME k = <<1,TRUE>> \n"
			+ "=================================";

		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("INTEGER*BOOL", t.getConstantType("k"));
	}


	@Test
	public void testTupleFunctionCall() throws TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "EXTENDS Naturals \n"
			+ "CONSTANTS k \n"
			+ "ASSUME k = <<1,TRUE,1>>[2] \n"
			+ "=================================";

		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("BOOL", t.getConstantType("k"));
	}

	@Test
	public void testTupleFunctionCall2() throws TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "EXTENDS Naturals \n"
			+ "CONSTANTS k \n"
			+ "ASSUME k = <<1,TRUE,\"str\">>[3] \n"
			+ "=================================";

		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("STRING", t.getConstantType("k"));
	}

	@Test
	public void testTuple3Components() throws TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "EXTENDS Naturals \n"
			+ "CONSTANTS k \n"
			+ "ASSUME k = <<1,TRUE,1>> \n"
			+ "=================================";

		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("INTEGER*BOOL*INTEGER", t.getConstantType("k"));
	}

	@Test
	public void testTuple3Components2() throws TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "EXTENDS Naturals \n"
			+ "CONSTANTS k \n"
			+ "ASSUME k = <<1,1,1>> \n"
			+ "=================================";

		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("POW(INTEGER*INTEGER)", t.getConstantType("k"));
	}

	@Test
	public void testTupleComponentsOfTheSameType() throws TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "EXTENDS Naturals \n"
			+ "CONSTANTS k \n"
			+ "ASSUME k = <<1,1>> \n" + "=================================";

		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("POW(INTEGER*INTEGER)", t.getConstantType("k"));
	}

	@Test
	public void testTuple1() throws TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "EXTENDS Naturals \n"
			+ "CONSTANTS k, k2 \n"
			+ "ASSUME k = <<1,k2>> /\\ k2 = TRUE \n"
			+ "=================================";

		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("INTEGER*BOOL", t.getConstantType("k"));
		assertEquals("BOOL", t.getConstantType("k2"));
	}

	@Test
	public void testCartesianProduct() throws TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "EXTENDS Naturals \n"
			+ "CONSTANTS k \n"
			+ "ASSUME k = {1} \\times BOOLEAN \n"
			+ "=================================";

		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("POW(INTEGER*BOOL)", t.getConstantType("k"));
	}

	@Test
	public void testTupleSingleElement() throws TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "CONSTANTS k \n"
			+ "ASSUME k = <<TRUE>> \n"
			+ "=================================";

		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("POW(INTEGER*BOOL)", t.getConstantType("k"));
	}

	@Test
	public void testTuple2Elements() throws TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "CONSTANTS k, k2, k3 \n"
			+ "ASSUME k = <<k2, k3>> /\\ k2 = 1 /\\ k3 = TRUE \n"
			+ "=================================";

		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("INTEGER*BOOL", t.getConstantType("k"));
	}

	@Test
	public void testUnifyTuple3() throws TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "CONSTANTS k, k2, k3 \n"
			+ "ASSUME k = <<k2, <<k3>> >> /\\ k3 = TRUE /\\ k2 = 1\n"
			+ "=================================";

		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("INTEGER*POW(INTEGER*BOOL)", t.getConstantType("k"));
		assertEquals("INTEGER", t.getConstantType("k2"));
		assertEquals("BOOL", t.getConstantType("k3"));
	}

	@Test(expected = TypeErrorException.class)
	public void testUnifyTuple4() throws TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "CONSTANTS k \n"
			+ "ASSUME k \\in <<TRUE>>\n"
			+ "=================================";

		TestUtil.typeCheckString(module);
	}

	/*
	 * Cartesian Product
	 */
	@Test
	public void testCartesianProduct2() throws TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "CONSTANTS k \n"
			+ "ASSUME k = BOOLEAN \\X {1} \n"
			+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("POW(BOOL*INTEGER)", t.getConstantType("k"));
	}

	@Test
	public void testCartesianProduct3() throws TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "CONSTANTS k, k2 \n"
			+ "ASSUME BOOLEAN \\X {1} = k \\X k2 \n"
			+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("POW(BOOL)", t.getConstantType("k"));
		assertEquals("POW(INTEGER)", t.getConstantType("k2"));
	}

	@Test (expected = TypeErrorException.class)
	public void testCartesianProductException() throws TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "CONSTANTS k \n"
			+ "ASSUME k = BOOLEAN \\X 1 \n"
			+ "=================================";
		TestUtil.typeCheckString(module);
	}

	@Test
	public void testTupleWithRecord() throws TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k \n"
				+ "ASSUME k = <<[x |-> TRUE, y |-> 5], FALSE>> \n"
				+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("struct(x:BOOL,y:INTEGER)*BOOL", t.getConstantType("k"));
	}

}
