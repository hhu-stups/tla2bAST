package de.tla2b.typechecking;

import de.tla2b.util.TestTypeChecker;
import de.tla2b.util.TestUtil;
import org.junit.Test;

import static org.junit.Assert.assertEquals;

public class InstanceTest {

	private static final String path = "src/test/resources/typechecking/modules/";

	@Test
	public void TestNamedInstanceCounterReal() throws Exception {
		TestTypeChecker t = TestUtil.typeCheck(path + "NamedInstanceCounterReal.tla");
		assertEquals("REAL", t.getVariableType("c"));
		assertEquals("REAL", t.getConstantType("start"));
	}

	@Test
	public void TestNamedInstanceCounter() throws Exception {
		TestTypeChecker t = TestUtil.typeCheck(path + "NamedInstanceCounter.tla");
		assertEquals("INTEGER", t.getVariableType("c"));
		assertEquals("INTEGER", t.getConstantType("start"));
	}

	@Test
	public void TestNamedInstancePoly() throws Exception {
		TestTypeChecker t = TestUtil.typeCheck(path + "NamedInstancePoly.tla");
		assertEquals("INTEGER", t.getVariableType("c"));
	}

	@Test
	public void TestNamedInstancePoly2() throws Exception {
		TestTypeChecker t = TestUtil.typeCheck(path + "NamedInstancePoly2.tla");
		assertEquals("INTEGER", t.getVariableType("c"));
	}

	@Test
	public void TestNamedInstancePoly3() throws Exception {
		TestTypeChecker t = TestUtil.typeCheck(path + "NamedInstancePoly3.tla");
		assertEquals("BOOL", t.getVariableType("c"));
		assertEquals("INTEGER", t.getVariableType("c2"));
	}

	@Test
	public void TestNamedInstancePoly4() throws Exception {
		TestTypeChecker t = TestUtil.typeCheck(path + "NamedInstancePoly4.tla");
		assertEquals("BOOL", t.getVariableType("c"));
		assertEquals("INTEGER", t.getConstantType("k"));
	}

	@Test
	public void TestInstanceValue() throws Exception {
		TestTypeChecker t = TestUtil.typeCheck(path + "InstanceValue.tla");
		assertEquals("INTEGER", t.getConstantType("c2"));
		assertEquals("INTEGER", t.getConstantType("val2"));
	}

	@Test
	public void TestInstanceValue2Times() throws Exception {
		TestTypeChecker t = TestUtil.typeCheck(path + "InstanceValue2Times.tla");
		assertEquals("INTEGER", t.getConstantType("k"));
		assertEquals("BOOL", t.getConstantType("k2"));
	}

}
