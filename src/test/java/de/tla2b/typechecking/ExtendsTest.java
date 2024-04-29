package de.tla2b.typechecking;

import de.tla2b.util.TestTypeChecker;
import de.tla2b.util.TestUtil;
import org.junit.Test;

import static org.junit.Assert.assertEquals;


public class ExtendsTest {

	@Test
	public void TestExtendsCounter() throws Exception {
		String path = "src/test/resources/typechecking/modules/";
		TestTypeChecker t = TestUtil.typeCheck(path + "ExtendsCounter.tla");
		assertEquals("INTEGER", t.getVariableType("x"));
		assertEquals("INTEGER", t.getConstantType("start"));
	}
}
