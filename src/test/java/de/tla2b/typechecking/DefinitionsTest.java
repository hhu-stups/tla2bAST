package de.tla2b.typechecking;

import de.tla2b.exceptions.TLA2BException;
import de.tla2b.util.TestTypeChecker;
import de.tla2b.util.TestUtil;
import org.junit.Test;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

public class DefinitionsTest {

	/*
	 * Definition: foo(a,b) == e
	 */
	@Test
	public void testDefinition() throws TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "foo(a,b) == a = 1 /\\ b = TRUE \n"
			+ "Next == foo(1,TRUE) \n"
			+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("BOOL", t.getDefinitionType("foo"));
		assertEquals("INTEGER", t.getDefinitionParamType("foo", "a"));
		assertEquals("BOOL", t.getDefinitionParamType("foo", "b"));
	}

	@Test
	public void testDefinition2() throws TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "CONSTANTS k, k2 \n"
			+ "foo(a,b) == a = k /\\ b = k2 \n"
			+ "bar == k = 1 /\\ k2 = TRUE \n"
			+ "ASSUME foo(1,FALSE) /\\ bar \n"
			+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("BOOL", t.getDefinitionType("foo"));
		assertEquals("INTEGER", t.getDefinitionParamType("foo", "a"));
		assertEquals("BOOL", t.getDefinitionParamType("foo", "b"));
		assertEquals("BOOL", t.getDefinitionType("bar"));

	}

	@Test
	public void testDefinition3() throws TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "CONSTANTS k \n"
			+ "foo == k \n"
			+ "bar == foo = 1 \n"
			+ "ASSUME bar \n"
			+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("INTEGER", t.getDefinitionType("foo"));
		assertEquals("BOOL", t.getDefinitionType("bar"));
	}

	@Test
	public void testDefinition4() throws TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "CONSTANTS k, k2 \n"
			+ "foo(var, value) == var = value \n"
			+ "ASSUME foo(k,1) /\\ foo(k2,TRUE) \n"
			+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("BOOL", t.getDefinitionType("foo"));
		assertEquals("INTEGER", t.getConstantType("k"));
		assertEquals("BOOL", t.getConstantType("k2"));
	}

	/*
	 * Definition Call
	 */

	@Test
	public void testDefinitionCall() throws TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "foo(a) == TRUE \n"
			+ "bar == foo(1) \n"
			+ "ASSUME bar \n"
			+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("BOOL", t.getDefinitionType("foo"));
		assertEquals("BOOL", t.getDefinitionType("bar"));
	}

	@Test
	public void testDefinitionCall2() throws TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "foo(a) == a \n"
			+ "bar == foo(1) \n"
			+ "baz == foo(TRUE) \n"
			+ "ASSUME baz /\\ bar = bar"
			+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertTrue(t.getDefinitionType("foo").startsWith("UNTYPED"));
		assertEquals("INTEGER", t.getDefinitionType("bar"));
		assertEquals("BOOL", t.getDefinitionType("baz"));
	}

	@Test
	public void testDefinitionCall3() throws TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "CONSTANTS k, k2 \n"
			+ "foo(a) == a \n"
			+ "bar == foo(1) \n"
			+ "baz == k = foo(k2) /\\ k2 = bar \n"
			+ "ASSUME baz \n"
			+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertTrue(t.getDefinitionType("foo").startsWith("UNTYPED"));
		assertEquals("INTEGER", t.getDefinitionType("bar"));
		assertEquals("BOOL", t.getDefinitionType("baz"));
		assertEquals("INTEGER", t.getConstantType("k"));
		assertEquals("INTEGER", t.getConstantType("k2"));
	}

	@Test
	public void testDefinitionCall4() throws TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "CONSTANTS k, k2 \n"
			+ "foo(a,b) == a \\cup b \n"
			+ "bar == foo({1}, k) \n"
			+ "baz == foo({TRUE}, k2)\n"
			+ "ASSUME baz = baz /\\ bar = bar"
			+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertTrue(t.getDefinitionType("foo").startsWith("POW(UNTYPED"));
		assertEquals("POW(INTEGER)", t.getDefinitionType("bar"));
		assertEquals("POW(BOOL)", t.getDefinitionType("baz"));
		assertEquals("POW(INTEGER)", t.getConstantType("k"));
		assertEquals("POW(BOOL)", t.getConstantType("k2"));
	}

	@Test
	public void testDefinitionCall5() throws TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "CONSTANTS k \n"
			+ "foo(a,b) == a = b \n"
			+ "bar == foo(1,k) \n"
			+ "ASSUME bar \n"
			+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("BOOL", t.getDefinitionType("foo"));
		assertEquals("INTEGER", t.getConstantType("k"));
	}

	@Test
	public void testDefinitionCall6() throws TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "CONSTANTS k, k2 \n"
			+ "foo(a,b) == a = b \n"
			+ "bar == foo(k, k2) /\\ k2 = 1 \n"
			+ "ASSUME bar /\\ foo(TRUE,TRUE) \n"
			+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("BOOL", t.getDefinitionType("foo"));
		assertTrue(t.getDefinitionParamType("foo", "a").startsWith("UNTYPED"));
		assertEquals(t.getDefinitionParamType("foo", "a"), t.getDefinitionParamType("foo", "b"));
		assertEquals("BOOL", t.getDefinitionType("bar"));
		assertEquals("INTEGER", t.getConstantType("k"));
		assertEquals("INTEGER", t.getConstantType("k2"));
	}

	@Test
	public void testDefinitionCall7Simpler1() throws TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "CONSTANTS k \n"
			+ "foo(x) == x = {1} \n"
			+ "ASSUME foo(k) \n"
			+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("BOOL", t.getDefinitionType("foo"));
		assertEquals("POW(INTEGER)", t.getDefinitionParamType("foo", "x"));
		assertEquals("POW(INTEGER)", t.getConstantType("k"));
	}

	@Test
	public void testDefinitionCall7Simpler2() throws TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "CONSTANTS k \n"
			+ "foo(a,b) == a \\cup b \n"
			+ "ASSUME foo(k,{}) = {1} \n"
			+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertTrue(t.getDefinitionType("foo").startsWith("POW(UNTYPED"));
		assertTrue(t.getDefinitionParamType("foo", "a").startsWith("POW(UNTYPED"));
		assertEquals(t.getDefinitionParamType("foo", "a"), t.getDefinitionParamType("foo", "b"));
		assertEquals("POW(INTEGER)", t.getConstantType("k"));
	}

	@Test
	public void testDefinitionCall7Simpler3() throws TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "CONSTANTS k, k2, k3 \n"
			+ "foo(a,b) == a \\cup b \n"
			+ "ASSUME k2 = foo(k3, k) /\\ k3 = {1} \n"
			+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertTrue(t.getDefinitionType("foo").startsWith("POW(UNTYPED"));
		assertTrue(t.getDefinitionParamType("foo", "a").startsWith("POW(UNTYPED"));
		assertEquals(t.getDefinitionParamType("foo", "a"), t.getDefinitionParamType("foo", "b"));
		assertEquals("POW(INTEGER)", t.getConstantType("k"));
		assertEquals("POW(INTEGER)", t.getConstantType("k2"));
		assertEquals("POW(INTEGER)", t.getConstantType("k3"));
	}

	@Test
	public void testDefinitionCall7() throws TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "CONSTANTS k, k2, k3 \n"
			+ "foo(a,b) == a \\cup b \n"
			+ "bar(x,y) == x = foo(y, k) /\\ y = {1} \n"
			+ "ASSUME bar(k2,k3) \n"
			+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertTrue(t.getDefinitionType("foo").startsWith("POW(UNTYPED"));
		assertTrue(t.getDefinitionParamType("foo", "a").startsWith("POW(UNTYPED"));
		assertEquals(t.getDefinitionParamType("foo", "a"), t.getDefinitionParamType("foo", "b"));
		assertEquals("BOOL", t.getDefinitionType("bar"));
		assertEquals("POW(INTEGER)", t.getDefinitionParamType("bar", "x"));
		assertEquals("POW(INTEGER)", t.getDefinitionParamType("bar", "y"));
		assertEquals("POW(INTEGER)", t.getConstantType("k"));
	}

	@Test
	public void testDefinitionCall8() throws TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "CONSTANTS k, k2 \n"
			+ "foo(a) == k = a \n"
			+ "bar == foo(k2) \n"
			+ "baz == k2 = 1 \n"
			+ "ASSUME bar /\\ baz \n"
			+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("INTEGER", t.getConstantType("k"));
		assertEquals("INTEGER", t.getConstantType("k2"));
		assertEquals("BOOL", t.getDefinitionType("foo"));
		assertEquals("BOOL", t.getDefinitionType("bar"));
		assertEquals("BOOL", t.getDefinitionType("baz"));
		assertEquals("INTEGER", t.getDefinitionParamType("foo", "a"));
	}

	@Test
	public void testDefinitionCall9() throws TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "CONSTANTS k, k2 \n"
			+ "foo(a,b) == a = b \n"
			+ "ASSUME foo(k, 1) /\\ foo(k2, TRUE) \n"
			+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("INTEGER", t.getConstantType("k"));
		assertEquals("BOOL", t.getConstantType("k2"));
		assertEquals("BOOL", t.getDefinitionType("foo"));
		assertTrue(t.getDefinitionParamType("foo", "a").startsWith("UNTYPED"));
		assertTrue(t.getDefinitionParamType("foo", "b").startsWith("UNTYPED"));
	}

	@Test
	public void testDefinitionCall10() throws TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "foo(a,b) == a = 1 /\\ b = TRUE \n"
			+ "ASSUME foo(1, TRUE) \n"
			+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("BOOL", t.getDefinitionType("foo"));
		assertEquals("INTEGER", t.getDefinitionParamType("foo", "a"));
		assertEquals("BOOL", t.getDefinitionParamType("foo", "b"));
	}
}
