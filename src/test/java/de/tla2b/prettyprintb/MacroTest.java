package de.tla2b.prettyprintb;

import static de.tla2b.util.TestUtil.compare;

import org.junit.Test;

public class MacroTest {

	
	@Test
	public void testRenaming1() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "def(y) == \\A x \\in {1}: y = 3 \n"
				+ "ASSUME \\E x \\in {3}: def(x) \n"
				+ "=================================";

		final String expected = "MACHINE Testing\n"
				+ "DEFINITIONS def(y) == !(x_1).(x_1 : {1} => y = 3); "
				+ "PROPERTIES #(x).(x : {3} & def(x)) \n" + "END";
		compare(expected, module);
	}
	
	@Test
	public void testRenaming2() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "def(y) == \\A x \\in {1}: y = 3 \n"
				+ "ASSUME \\E x \\in {2}: def(x+1) \n"
				+ "=================================";

		final String expected = "MACHINE Testing\n"
				+ "DEFINITIONS def(y) == !(x_1).(x_1 : {1} => y = 3); "
				+ "PROPERTIES #(x).(x : {2} & def(x+1)) \n" + "END";
		compare(expected, module);
	}
	
	@Test
	public void testRenaming3() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "foo(a) == a \n"
				+ "def(y) == \\A x \\in {1}: y = 3 \n"
				+ "ASSUME \\E x \\in {2}: foo(def(x)) \n"
				+ "=================================";

		final String expected = "MACHINE Testing\n"
				+ "DEFINITIONS foo(a) == a; \n"
				+ "def(y) == !(x_1).(x_1 : {1} => y = 3) \n"
				+ "PROPERTIES #(x).(x : {2} & foo(bool(def(x))) = TRUE) \n" + "END";
		compare(expected, module);
	}
	
	@Test
	public void testRenaming4() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "def(y) == \\A x \\in {1}: y = 3 \n"
				+ "foo == \\E x \\in {2}: def(x) \n"
				+ "ASSUME foo \n"
				+ "=================================";

		final String expected = "MACHINE Testing\n"
				+ "DEFINITIONS \n"
				+ "def(y) == !(x_1).(x_1 : {1} => y = 3); \n"
				+ "foo == #(x).(x : {2} & def(x)); \n"
				+ "PROPERTIES foo \n" + "END";
		compare(expected, module);
	}
	
	@Test
	public void testRenaming5() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "def(y) == \\A x \\in {1}: y = 3 \n"
				+ "foo(x) == def(x) \n"
				+ "ASSUME \\E x \\in {2}: foo(x) \n"
				+ "=================================";

		final String expected = "MACHINE Testing\n"
				+ "DEFINITIONS \n"
				+ "def(y) == !(x_1).(x_1 : {1} => y = 3); \n"
				+ "foo(x) == def(x); \n"
				+ "PROPERTIES #(x).(x : {2} & foo(x)) \n" + "END";
		compare(expected, module);
	}
	
	@Test
	public void testRenamingGlobal() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "def(y) == \\A x \\in {1}: y = 3 \n"
				+ "CONSTANTS x\n"
				+ "ASSUME x = 3 /\\  def(x) \n"
				+ "=================================";

		final String expected = "MACHINE Testing\n"
				+ "DEFINITIONS \n"
				+ "def(y) == !(x_1).(x_1 : {1} => y = 3); \n"
				+ "CONSTANTS x\n"
				+ "PROPERTIES x : INTEGER & (x = 3 &  def(x)) \n" + "END";
		compare(expected, module);
	}
	
}
