package de.tla2b.typechecking;

import static org.junit.Assert.assertEquals;

import org.junit.Test;

import de.tla2b.exceptions.TLA2BException;
import de.tla2b.exceptions.TypeErrorException;
import de.tla2b.util.TestTypeChecker;
import de.tla2b.util.TestUtil;


public class StringTest {
	
	/*
	 * a String: "abc"
	 */

	@Test
	public void testAString() throws TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k \n"
				+ "ASSUME k = \"abc\" \n"
				+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("STRING", t.getConstantType("k"));
	}
	
	@Test (expected = TypeErrorException.class)
	public void testAStringException() throws TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "ASSUME 1 = \"abc\" \n"
				+ "=================================";
		TestUtil.typeCheckString(module);
	}
	
	@Test
	public void testStringAsSequence() throws TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Sequences \n"
				+ "ASSUME  \"a\" \\o \"bc\" = \"abc\"  \n"
				+ "=================================";
		TestUtil.typeCheckString(module);
	}
	
	@Test
	public void testStringAsSequence2() throws TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Sequences \n"
				+ "ASSUME SubSeq(\"abc\",1,1) = \"a\"  \n"
				+ "=================================";
		TestUtil.typeCheckString(module);
	}
	
	@Test
	public void testStringAsSequence3() throws TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Sequences \n"
				+ "ASSUME Len(\"abc\") = 3 \n"
				+ "=================================";
		TestUtil.typeCheckString(module);
	}
	
	
	/*
	 * STRING
	 */
	@Test 
	public void testString() throws TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k \n"
				+ "ASSUME k = STRING \n"
				+ "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("POW(STRING)", t.getConstantType("k"));
	}
	
	@Test (expected = TypeErrorException.class)
	public void testStringException() throws TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "ASSUME 1 = STRING \n"
				+ "=================================";

		TestUtil.typeCheckString(module);
	}
	
	
	
}
