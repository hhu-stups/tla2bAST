/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package de.tla2b.prettyprintb;

import static de.tla2b.util.TestUtil.compare;

import org.junit.Test;

public class BBuiltInsTest {

	@Test
	public void testBoolean() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "ASSUME TRUE \\in BOOLEAN\n"
				+ "=================================";

		final String expected = "MACHINE Testing\n"
				+ "PROPERTIES TRUE : BOOL \n" + "END";
		compare(expected, module);
	}

	@Test
	public void testString() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "ASSUME \"abc\" \\in STRING\n"
				+ "=================================";

		final String expected = "MACHINE Testing\n"
				+ "PROPERTIES \"abc\" : STRING \n" + "END";
		compare(expected, module);
	}

	@Test
	public void testBoolValue() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "ASSUME TRUE \n" + "=================================";

		final String expected = "MACHINE Testing\n"
				+ "PROPERTIES TRUE = TRUE \n" + "END";
		compare(expected, module);
	}

	@Test
	public void testBoolValue2() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "ASSUME TRUE = FALSE \n"
				+ "=================================";

		final String expected = "MACHINE Testing\n"
				+ "PROPERTIES TRUE = FALSE \n" + "END";
		compare(expected, module);
	}
}
