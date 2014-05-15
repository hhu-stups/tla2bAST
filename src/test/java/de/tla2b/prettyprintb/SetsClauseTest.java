package de.tla2b.prettyprintb;

import static de.tla2b.util.TestUtil.compare;

import org.junit.Test;

public class SetsClauseTest {

	@Test
	public void testSetEnumeration() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS S\n"
				+ "ASSUME S = S\n"
				+ "=================================";
		final String config = "CONSTANTS S = {s1,s2,s3}"; 

		final String expected = "MACHINE Testing\n" 
				+ "SETS ENUM1 = {s1,s2,s3} \n"
				+ "CONSTANTS S "
				+ "PROPERTIES S = ENUM1 & S = S \n" + "END";
		compare(expected, module, config);
	}
}
