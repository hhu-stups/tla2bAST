/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package de.tla2b.prettyprintb;

import static de.tla2b.util.TestUtil.compare;
import static org.junit.Assert.assertEquals;

import org.junit.Test;

import de.tla2b.util.TestUtil;


public class TupleTest {
	
	@Test
	public void testTuple() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k\n"
				+ "ASSUME k = <<TRUE,FALSE,TRUE>>\n"
				+ "=================================";
		
		final String expected = "MACHINE Testing\n" + "ABSTRACT_CONSTANTS k\n"
				+ "PROPERTIES k = (TRUE,FALSE,TRUE) \n" + "END";
		compare(expected, module);
	}
	
	@Test
	public void testCartesianProduct() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k \n"
				+ "ASSUME k = BOOLEAN \\X {1} \n"
				+ "=================================";
		
		final String expected = "MACHINE Testing\n"+ "ABSTRACT_CONSTANTS k\n"
				+ "PROPERTIES k = BOOL*{1} \n" + "END";
		compare(expected, module);
	}
	
	@Test
	public void testCartesianProduct2() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "CONSTANTS k \n"
				+ "ASSUME k = BOOLEAN \\X ({1} \\X BOOLEAN) \n"
				+ "=================================";
		
		final String expected = "MACHINE Testing\n"+ "ABSTRACT_CONSTANTS k\n"
				+ "PROPERTIES k = BOOL*({1}*BOOL) \n" + "END";
		compare(expected, module);
	}
	
	
}
