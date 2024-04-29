package de.tla2b.expression;

import de.tla2b.exceptions.TypeErrorException;
import org.junit.Test;

import static de.tla2b.util.TestUtil.compareExprIncludingModel;

public class ModuleAndExpressionTest {

	@Test
	public void testCon() throws Exception {
		String module = "---- MODULE Testing ----\n" + "CONSTANTS k \n"
			+ "ASSUME k = 4" + "===============";
		compareExprIncludingModel("k = 1", "k = 1", module);
	}

	@Test(expected = TypeErrorException.class)
	public void testTypeError() throws Exception {
		String module = "---- MODULE Testing ----\n" + "CONSTANTS k \n"
			+ "ASSUME k = 4" + "===============";
		compareExprIncludingModel(null, "k = TRUE", module);
	}
}
