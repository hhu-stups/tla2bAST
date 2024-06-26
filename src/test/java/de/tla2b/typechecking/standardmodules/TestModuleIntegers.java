package de.tla2b.typechecking.standardmodules;

import de.tla2b.exceptions.TLA2BException;
import de.tla2b.exceptions.TypeErrorException;
import de.tla2b.util.TestTypeChecker;
import de.tla2b.util.TestUtil;
import org.junit.Test;

import static org.junit.Assert.assertEquals;


public class TestModuleIntegers {

	/*
	 * Int
	 */
	@Test
	public void unifyInt() throws TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "EXTENDS Integers \n"
			+ "CONSTANTS k \n"
			+ "ASSUME k = Int \n" + "=================================";
		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("POW(INTEGER)", t.getConstantType("k"));
	}

	@Test(expected = TypeErrorException.class)
	public void unifyErrorInt() throws TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "EXTENDS Integers \n"
			+ "ASSUME TRUE \\in Int \n"
			+ "=================================";

		TestUtil.typeCheckString(module);
	}

	/*
	 * unary minus: -x
	 */
	@Test
	public void unifyUnaryMinus() throws TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "EXTENDS Integers \n"
			+ "CONSTANTS k, k2 \n"
			+ "ASSUME k = -k2 \n" + "=================================";

		TestTypeChecker t = TestUtil.typeCheckString(module);
		assertEquals("INTEGER", t.getConstantType("k"));
		assertEquals("INTEGER", t.getConstantType("k2"));
	}

	@Test(expected = TypeErrorException.class)
	public void unifyErrorUnaryMinus() throws TLA2BException {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "EXTENDS Integers \n"
			+ "ASSUME TRUE = -1 \n"
			+ "=================================";
		TestUtil.typeCheckString(module);
	}

}
