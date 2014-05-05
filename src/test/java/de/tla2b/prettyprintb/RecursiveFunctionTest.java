package de.tla2b.prettyprintb;

import static de.tla2b.util.TestUtil.compare;

import org.junit.Ignore;
import org.junit.Test;

public class RecursiveFunctionTest {

	@Ignore
	@Test
	public void testRecursiveDefinition() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "sum[S \\in SUBSET(Nat)] == IF S = {} THEN 0 ELSE LET x == CHOOSE a \\in S : TRUE IN x + sum[S \\ {x}] \n"
				+ "ASSUME sum[{1,2,3}] = 6 \n"
				+ "=================================";

		final String expected = "MACHINE Testing\n" + "ABSTRACT_CONSTANTS k\n"
				+ "PROPERTIES " + " k : BOOL +-> INTEGER "
				+ "& k = k <+ {TRUE |-> 0, FALSE |-> 0}" + "END";
		compare(expected, module);

	}

	@Test
	public void testFactorial() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "fac[x \\in Nat] == IF x = 1 THEN 1 ELSE x * fac[x-1]\n"
				+ "ASSUME fac[3] = 6 \n" + "=================================";

		final String expected = "MACHINE Testing\n"
				+ "ABSTRACT_CONSTANTS fac\n"
				+ "PROPERTIES "
				+ "fac = %(x).(x : NATURAL | (%(t_).(t_ = 0 & x = 1 | 1) \\/ %(t_).(t_ = 0 & not(x = 1) | x * fac((x - 1))))(0)) & fac(3) = 6 \n"
				+ "END";
		compare(expected, module);

	}

	@Test
	public void testFactorial2() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "fac[x \\in Nat] == 5 + IF x = 1 THEN 1 ELSE x * fac[x-1]\n"
				+ "ASSUME fac[3] = 56 \n" + "=================================";

		final String expected = "MACHINE Testing\n"
				+ "ABSTRACT_CONSTANTS fac\n"
				+ "PROPERTIES "
				+ "fac = %(x).(x : NATURAL | 5 + (%(t_).(t_ = 0 & x = 1 | 1) \\/ %(t_).(t_ = 0 & not(x = 1) | x * fac((x - 1))))(0)) & fac(3) = 56 \n"
				+ "END";
		compare(expected, module);
	}

	@Test
	public void testSum() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Integers, FiniteSets \n"
				+ "	Sum[x \\in Nat] == IF x = 0 THEN 0 ELSE x + Sum[x-1] \n"
				+ "ASSUME 6 = Sum[3] \n"
				+ "=================================";

		final String expected = "MACHINE Testing\n"
				+ "ABSTRACT_CONSTANTS Sum\n"
				+ "PROPERTIES "
				+ "Sum = %(x).(x : NATURAL | (%(t_).(t_ = 0 & x = 0 | 0) \\/ %(t_).(t_ = 0 & not(x = 0) | x + Sum((x - 1))))(0)) & 6 = Sum(3) \n"
				+ "END";
		compare(expected, module);
	}
	


}
