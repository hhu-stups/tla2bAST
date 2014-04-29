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
				+ "PROPERTIES " 
				+ " k : BOOL +-> INTEGER "
				+ "& k = k <+ {TRUE |-> 0, FALSE |-> 0}" + "END";
		compare(expected, module);
		
	}
}
