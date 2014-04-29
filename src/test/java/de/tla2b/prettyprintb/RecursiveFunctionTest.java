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
				+ "RECURSIVE sum(_) \n"
				+ "sum(S) == IF S = {} THEN 0 ELSE (LET x == CHOOSE a \\in S : TRUE IN x + sum(S \\ {x})) \n"
				+ "ASSUME sum({1,2,3}) = 6 \n"
				+ "=================================";

		final String expected = "MACHINE Testing\n" + "ABSTRACT_CONSTANTS k\n"
				+ "PROPERTIES " 
				+ " k : BOOL +-> INTEGER "
				+ "& k = k <+ {TRUE |-> 0, FALSE |-> 0}" + "END";
		compare(expected, module);
		
	}
	
	@Ignore
	@Test
	public void testRecursiveDefinition2() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "RECURSIVE Sum(_,_) \n"
				+ " Sum(f,S) == IF S = {} THEN 0 \n"
				+ "                       ELSE LET x == CHOOSE x \\in S : TRUE \n"
				+ "                            IN  f[x] + Sum(f, S \\ {x}) \n"
				+ "foo[x \\in Nat] == x \n"
				+ "ASSUME Sum(foo, {1,2,3}) = 6 \n"
				+ "=================================";

		final String expected = "MACHINE Testing\n" + "ABSTRACT_CONSTANTS k\n"
				+ "PROPERTIES " 
				+ " k = k <+ {TRUE |-> 0, FALSE |-> 0}" + "END";
		compare(expected, module);
		
	}
	
	

}
