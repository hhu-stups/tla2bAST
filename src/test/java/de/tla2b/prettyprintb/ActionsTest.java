package de.tla2b.prettyprintb;

import de.tla2b.exceptions.SemanticErrorException;
import org.junit.Ignore;
import org.junit.Test;

import static de.tla2b.util.TestUtil.compare;

public class ActionsTest {

	@Ignore // changed UNCHANGED translation TODO fix test
	@Test
	public void testOperation1() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "EXTENDS Naturals \n"
			+ "VARIABLES x, y \n"
			+ "Init == x = 1 /\\ y = 1 \n"
			+ "Next == x' = 1 /\\ UNCHANGED y \n"
			+ "=================================";

		final String expected = "MACHINE Testing\n"
			+ "VARIABLES x, y\n"
			+ "INVARIANT x : INTEGER & y : INTEGER \n"
			+ "INITIALISATION  x, y:(x = 1 & y = 1) \n"
			+ "OPERATIONS \n"
			+ " Next = ANY y_n WHERE y_n : INTEGER "
			+ " & y_n = y THEN x,y := 1,y_n END \n"
			+ "END";
		compare(expected, module);
	}

	@Test
	public void testOperation2() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "EXTENDS Naturals \n"
			+ "VARIABLES x, y \n"
			+ "Init == x = 1 /\\ y = 1 \n"
			+ "Next == x = 2 /\\ x' = 1 /\\ y' = y\n"
			+ "=================================";

		final String expected = "MACHINE Testing\n"
			+ "VARIABLES x, y\n"
			+ "INVARIANT x : INTEGER & y : INTEGER \n"
			+ "INITIALISATION  x, y:(x = 1 & y = 1) \n"
			+ "OPERATIONS Next = SELECT x = 2 THEN x,y := 1,y END \n"
			+ "END";
		compare(expected, module);
	}

	@Test
	public void testOperation3() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "EXTENDS Naturals \n"
			+ "VARIABLES x, y \n"
			+ "Init == x = 1 /\\ y = 1 \n"
			+ "Next == x < 2 /\\ x' = 1 /\\ y' = y\n"
			+ "=================================";

		final String expected = "MACHINE Testing\n"
			+ "VARIABLES x, y\n"
			+ "INVARIANT x : INTEGER & y : INTEGER \n"
			+ "INITIALISATION  x, y:(x = 1 & y = 1) \n"
			+ "OPERATIONS Next = SELECT x < 2 THEN x,y := 1,y END \n"
			+ "END";
		compare(expected, module);
	}

	@Test(expected = SemanticErrorException.class)
	public void testMissingInit() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "VARIABLES x \n"
				+ "Next == x'=x+1 \n"
				+ "=================================";

		compare("MACHINE Testing END", module);
	}
}
