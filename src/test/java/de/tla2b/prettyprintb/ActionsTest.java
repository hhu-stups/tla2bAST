package de.tla2b.prettyprintb;

import de.tla2b.exceptions.SemanticErrorException;
import org.junit.Ignore;
import org.junit.Test;

import static de.tla2b.util.TestUtil.compare;

public class ActionsTest {

	@Test
	public void testOperation1() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "EXTENDS Naturals \n"
			+ "VARIABLES x, y \n"
			+ "Init == x = 1 /\\ y = 1 \n"
			+ "Next == x' \\in 1..5 /\\ UNCHANGED y \n"
			+ "=================================";

		final String expected = "MACHINE Testing\n"
			+ "VARIABLES x, y\n"
			+ "INVARIANT x : INTEGER & y : INTEGER \n"
			+ "INITIALISATION  x, y:(x = 1 & y = 1) \n"
			+ "OPERATIONS \n"
			+ " Next = ANY x_n WHERE x_n : INTEGER "
			+ " & x_n : 1..5 & TRUE = TRUE THEN x := x_n END \n"
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

	@Test
	public void testOperation4() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "VARIABLES x, y \n"
				+ "Init == x = 1 /\\ y = 1 \n"
				+ "Next == x < 2 /\\ x' < x /\\ y' > y + x\n"
				+ "=================================";

		final String expected = "MACHINE Testing\n"
				+ "VARIABLES x, y\n"
				+ "INVARIANT x : INTEGER & y : INTEGER \n"
				+ "INITIALISATION  x, y:(x = 1 & y = 1) \n"
				+ "OPERATIONS Next = ANY x_n, y_n WHERE x < 2 & x_n : INTEGER & y_n : INTEGER & x_n < x & y_n > y + x THEN x,y := x_n,y_n END \n"
				+ "END";
		compare(expected, module);
	}

	@Test
	public void testUnchangedOnTopLevel() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "VARIABLES x, y \n"
				+ "Init == x = 1 /\\ y = 1 \n"
				+ "Next == x < 2 /\\ x' = 1 /\\ UNCHANGED y\n"
				+ "=================================";

		final String expected = "MACHINE Testing\n"
				+ "VARIABLES x, y\n"
				+ "INVARIANT x : INTEGER & y : INTEGER \n"
				+ "INITIALISATION  x, y:(x = 1 & y = 1) \n"
				+ "OPERATIONS Next = SELECT x < 2 & TRUE = TRUE & TRUE = TRUE THEN x:= 1 END \n"
				+ "END";
		compare(expected, module);
		// TODO: get rid of TRUE = TRUE
	}

	@Test
	public void testUnchangedOnly() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "VARIABLES x, y \n"
				+ "Init == x = 1 /\\ y = 1 \n"
				+ "Next == UNCHANGED <<x,y>>\n"
				+ "=================================";

		final String expected = "MACHINE Testing\n"
				+ "VARIABLES x, y\n"
				+ "INVARIANT x : INTEGER & y : INTEGER \n"
				+ "INITIALISATION  x, y:(x = 1 & y = 1) \n"
				+ "OPERATIONS Next = BEGIN skip END \n"
				+ "END";
		compare(expected, module);
	}

	@Test
	public void testSpecification() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "VARIABLES x \n"
				+ "Init == x = 1 \n"
				+ "Next == x' \\in 1..5 \n"
				+ "Spec == Init /\\ [][Next]_x \n"
				+ "=================================";

		final String expected = "MACHINE Testing\n"
				+ "DEFINITIONS Init == x=1 \n"
				+ "VARIABLES x \n"
				+ "INVARIANT x : INTEGER \n"
				+ "INITIALISATION  x:(Init) \n"
				+ "OPERATIONS \n"
				+ " Next = ANY x_n WHERE x_n : INTEGER "
				+ " & x_n : 1..5 THEN x := x_n END \n"
				+ "END";
		compare(expected, module);
	}

	@Ignore
	@Test
	public void testPrimedTuple() throws Exception {
		// TODO: implement
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "VARIABLES x, y, b \n"
				+ "Init == <<x,y,b>> = <<1,1,FALSE>> \n"
				+ "Next == <<x,y,b>>' = <<x+1,y-1,~b>>\n"
				+ "=================================";

		final String expected = "MACHINE Testing\n"
				+ "VARIABLES x, y, b\n"
				+ "INVARIANT x : INTEGER & y : INTEGER & b : BOOL \n"
				+ "INITIALISATION  x, y, b:(x = 1 & y = 1 & b = FALSE) \n"
				+ "OPERATIONS Next = BEGIN x,y,b := x+1,y-1,bool(b = FALSE) END \n"
				+ "END";
		compare(expected, module);
	}

	@Ignore
	@Test
	public void testPrimedDefinition() throws Exception {
		// TODO: implement
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "VARIABLES x, y, b \n"
				+ "Init == <<x,y,b>> = <<1,1,FALSE>> \n"
				+ "NextDef(s,t,u) == s=t+2 /\\ u=TRUE \n"
				+ "Next == NextDef(x,y,b)' /\\ y'=y-1 \n"
				+ "=================================";

		final String expected = "MACHINE Testing\n"
				+ "VARIABLES x, y, b\n"
				+ "INVARIANT x : INTEGER & y : INTEGER & b : BOOL \n"
				+ "INITIALISATION  x, y, b:(x = 1 & y = 1 & b = FALSE) \n"
				+ "OPERATIONS Next = ANY x_n, y_n WHERE x_n : INTEGER & y_n : INTEGER & x_n = y_n+2 & y_n = y-1 THEN x,y,b := x_n,y_n,TRUE END \n"
				+ "END";
		compare(expected, module);
	}

	@Test
	public void testAlwaysDisabled() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "Init == TRUE \n"
				+ "Next == FALSE\n"
				+ "=================================";

		final String expected = "MACHINE Testing\n"
				+ "OPERATIONS Next = SELECT FALSE = TRUE THEN skip END \n"
				+ "END";
		compare(expected, module);
	}

	@Test
	public void testAlwaysEnabled() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "Init == TRUE \n"
				+ "Next == TRUE\n"
				+ "=================================";

		final String expected = "MACHINE Testing\n"
				+ "OPERATIONS Next = SELECT TRUE = TRUE THEN skip END \n"
				+ "END";
		compare(expected, module);
	}

	@Ignore
	@Test
	public void testAngleAct() throws Exception {
		// TODO: implement?
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "VARIABLES x \n"
				+ "AngleActDef == x' \\in 1..3 \n"
				+ "Init == x = 1 \n"
				+ "Next == <<AngleActDef>>_x \n"
				+ "=================================";

		// <<AngleAct>>_x means: AngleAct AND x'/=x
		final String expected = "MACHINE Testing\n"
				+ "DEFINITIONS AngleActDef == x_n : 1..3"
				+ "VARIABLES x\n"
				+ "INVARIANT x : INTEGER \n"
				+ "INITIALISATION  x:(x = 1) \n"
				+ "OPERATIONS Next = ANY x_n WHERE x_n : INTEGER & (AngleActDef & x_n /= x) THEN x := x_n END \n"
				+ "END";
		compare(expected, module);
	}

	@Ignore
	@Test
	public void testSquaredAct() throws Exception {
		// TODO: do we need a translation for stuttering steps? => implement?
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "VARIABLES x \n"
				+ "SquaredActDef == x' \\in 1..3 \n"
				+ "Init == x = 1 \n"
				+ "Next == [SquaredActDef]_x \n"
				+ "=================================";

		// [SquaredAct]_x means: SquaredAct OR x'=x
		final String expected = "MACHINE Testing\n"
				+ "DEFINITIONS SquaredActDef == x_n = 1"
				+ "VARIABLES x\n"
				+ "INVARIANT x : INTEGER \n"
				+ "INITIALISATION  x:(x = 1) \n"
				+ "OPERATIONS Next = ANY x_n WHERE x_n : INTEGER & (SquaredActDef or x_n = x) THEN x := x_n END \n"
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
