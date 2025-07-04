package de.tla2b.prettyprintb;

import java.io.File;

import de.be4.classicalb.core.parser.BParser;
import de.be4.classicalb.core.parser.node.Start;
import de.be4.classicalb.core.parser.util.PrettyPrinter;
import de.tla2b.util.TestUtil;
import de.tla2bAst.Translator;

import org.junit.Test;

import static de.tla2b.util.TestUtil.compare;
import static org.junit.Assert.assertEquals;

public class MiscellaneousConstructsTest {

	@Test
	public void testSimpleLet() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "EXTENDS Naturals \n"
			+ "ASSUME LET foo(a) == a + a IN 4 = foo(2)\n"
			+ "=================================";

		final String expected = "MACHINE Testing\n"
			+ "PROPERTIES 4 = 2 + 2 \n" + "END";
		compare(expected, module);
	}

	@Test
	public void testLet2Definitions() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "EXTENDS Naturals \n"
			+ "ASSUME LET foo(a) == a + a bar(b) == b * b IN bar(2) = foo(2)\n"
			+ "=================================";

		final String expected = "MACHINE Testing\n"
			+ "PROPERTIES 2 * 2 = 2 + 2 \n" + "END";
		compare(expected, module);
	}

	@Test
	public void testNestedLet() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "EXTENDS Naturals \n"
			+ "ASSUME LET foo(a) == LET bar(b) == b * b IN bar(a+1) IN 9 = foo(2)\n"
			+ "=================================";

		final String expected = "MACHINE Testing\n"
			+ "PROPERTIES 9 = (2 + 1) * (2 + 1) \n" + "END";
		compare(expected, module);
	}

	@Test
	public void testSimpleCase() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "EXTENDS Naturals \n"
			+ "ASSUME 2 = CASE 1 = 1 -> 2 \n"
			+ "=================================";

		final String expected = "MACHINE Testing\n"
			+ "DEFINITIONS CHOOSE(X) == \"a member of X\"; EXTERNAL_FUNCTION_CHOOSE(T) == POW(T) --> T;"
			+ "PROPERTIES 2 = CHOOSE({t_ | 1=1 & t_ = 2}) \n" + "END";
		compare(expected, module);
	}

	@Test
	public void testCase2Conditions() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "EXTENDS Naturals \n"
			+ "ASSUME 2 = CASE 1 = 1 -> 2 [] 1 = 2 -> 3\n"
			+ "=================================";

		final String expected = "MACHINE Testing\n"
			+ "DEFINITIONS CHOOSE(X) == \"a member of X\"; EXTERNAL_FUNCTION_CHOOSE(T) == POW(T) --> T;"
			+ "PROPERTIES 2 = CHOOSE({t_ | (1 = 1 & t_ = 2) or (1 = 2 & t_ = 3)}) \n" + "END";
		compare(expected, module);
	}

	@Test
	public void testCaseOtherCondition() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "EXTENDS Naturals \n"
			+ "ASSUME 4 = CASE 1 = 2 -> 2 [] 1 = 3 -> 3 [] OTHER -> 4\n"
			+ "=================================";

		final String expected = "MACHINE Testing\n"
			+ "DEFINITIONS CHOOSE(X) == \"a member of X\"; EXTERNAL_FUNCTION_CHOOSE(T) == POW(T) --> T;"
			+ "PROPERTIES 4 = CHOOSE({t_ | ((1 = 2 & t_ = 2) or (1 = 3 & t_ = 3)) or (not(1 = 2 or 1 = 3) & t_ = 4)}) \n" + "END";
		compare(expected, module);
	}

	@Test
	public void testCasePredicate() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "EXTENDS Naturals \n"
			+ "ASSUME CASE 1 = 2 -> TRUE [] TRUE -> 1=1\n"
			+ "=================================";

		final String expected = "MACHINE Testing\n"
			+ "DEFINITIONS CHOOSE(X) == \"a member of X\"; EXTERNAL_FUNCTION_CHOOSE(T) == POW(T) --> T;"
			+ "PROPERTIES CHOOSE({t_ | (1 = 2 & t_ = TRUE) or (TRUE = TRUE & t_ = bool(1 = 1))}) = TRUE \n" + "END";
		compare(expected, module);
	}


	@Test
	public void testUnboundedChoose() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "ASSUME (CHOOSE x : x = 1) = 1\n"
			+ "=================================";

		final String expected = "MACHINE Testing\n"
			+ "DEFINITIONS CHOOSE(X) == \"a member of X\"; EXTERNAL_FUNCTION_CHOOSE(T) == POW(T) --> T;"
			+ "PROPERTIES CHOOSE({x | x = 1}) = 1 \n" + "END";
		compare(expected, module);
	}

	@Test
	public void testUnboundedChoosePredicate() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "ASSUME (CHOOSE x : x = TRUE)\n"
			+ "=================================";

		final String expected = "MACHINE Testing\n"
			+ "DEFINITIONS CHOOSE(X) == \"a member of X\"; EXTERNAL_FUNCTION_CHOOSE(T) == POW(T) --> T;"
			+ "PROPERTIES CHOOSE({x | x = TRUE}) = TRUE \n" + "END";
		compare(expected, module);
	}

	@Test
	public void testBoundedChoose() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "ASSUME (CHOOSE x \\in {1}: TRUE) = 1\n"
			+ "=================================";

		final String expected = "MACHINE Testing\n"
			+ "DEFINITIONS CHOOSE(X) == \"a member of X\"; EXTERNAL_FUNCTION_CHOOSE(T) == POW(T) --> T;"
			+ "PROPERTIES CHOOSE({x | x : {1} & TRUE = TRUE}) = 1 \n" + "END";
		compare(expected, module);
	}


	@Test
	public void testUnBoundedChooseTuple() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "ASSUME <<1,TRUE>> = CHOOSE <<a,b>> \\in {<<1,TRUE>>}: TRUE \n"
			+ "=================================";

		final String expected = "MACHINE Testing\n"
			+ "DEFINITIONS CHOOSE(X) == \"a member of X\"; EXTERNAL_FUNCTION_CHOOSE(T) == POW(T) --> T;"
			+ "PROPERTIES (1,TRUE) = CHOOSE({a,b | (a,b) : {(1,TRUE)} & TRUE = TRUE}) \n" + "END";
		compare(expected, module);
	}


	@Test
	public void testBoundedChoosePredicate() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "ASSUME (CHOOSE x \\in {TRUE}: TRUE) = TRUE\n"
			+ "=================================";

		final String expected = "MACHINE Testing\n"
			+ "DEFINITIONS CHOOSE(X) == \"a member of X\"; EXTERNAL_FUNCTION_CHOOSE(T) == POW(T) --> T;"
			+ "PROPERTIES CHOOSE({x | x : {TRUE} & TRUE = TRUE}) = TRUE \n" + "END";
		compare(expected, module);
	}

	@Test
	public void testBoundedChooseTuple() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "ASSUME <<1,TRUE>> = CHOOSE <<a,b>> \\in {<<1,TRUE>>}: TRUE \n"
			+ "=================================";

		final String expected = "MACHINE Testing\n"
			+ "DEFINITIONS CHOOSE(X) == \"a member of X\"; EXTERNAL_FUNCTION_CHOOSE(T) == POW(T) --> T;"
			+ "PROPERTIES (1,TRUE) = CHOOSE({a,b | (a,b) : {(1,TRUE)} & TRUE = TRUE}) \n" + "END";
		compare(expected, module);
	}

	@Test
	public void testUnboundedChooseTuple() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "ASSUME <<1,TRUE>> = CHOOSE <<a,b>> : <<a,b>> = <<1,TRUE>>\n"
			+ "=================================";

		final String expected = "MACHINE Testing\n"
			+ "DEFINITIONS CHOOSE(X) == \"a member of X\"; EXTERNAL_FUNCTION_CHOOSE(T) == POW(T) --> T;"
			+ "PROPERTIES (1,TRUE) = CHOOSE({a,b | (a,b) = (1,TRUE)}) \n" + "END";
		compare(expected, module);
	}

	@Test
	public void testRelParFuncEleOf() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "EXTENDS FiniteSets, Integers \n"
			+ "CONSTANTS k \n"
			+ "RelParFuncEleOf(S, T) == {f \\in SUBSET (S \\times T): Cardinality({ x[1] :x \\in f}) = Cardinality(f)} \n"
			+ "ASSUME k \\in RelParFuncEleOf(Int, BOOLEAN) \n"
			+ "=================================";

		final String expected = "MACHINE Testing\n"
			+ "DEFINITIONS RelParFuncEleOf(p__S,p__T) == LET S,T BE S=p__S & T=p__T IN {f|f:POW(S*T) & card(UNION(x).(x:f|{@prj1(x)}))=card(f)} END;"
			+ "CONSTANTS k \n"
			+ "PROPERTIES k : POW(INTEGER*BOOL) & k : RelParFuncEleOf(INTEGER,BOOL) \n"
			+ "END";
		compare(expected, module);
	}

	@Test
	public void testRelParFuncEleOf2() throws Exception {
		Translator t = new Translator("src/test/resources/prettyprint/RelParFuncEleOf/RelParFuncEleOf.tla");
		Start start = t.translate();
		String resultTree = TestUtil.getTreeAsString(start);

		PrettyPrinter pp = new PrettyPrinter();
		start.apply(pp);

		// parse pretty print result
		final BParser parser = new BParser("testcase");
		final Start ppStart = parser.parseMachine(pp.getPrettyPrint());
		String ppTree = TestUtil.getTreeAsString(ppStart);

		// comparing result with pretty print
		assertEquals(resultTree, ppTree);


		// machine file
		File expectedMachine = new File("src/test/resources/prettyprint/RelParFuncEleOf/RelParFuncEleOf.mch");

		final BParser expectedParser = new BParser("testcase");
		final Start expectedStart = expectedParser.parseFile(expectedMachine);

		String expectedTree = TestUtil.getTreeAsString(expectedStart);

		assertEquals(expectedTree, resultTree);
	}
}
