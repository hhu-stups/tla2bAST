package de.tla2b.util;

import static org.junit.Assert.*;

import util.FileUtil;
import de.be4.classicalb.core.parser.BParser;
import de.be4.classicalb.core.parser.exceptions.BCompoundException;
import de.be4.classicalb.core.parser.node.Node;
import de.be4.classicalb.core.parser.node.Start;
import de.tla2b.exceptions.FrontEndException;
import de.tla2b.exceptions.TLA2BException;
import de.tla2b.output.ASTPrettyPrinter;
import de.tla2b.output.Renamer;
import de.tla2bAst.Translator;
import util.ToolIO;

public class TestUtil {

	public static void loadTlaFile(String tlaFile) throws Exception {
		Translator t = new Translator(tlaFile);
		t.translate();
	}

	public static void runModule(String tlaFile) throws Exception {
		Translator t = new Translator(tlaFile);
		Start start = t.translate();

		System.out.println("-------------------");
		ASTPrettyPrinter aP = new ASTPrettyPrinter(start);
		start.apply(aP);
		System.out.println(aP.getResultString());

		final BParser parser = new BParser("testcase");
		final Start ppStart = parser.parse(aP.getResultString(), false);

		String result = getTreeAsString(start);
		System.out.println(result);
		String ppResult = getTreeAsString(ppStart);
		System.out.println(ppResult);

		System.out.println("-------------------");
		// compare the generated AST and the AST of the pretty print
		// assertEquals(result, ppResult);
		// System.out.println(t.getBDefinitions().getDefinitionNames());
	}

	public static void compareExpr(String bExpr, String tlaExpr) throws Exception {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		Start resultNode = Translator.translateTlaExpression(tlaExpr);
		Renamer renamer = new Renamer(resultNode);
		ASTPrettyPrinter aP = new ASTPrettyPrinter(resultNode, renamer);
		resultNode.apply(aP);
		System.out.println(aP.getResultString());
		String bAstString = getAstStringofBExpressionString(bExpr);
		String result = getAstStringofBExpressionString(aP.getResultString());
		// String tlaAstString = getTreeAsString(resultNode);
		assertEquals(bAstString, result);
	}

	public static void compareExprIncludingModel(String bExpr, String tlaExpr, String moduleString) throws Exception {
		Translator trans = new Translator(moduleString, null);
		trans.translate();
		Start resultNode = trans.translateExpression(tlaExpr);
		Renamer renamer = new Renamer(resultNode);
		ASTPrettyPrinter aP = new ASTPrettyPrinter(resultNode, renamer);
		resultNode.apply(aP);
		String bAstString = getAstStringofBExpressionString(bExpr);
		String result = getAstStringofBExpressionString(aP.getResultString());
		assertEquals(bAstString, result);
	}

	public static void compare(final String bMachine, final String tlaModule) throws Exception {
		ToolIO.setMode(ToolIO.TOOL);
		String expected = getAstStringofBMachineString(bMachine);

		Translator trans = new Translator(tlaModule, null);
		Start resultNode = trans.translate();
		String result = getTreeAsString(resultNode);
		System.out.println(expected);
		System.out.println(result);

		ASTPrettyPrinter aP = new ASTPrettyPrinter(resultNode);
		resultNode.apply(aP);
		System.out.println("-------------------");
		System.out.println(aP.getResultString());
		final BParser parser = new BParser("testcase");
		// Start ast = parser.parse(aP.getResultString(), false);
		// BParser.printASTasProlog(System.out, new BParser(), new
		// File("./test.mch"), resultNode, false, true, null);

		// System.out.println("----------PP------------");
		// System.out.println(aP.getResultString());
		// System.out.println(getTreeAsString(ast));
		assertEquals(expected, result);

		// System.out.println(result);
		// assertEquals(expected, getTreeAsString(ast));
	}

	public static void compare(String bMachine, String tlaModule, String config) throws Exception {
		ToolIO.setMode(ToolIO.TOOL);
		String expected = getAstStringofBMachineString(bMachine);
		System.out.println(expected);

		Translator trans = new Translator(tlaModule, config);
		Start resultNode = trans.translate();

		ASTPrettyPrinter aP = new ASTPrettyPrinter(resultNode);
		resultNode.apply(aP);
		System.out.println(aP.getResultString());

		String result = getTreeAsString(resultNode);
		System.out.println(result);
		assertEquals(expected, result);
	}

	public static String getTreeAsString(Node node) {
		final Ast2String ast2String = new Ast2String();
		node.apply(ast2String);
		return ast2String.toString();
	}

	public static void renamerTest(String tlaFile) throws Exception {
		Translator t = new Translator(tlaFile);
		Start start = t.translate();
		Renamer renamer = new Renamer(start);
		ASTPrettyPrinter aP = new ASTPrettyPrinter(start, renamer);
		start.apply(aP);
		System.out.println(aP.getResultString());

		final BParser parser = new BParser("testcase");
		parser.parse(aP.getResultString(), false);
	}

	public static TestTypeChecker typeCheckString(String moduleString) throws FrontEndException, TLA2BException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		TestTypeChecker testTypeChecker = new TestTypeChecker();
		testTypeChecker.startTest(moduleString, null);
		return testTypeChecker;

	}

	public static TestTypeChecker typeCheckString(String moduleString, String configString)
			throws FrontEndException, TLA2BException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		TestTypeChecker testTypeChecker = new TestTypeChecker();
		testTypeChecker.startTest(moduleString, configString);
		return testTypeChecker;
	}

	public static TestTypeChecker typeCheck(String moduleFileName) throws FrontEndException, TLA2BException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		moduleFileName = moduleFileName.replace('/', FileUtil.separatorChar);
		TestTypeChecker testTypeChecker = new TestTypeChecker();
		testTypeChecker.start(moduleFileName);
		return testTypeChecker;
	}

	public static String getAstStringofBMachineString(final String testMachine) throws BCompoundException {
		final BParser parser = new BParser("testcase");
		final Start startNode = parser.parse(testMachine, false);

		final Ast2String ast2String = new Ast2String();
		startNode.apply(ast2String);
		final String string = ast2String.toString();
		return string;
	}

	public static String getAstStringofBExpressionString(final String expr) throws BCompoundException {
		final BParser parser = new BParser("testcase");
		final Start startNode = parser.parse("#FORMULA " + expr, false);

		final Ast2String ast2String = new Ast2String();
		startNode.apply(ast2String);
		final String string = ast2String.toString();
		return string;
	}

}
