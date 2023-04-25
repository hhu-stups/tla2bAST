package de.tla2b.util;

import de.be4.classicalb.core.parser.BParser;
import de.be4.classicalb.core.parser.analysis.prolog.ASTProlog;
import de.be4.classicalb.core.parser.exceptions.BCompoundException;
import de.be4.classicalb.core.parser.node.Node;
import de.be4.classicalb.core.parser.node.Start;
import de.prob.prolog.output.PrologTermStringOutput;
import de.tla2b.exceptions.TLA2BException;
import de.tla2b.output.ASTPrettyPrinter;
import de.tla2b.output.Renamer;
import de.tla2bAst.Translator;

import util.FileUtil;
import util.ToolIO;

import static org.junit.Assert.assertEquals;

public class TestUtil {

	public static void loadTlaFile(String tlaFile) throws TLA2BException {
		Translator t = new Translator(tlaFile);
		t.translate();
	}

	public static void runModule(String tlaFile) throws BCompoundException, TLA2BException {
		Translator t = new Translator(tlaFile);
		Start start = t.translate();

		ASTPrettyPrinter aP = new ASTPrettyPrinter(start);
		start.apply(aP);
		final BParser parser = new BParser("testcase");
		final Start ppStart = parser.parse(aP.getResultString(), false);

		String result = getTreeAsString(start);
		String ppResult = getTreeAsString(ppStart);

		// compare the generated AST and the AST of the pretty print
		// assertEquals(result, ppResult);
	}

	public static void compareExpr(String bExpr, String tlaExpr) throws BCompoundException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		Start resultNode = Translator.translateTlaExpression(tlaExpr);
		Renamer renamer = new Renamer(resultNode);
		ASTPrettyPrinter aP = new ASTPrettyPrinter(resultNode, renamer);
		resultNode.apply(aP);
		String bAstString = getAstStringofBExpressionString(bExpr);
		String result = getAstStringofBExpressionString(aP.getResultString());
		// String tlaAstString = getTreeAsString(resultNode);
		assertEquals(bAstString, result);
	}

	public static void compareExprIncludingModel(String bExpr, String tlaExpr, String moduleString) throws BCompoundException, TLA2BException {
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

	public static void compare(final String bMachine, final String tlaModule) throws BCompoundException, TLA2BException {
		ToolIO.setMode(ToolIO.TOOL);
		String expected = getAstStringofBMachineString(bMachine);

		Translator trans = new Translator(tlaModule, null);
		Start resultNode = trans.translate();
		String result = getTreeAsString(resultNode);
		assertEquals(expected, result);
	}

	public static void compare(String bMachine, String tlaModule, String config) throws BCompoundException, TLA2BException {
		ToolIO.setMode(ToolIO.TOOL);
		String expected = getAstStringofBMachineString(bMachine);

		Translator trans = new Translator(tlaModule, config);
		Start resultNode = trans.translate();

		String result = getTreeAsString(resultNode);
		assertEquals(expected, result);
	}

	public static String getTreeAsString(Node node) {
		final PrologTermStringOutput pout = new PrologTermStringOutput();
		node.apply(new ASTProlog(pout, null));
		return pout.toString();
	}

	public static void renamerTest(String tlaFile) throws BCompoundException, TLA2BException {
		Translator t = new Translator(tlaFile);
		Start start = t.translate();
		Renamer renamer = new Renamer(start);
		ASTPrettyPrinter aP = new ASTPrettyPrinter(start, renamer);
		start.apply(aP);
		final BParser parser = new BParser("testcase");
		parser.parse(aP.getResultString(), false);
	}

	public static TestTypeChecker typeCheckString(String moduleString) throws TLA2BException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		TestTypeChecker testTypeChecker = new TestTypeChecker();
		testTypeChecker.startTest(moduleString, null);
		return testTypeChecker;

	}

	public static TestTypeChecker typeCheckString(String moduleString, String configString) throws TLA2BException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		TestTypeChecker testTypeChecker = new TestTypeChecker();
		testTypeChecker.startTest(moduleString, configString);
		return testTypeChecker;
	}

	public static TestTypeChecker typeCheck(String moduleFileName) throws TLA2BException {
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
		return getTreeAsString(startNode);
	}

	public static String getAstStringofBExpressionString(final String expr) throws BCompoundException {
		final BParser parser = new BParser("testcase");
		final Start startNode = parser.parse("#FORMULA " + expr, false);
		return getTreeAsString(startNode);
	}

}
