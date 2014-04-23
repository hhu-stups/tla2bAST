/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package de.tla2b.util;

import static org.junit.Assert.assertEquals;

import java.io.BufferedReader;
import java.io.FileReader;
import java.io.IOException;

import de.be4.classicalb.core.parser.BParser;
import de.be4.classicalb.core.parser.exceptions.BException;
import de.be4.classicalb.core.parser.node.Node;
import de.be4.classicalb.core.parser.node.Start;
import de.tla2b.exceptions.FrontEndException;
import de.tla2b.exceptions.TLA2BException;
import de.tla2b.pprint.ASTPrettyPrinter;
import de.tla2b.translation.Tla2BTranslator;
import de.tla2bAst.Translator;
import tla2sany.semantic.AbortException;
import util.FileUtil;
import util.ToolIO;

public class TestUtil {

	public static StringBuilder translateString(String moduleString)
			throws FrontEndException, TLA2BException, AbortException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		Tla2BTranslator translator = new Tla2BTranslator();
		translator.startTest(moduleString, null);
		return translator.translate();
	}
	
	public static void runModule(String tlaFile) throws Exception{
		Translator t = new Translator(tlaFile);
		Start start = t.translate();
		System.out.println(t.getBMachineString());
		System.out.println("---------------------");
		//String printResult = getAstStringofBMachineString(t.getBMachineString());
		//System.out.println(printResult);
		//System.out.println(getTreeAsString(start));
		//BParser.printASTasProlog(System.out, new BParser(), new File("./test.mch"), resultNode, false, true, null);
		
		
		
		System.out.println("-------------------");
		ASTPrettyPrinter aP = new ASTPrettyPrinter();
		start.apply(aP);
		System.out.println(aP.getResult());

		
		final BParser parser = new BParser("testcase");
		final Start ppStart = parser.parse(aP.getResult(), false);
		
		
		String result = getTreeAsString(start);
		System.out.println(result);
		String ppResult = getTreeAsString(ppStart);
		System.out.println(ppResult);
		
		
		System.out.println("-------------------");
		
		assertEquals(result, ppResult);
	}
	
	public static void compare(String bMachine, String tlaModule) throws BException, TLA2BException{
		ToolIO.setMode(ToolIO.TOOL);
		String expected = getAstStringofBMachineString(bMachine);
		System.out.println(expected);
		
		Translator trans = new Translator(tlaModule, null);
		Start resultNode = trans.translate();
		String result = getTreeAsString(resultNode);
		System.out.println(result);
		ASTPrettyPrinter aP = new ASTPrettyPrinter();
		resultNode.apply(aP);
		System.out.println("-------------------");
		System.out.println(aP.getResult());
		final BParser parser = new BParser("testcase");
		Start ast = parser.parse(aP.getResult(), false);
		//BParser.printASTasProlog(System.out, new BParser(), new File("./test.mch"), resultNode, false, true, null);
		
		
		//System.out.println(result);
		assertEquals(expected, result);
		assertEquals(expected, getTreeAsString(ast));
	}
	
	public static void compareWithPrintResult(String tlaModule) throws Exception{
		ToolIO.setMode(ToolIO.TOOL);
		
		Translator trans = new Translator(tlaModule);
		Start resultNode = trans.translate();
		
		String printResult = getAstStringofBMachineString(trans.getBMachineString());
		
		//BParser.printASTasProlog(System.out, new BParser(), new File("./test.mch"), resultNode, false, true, null);
		
		String result = getTreeAsString(resultNode);
		assertEquals(printResult, result);
		System.out.println(result);
	}
	
	
	public static void compare(String bMachine, String tlaModule, String config) throws BException, TLA2BException{
		ToolIO.setMode(ToolIO.TOOL);
		String expected = getAstStringofBMachineString(bMachine);
		System.out.println(expected);
		
		Translator trans = new Translator(tlaModule, config);
		Start resultNode = trans.translate();
		
		//BParser.printASTasProlog(System.out, new BParser(), new File("./test.mch"), resultNode, false, true, null);
		
		String result = getTreeAsString(resultNode);
		System.out.println(result);
		assertEquals(expected, result);
	}
	
	public static String getTreeAsString(Node node){
		final Ast2String ast2String = new Ast2String();
		node.apply(ast2String);
		return ast2String.toString();
	}
	

	public static StringBuilder translateString(String moduleString, String configString)
			throws FrontEndException, TLA2BException, AbortException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		Tla2BTranslator translator = new Tla2BTranslator();
		translator.startTest(moduleString, configString);
		return translator.translate();
	}
	
	
	public static StringBuilder translate(String moduleFileName)
			throws FrontEndException, TLA2BException, AbortException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		moduleFileName = moduleFileName.replace('/', FileUtil.separatorChar);
		Tla2BTranslator translator = new Tla2BTranslator();
		translator.start(moduleFileName, null);
		StringBuilder res = translator.translate();
		return res;
	}
	
	public static StringBuilder translate(String moduleFileName, String configFileName)
			throws FrontEndException, TLA2BException {
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		moduleFileName = moduleFileName.replace('/', FileUtil.separatorChar);
		configFileName = configFileName.replace('/', FileUtil.separatorChar);
		Tla2BTranslator translator = new Tla2BTranslator();
		translator.start(moduleFileName, configFileName);
		return translator.translate();
	}
	
	
	public static TestTypeChecker typeCheckString(String moduleString) throws FrontEndException, TLA2BException{
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		TestTypeChecker testTypeChecker = new TestTypeChecker();
		testTypeChecker.startTest(moduleString, null);
		return testTypeChecker;
		
	}
	
	public static TestTypeChecker typeCheckString(String moduleString, String configString) throws FrontEndException, TLA2BException{
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		TestTypeChecker testTypeChecker = new TestTypeChecker();
		testTypeChecker.startTest(moduleString, configString);
		return testTypeChecker;
	}
	
	public static TestTypeChecker typeCheck(String moduleFileName) throws FrontEndException, TLA2BException{
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		moduleFileName = moduleFileName.replace('/', FileUtil.separatorChar);
		TestTypeChecker testTypeChecker = new TestTypeChecker();
		testTypeChecker.start(moduleFileName, null);
		return testTypeChecker;
	}
	
	public static TestTypeChecker typeCheck(String moduleFileName, String configFileName) throws FrontEndException, TLA2BException{
		ToolIO.setMode(ToolIO.TOOL);
		ToolIO.reset();
		moduleFileName = moduleFileName.replace('/', FileUtil.separatorChar);
		configFileName = configFileName.replace('/', FileUtil.separatorChar);
		TestTypeChecker testTypeChecker = new TestTypeChecker();
		testTypeChecker.start(moduleFileName, configFileName);
		return testTypeChecker;
	}


	public static String fileToString(String fileName) throws IOException {
		StringBuilder res = new StringBuilder();
		BufferedReader in = new BufferedReader(new FileReader(fileName));
		String str;
		while ((str = in.readLine()) != null) {
			res.append(str + "\n");
		}
		in.close();
		return res.toString();
	}


	public static String getAstStringofBMachineString(final String testMachine)
			throws BException {
		final BParser parser = new BParser("testcase");
		final Start startNode = parser.parse(testMachine, false);
		
		final Ast2String ast2String = new Ast2String();
		startNode.apply(ast2String);
		final String string = ast2String.toString();
		return string;
	}
	
	
}
