package de.tla2b.prettyprintb;

import de.be4.classicalb.core.parser.BParser;
import de.be4.classicalb.core.parser.node.Start;
import de.be4.classicalb.core.parser.util.PrettyPrinter;
import de.tla2b.util.TestUtil;
import de.tla2bAst.Translator;
import org.junit.Ignore;
import org.junit.Test;

import java.io.File;

import static org.junit.Assert.assertEquals;

public class OperationsTest {
	@Ignore
	@Test
	public void testRunTLC() throws Exception {
		// String[] a = new String[] { moduleFile.getPath() };
		// runModule(moduleFile.getPath());
		Translator t = new Translator("src/test/resources/prettyprint/OperationsTest/OperationsTest.tla");
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
		File expectedMachine = new File("src/test/resources/prettyprint/OperationsTest/OperationsTest.mch");

		final BParser expectedParser = new BParser("testcase");
		final Start expectedStart = expectedParser.parseFile(expectedMachine);

		String expectedTree = TestUtil.getTreeAsString(expectedStart);

		assertEquals(expectedTree, resultTree);
	}
}
