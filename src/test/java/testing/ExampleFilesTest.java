package testing;

import java.io.File;
import java.util.ArrayList;

import de.be4.classicalb.core.parser.BParser;
import de.be4.classicalb.core.parser.node.Start;
import de.be4.classicalb.core.parser.util.PrettyPrinter;
import de.tla2b.util.AbstractParseModuleTest;
import de.tla2b.util.FileUtils;
import de.tla2b.util.PolySuite;
import de.tla2b.util.PolySuite.Config;
import de.tla2b.util.PolySuite.Configuration;
import de.tla2b.util.TestUtil;
import de.tla2bAst.Translator;

import org.junit.Test;
import org.junit.runner.RunWith;

import static org.junit.Assert.assertEquals;

@RunWith(PolySuite.class)
public class ExampleFilesTest extends AbstractParseModuleTest {

	private final File moduleFile;

	public ExampleFilesTest(File machine, Object result) {
		this.moduleFile = machine;
	}

	@Test
	public void testRunTLC() throws Exception {
		// String[] a = new String[] { moduleFile.getPath() };
		// runModule(moduleFile.getPath());
		Translator t = new Translator(moduleFile.getPath());
		Start start = t.translate();
		String resultTree = TestUtil.getTreeAsString(start);
		
		PrettyPrinter pp = new PrettyPrinter();
		// FIXME Is it intentional that we don't use SuffixIdentifierRenaming here?
		start.apply(pp);

		// parse pretty print result
		final BParser parser = new BParser("testcase");
		final Start ppStart = parser.parse(pp.getPrettyPrint(), false);
		String ppTree = TestUtil.getTreeAsString(ppStart);
		
		// comparing result with pretty print
		assertEquals(resultTree, ppTree);
		
		
		// machine file
		String machinePath = FileUtils.removeExtention(moduleFile.getPath())
				+ ".mch";
		File expectedMachine = new File(machinePath);

		final BParser expectedParser = new BParser("testcase");
		final Start expectedStart = expectedParser.parseFile(expectedMachine,
				false);

		String expectedTree = TestUtil.getTreeAsString(expectedStart);

		assertEquals(expectedTree, resultTree);
	}

	@Config
	public static Configuration getConfig() {
		final ArrayList<String> list = new ArrayList<String>();
		final ArrayList<String> ignoreList = new ArrayList<String>();

		list.add("./src/test/resources/prettyprint/OperationsTest/");
		// ignoreList.add("./src/test/resources/testing/");
		return getConfiguration2(list, ignoreList);
	}
}
