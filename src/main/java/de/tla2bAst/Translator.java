package de.tla2bAst;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.io.OutputStreamWriter;
import java.io.PrintWriter;
import java.io.UnsupportedEncodingException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.util.Hashtable;

import de.be4.classicalb.core.parser.BParser;
import de.be4.classicalb.core.parser.Definitions;
import de.be4.classicalb.core.parser.analysis.prolog.RecursiveMachineLoader;
import de.be4.classicalb.core.parser.exceptions.BCompoundException;
import de.be4.classicalb.core.parser.exceptions.PreParseException;
import de.be4.classicalb.core.parser.node.Node;
import de.be4.classicalb.core.parser.node.Start;
import de.be4.classicalb.core.parser.util.PrettyPrinter;
import de.be4.classicalb.core.parser.util.SuffixIdentifierRenaming;
import de.tla2b.analysis.InstanceTransformation;
import de.tla2b.analysis.PredicateVsExpression;
import de.tla2b.analysis.SpecAnalyser;
import de.tla2b.analysis.SymbolRenamer;
import de.tla2b.analysis.SymbolSorter;
import de.tla2b.analysis.TypeChecker;
import de.tla2b.analysis.UsedExternalFunctions;
import de.tla2b.config.ConfigfileEvaluator;
import de.tla2b.config.ModuleOverrider;
import de.tla2b.exceptions.FrontEndException;
import de.tla2b.exceptions.TLA2BException;
import de.tla2b.global.TranslationGlobals;
import de.tla2b.output.PrologPrinter;
import de.tla2b.translation.BMacroHandler;
import de.tla2b.translation.RecursiveFunctionHandler;
import de.tla2b.types.TLAType;
import de.tla2b.util.FileUtils;

import tla2sany.drivers.SANY;
import tla2sany.modanalyzer.SpecObj;
import tla2sany.semantic.ModuleNode;

import tlc2.tool.ModelConfig;

import util.ToolIO;

public class Translator implements TranslationGlobals {
	private String moduleFileName;
	private File moduleFile;
	private File configFile;
	private Start BAst;
	private Hashtable<Node, TLAType> typeTable;

	private Definitions bDefinitions;

	private BAstCreator bAstCreator;

	// private String moduleName;
	private ModuleNode moduleNode;
	private ModelConfig modelConfig;

	private SpecAnalyser specAnalyser;
	private TypeChecker typechecker;

	public Translator(String moduleFileName) throws FrontEndException {
		this.moduleFileName = moduleFileName;

		findModuleFile();
		findConfigFile();

		parse();
	}

	private void findConfigFile() {
		String configFileName = FileUtils.removeExtention(moduleFile.getAbsolutePath());
		configFileName = configFileName + ".cfg";
		configFile = new File(configFileName);
		if (!configFile.exists()) {
			configFile = null;
		}
	}

	private void findModuleFile() {
		moduleFile = new File(moduleFileName);
		if (!moduleFile.exists()) {
			throw new RuntimeException("Can not find module file: '" + moduleFileName + "'");
		}
		try {
			moduleFile = moduleFile.getCanonicalFile();
		} catch (IOException e) {
			throw new RuntimeException("Can not access module file: '" + moduleFileName + "'");
		}
	}

	/**
	 * External interface
	 */
	public static String translateModuleString(String moduleName, String moduleString, String configString)
			throws TLA2BException {
		Translator translator = new Translator(moduleName, moduleString, configString);
		Start bAST = translator.getBAST();
		PrettyPrinter pp = new PrettyPrinter();
		pp.setRenaming(new SuffixIdentifierRenaming());
		bAST.apply(pp);
		return pp.getPrettyPrint();
	}

	public Translator(String moduleName, String moduleString, String configString) throws TLA2BException {
		createTLATempFile(moduleString, moduleName);
		createCfgFile(configString, moduleName);
		parse();
		translate();
	}

	// Used for Testing in tla2bAST project
	public Translator(String moduleString, String configString) throws FrontEndException {
		String moduleName = "Testing";
		createTLATempFile(moduleString, moduleName);
		createCfgFile(configString, moduleName);
		parse();
	}

	private void createCfgFile(String configString, String moduleName) {
		modelConfig = null;
		if (configString != null) {
			configFile = new File("temp/" + moduleName + ".cfg");
			try {
				configFile.createNewFile();
				try (BufferedWriter out = new BufferedWriter(
					new OutputStreamWriter(Files.newOutputStream(configFile.toPath()), StandardCharsets.UTF_8))) {
					out.write(configString);
				}
			} catch (IOException e) {
				e.printStackTrace();
			}
		}
	}

	private void createTLATempFile(String moduleString, String moduleName) {
		File dir = new File("temp/");
		dir.mkdirs();
		dir.deleteOnExit();

		try {
			moduleFile = new File("temp/" + moduleName + ".tla");
			moduleFile.createNewFile();
			try (BufferedWriter out = new BufferedWriter(new OutputStreamWriter(Files.newOutputStream(moduleFile.toPath()), StandardCharsets.UTF_8))) {
				out.write(moduleString);
			}
			moduleFileName = moduleFile.getAbsolutePath();
		} catch (IOException e) {
			e.printStackTrace();
		}
	}

	public ModuleNode parseModule() throws de.tla2b.exceptions.FrontEndException {
		String fileName = moduleFile.getName();
		ToolIO.setUserDir(moduleFile.getParent());

		SpecObj spec = new SpecObj(fileName, null);
		try {
			SANY.frontEndMain(spec, fileName, ToolIO.out);
		} catch (tla2sany.drivers.FrontEndException e) {
			// should never happen
			e.printStackTrace();
		}

		if (spec.parseErrors.isFailure()) {
			throw new de.tla2b.exceptions.FrontEndException(
					allMessagesToString(ToolIO.getAllMessages()) + spec.parseErrors, spec);
		}

		if (spec.semanticErrors.isFailure()) {
			throw new de.tla2b.exceptions.FrontEndException(
					// allMessagesToString(ToolIO.getAllMessages())
					"" + spec.semanticErrors, spec);
		}

		// RootModule
		ModuleNode n = spec.getExternalModuleTable().rootModule;
		if (spec.getInitErrors().isFailure()) {
			System.err.println(spec.getInitErrors());
			return null;
		}

		if (n == null) { // Parse Error
			// System.out.println("Rootmodule null");
			throw new de.tla2b.exceptions.FrontEndException(allMessagesToString(ToolIO.getAllMessages()), spec);
		}

		return n;
	}

	public static String allMessagesToString(String[] allMessages) {
		StringBuilder sb = new StringBuilder();
		for (int i = 0; i < allMessages.length - 1; i++) {
			sb.append(allMessages[i]).append("\n");
		}
		return sb.toString();
	}

	private void parse() throws FrontEndException {
		moduleNode = parseModule();

		modelConfig = null;
		if (configFile != null) {
			modelConfig = new ModelConfig(configFile.getAbsolutePath(), new SimpleResolver());
			modelConfig.parse();
		}

	}

	public Start translate() throws TLA2BException {
		InstanceTransformation trans = new InstanceTransformation(moduleNode);
		trans.start();

		SymbolSorter symbolSorter = new SymbolSorter(moduleNode);
		symbolSorter.sort();
		PredicateVsExpression predicateVsExpression = new PredicateVsExpression(moduleNode);

		ConfigfileEvaluator conEval = null;
		if (modelConfig != null) {

			conEval = new ConfigfileEvaluator(modelConfig, moduleNode);
			conEval.start();

			ModuleOverrider modOver = new ModuleOverrider(moduleNode, conEval);
			modOver.start();
			specAnalyser = SpecAnalyser.createSpecAnalyser(moduleNode, conEval);
		} else {
			specAnalyser = SpecAnalyser.createSpecAnalyser(moduleNode);
		}
		specAnalyser.start();
		typechecker = new TypeChecker(moduleNode, conEval, specAnalyser);
		typechecker.start();
		SymbolRenamer symRenamer = new SymbolRenamer(moduleNode, specAnalyser);
		symRenamer.start();
		UsedExternalFunctions usedExternalFunctions = new UsedExternalFunctions(moduleNode, specAnalyser);
		RecursiveFunctionHandler recursiveFunctionHandler = new RecursiveFunctionHandler(specAnalyser);
		BMacroHandler bMacroHandler = new BMacroHandler(specAnalyser, conEval);
		bAstCreator = new BAstCreator(moduleNode, conEval, specAnalyser, usedExternalFunctions, predicateVsExpression,
				bMacroHandler, recursiveFunctionHandler);

		this.BAst = bAstCreator.getStartNode();
		this.typeTable = bAstCreator.getTypeTable();
		this.bDefinitions = bAstCreator.getBDefinitions();
		return BAst;
	}

	public void createProbFile() {
		String fileName = FileUtils.removeExtention(moduleFile.getAbsolutePath());
		fileName = fileName + ".prob";
		File probFile;
		probFile = new File(fileName);
		try {
			probFile.createNewFile();
		} catch (IOException e) {
			System.err.printf("Could not create File %s.%n", probFile.getName());
			System.exit(-1);
		}

		BParser bParser = new BParser();

		try {
			bParser.getDefinitions().addDefinitions(getBDefinitions());
			final RecursiveMachineLoader rml = parseAllMachines(getBAST(), getModuleFile(), bParser);

			String moduleName = FileUtils.removeExtention(moduleFile.getName());
			PrologPrinter prologPrinter = new PrologPrinter(rml, bParser, moduleFile, moduleName, typeTable);
			prologPrinter.setPositions(bAstCreator.getSourcePositions());

			PrintWriter outWriter = new PrintWriter(probFile, "UTF-8");
			prologPrinter.printAsProlog(outWriter, false);
			outWriter.close();
			System.out.println(probFile.getAbsolutePath() + " created.");

		} catch (BCompoundException | FileNotFoundException | PreParseException | UnsupportedEncodingException e) {
			System.err.println(e.getMessage());
			System.exit(-1);
		}
	}

	public void createMachineFile() {
		String bFile = FileUtils.removeExtention(moduleFile.getAbsolutePath());
		bFile = bFile + "_tla.txt";

		File machineFile;
		machineFile = new File(bFile);
		if (machineFile.exists()) {
			try {
				BufferedReader in;
				in = new BufferedReader(new FileReader(machineFile));
				String firstLine = in.readLine();
				in.close();
				if (firstLine != null && !firstLine.startsWith("/*@ generated by TLA2B ")) {
					System.err.println("Error: File " + machineFile.getName() + " already exists"
							+ " and was not generated by TLA2B.\n" + "Delete or move this file.");
					System.exit(-1);
				}
			} catch (IOException e) {
				System.err.println(e.getMessage());
				System.exit(-1);
			}
		}

		try {
			machineFile.createNewFile();
		} catch (IOException e) {
			System.err.printf("Could not create File %s.%n", machineFile.getName());
			System.exit(-1);
		}

		PrettyPrinter pp = new PrettyPrinter();
		pp.setRenaming(new SuffixIdentifierRenaming());
		BAst.apply(pp);
		String result = "/*@ generated by TLA2B " + VERSION_NUMBER + " */\n" + pp.getPrettyPrint();

		try {
			try (BufferedWriter out = new BufferedWriter(new OutputStreamWriter(Files.newOutputStream(machineFile.toPath()), StandardCharsets.UTF_8))) {
				out.write(result);
			}
			System.out.println("B-Machine " + machineFile.getAbsolutePath() + " created.");
		} catch (IOException e) {
			System.err.println("Error while creating file '" + machineFile.getAbsolutePath() + "'.");
			System.exit(-1);
		}

	}

	public static RecursiveMachineLoader parseAllMachines(final Start ast, final File f, final BParser bparser)
			throws BCompoundException {
		final RecursiveMachineLoader rml = new RecursiveMachineLoader(f.getParent(), bparser.getContentProvider());
		rml.loadAllMachines(f, ast, bparser.getDefinitions());
		return rml;
	}

	public Start translateExpression(String tlaExpression) throws TLA2BException {
		ExpressionTranslator expressionTranslator = new ExpressionTranslator(tlaExpression, this);
		expressionTranslator.parse();
		return expressionTranslator.translateIncludingModel();
	}

	public static Start translateTlaExpression(String tlaExpression) {
		ExpressionTranslator expressionTranslator = new ExpressionTranslator(tlaExpression);
		expressionTranslator.parse();
		expressionTranslator.translate();
		return expressionTranslator.getBExpressionParseUnit();
	}

	public Definitions getBDefinitions() {
		return bDefinitions;
	}

	public ModuleNode getModuleNode() {
		return moduleNode;
	}

	protected TypeChecker getTypeChecker() {
		return this.typechecker;
	}

	protected SpecAnalyser getSpecAnalyser() {
		return this.specAnalyser;
	}

	public Start getBAST() {
		return BAst;
	}

	public File getModuleFile() {
		return moduleFile;
	}

	public Hashtable<Node, TLAType> getTypeTable() {
		return this.typeTable;
	}

}
