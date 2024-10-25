package de.tla2bAst;

import de.be4.classicalb.core.parser.BParser;
import de.be4.classicalb.core.parser.Definitions;
import de.be4.classicalb.core.parser.analysis.prolog.RecursiveMachineLoader;
import de.be4.classicalb.core.parser.exceptions.BCompoundException;
import de.be4.classicalb.core.parser.exceptions.PreParseException;
import de.be4.classicalb.core.parser.node.Node;
import de.be4.classicalb.core.parser.node.Start;
import de.be4.classicalb.core.parser.util.PrettyPrinter;
import de.be4.classicalb.core.parser.util.SuffixIdentifierRenaming;
import de.hhu.stups.sablecc.patch.PositionedNode;
import de.prob.prolog.output.PrologTermOutput;
import de.tla2b.analysis.*;
import de.tla2b.config.ConfigfileEvaluator;
import de.tla2b.config.ModuleOverrider;
import de.tla2b.exceptions.TLA2BFrontEndException;
import de.tla2b.exceptions.TLA2BException;
import de.tla2b.global.TranslationGlobals;
import de.tla2b.output.TlaTypePrinter;
import de.tla2b.translation.BMacroHandler;
import de.tla2b.translation.RecursiveFunctionHandler;
import de.tla2b.types.TLAType;
import de.tla2b.util.FileUtils;
import tla2sany.drivers.FrontEndException;
import tla2sany.drivers.SANY;
import tla2sany.modanalyzer.SpecObj;
import tla2sany.semantic.ModuleNode;
import tlc2.tool.impl.ModelConfig;
import util.ToolIO;

import java.io.*;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.util.Map;

public class Translator implements TranslationGlobals {
	private String moduleFileName;
	private File moduleFile;
	private File configFile;
	private Start BAst;
	private Map<Node, TLAType> types;

	private Definitions bDefinitions;

	private BAstCreator bAstCreator;

	// private String moduleName;
	private ModuleNode moduleNode;
	private ModelConfig modelConfig;

	private SpecAnalyser specAnalyser;
	private TypeChecker typechecker;

	public Translator(String moduleFileName) throws TLA2BFrontEndException {
		this.moduleFileName = moduleFileName;

		this.moduleFile = new File(moduleFileName);
		if (!moduleFile.exists()) {
			throw new RuntimeException("Can not find module file: '" + moduleFileName + "'");
		}
		try {
			this.moduleFile = moduleFile.getCanonicalFile();
		} catch (IOException e) {
			throw new RuntimeException("Can not access module file: '" + moduleFileName + "'");
		}

		this.configFile = new File(FileUtils.removeExtension(moduleFile.getAbsolutePath()) + ".cfg");
		if (!configFile.exists()) {
			this.configFile = null;
		}

		parse();
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
	public Translator(String moduleString, String configString) throws TLA2BFrontEndException {
		String moduleName = "Testing";
		createTLATempFile(moduleString, moduleName);
		createCfgFile(configString, moduleName);
		parse();
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

	private void parse() throws TLA2BFrontEndException {
		moduleNode = parseModule();

		modelConfig = null;
		if (configFile != null) {
			modelConfig = new ModelConfig(configFile.getAbsolutePath(), new SimpleResolver());
			modelConfig.parse();
		}
	}

	public ModuleNode parseModule() throws TLA2BFrontEndException {
		String fileName = moduleFile.getName();
		ToolIO.setUserDir(moduleFile.getParent());

		SpecObj spec = new SpecObj(fileName, null);
		try {
			SANY.frontEndMain(spec, fileName, ToolIO.out);
		} catch (FrontEndException e) {
			// should never happen
			throw new RuntimeException("Could not parse module: '" + fileName + "'", e);
		}

		if (spec.getParseErrors().isFailure()) {
			throw new TLA2BFrontEndException(allMessagesToString(ToolIO.getAllMessages()) + spec.getParseErrors(), spec);
		}

		if (spec.getSemanticErrors().isFailure()) {
			throw new TLA2BFrontEndException(allMessagesToString(ToolIO.getAllMessages()) + spec.getSemanticErrors(), spec);
		}

		// RootModule
		ModuleNode n = spec.getExternalModuleTable().getRootModule();
		if (spec.getInitErrors().isFailure()) {
			throw new TLA2BFrontEndException(spec.getInitErrors().toString(), spec);
		}

		if (n == null) { // Parse Error
			throw new TLA2BFrontEndException(allMessagesToString(ToolIO.getAllMessages()), spec);
		}

		return n;
	}

	public static String allMessagesToString(String[] allMessages) {
		return String.join("\n", allMessages) + "\n";
	}

	public Start translate() throws TLA2BException {
		InstanceTransformation.run(moduleNode);
		SymbolSorter.sort(moduleNode);

		ConfigfileEvaluator conEval = null;
		if (modelConfig != null) {
			conEval = new ConfigfileEvaluator(modelConfig, moduleNode);
			conEval.start();

			ModuleOverrider.run(moduleNode, conEval);
			specAnalyser = SpecAnalyser.createSpecAnalyser(moduleNode, conEval);
		} else {
			specAnalyser = SpecAnalyser.createSpecAnalyser(moduleNode);
		}
		specAnalyser.start();
		typechecker = new TypeChecker(moduleNode, conEval, specAnalyser);
		typechecker.start();
		SymbolRenamer.run(moduleNode, specAnalyser);
		bAstCreator = new BAstCreator(moduleNode, conEval, specAnalyser,
				new UsedExternalFunctions(moduleNode, specAnalyser),
				new PredicateVsExpression(moduleNode),
				new BMacroHandler(specAnalyser, conEval),
				new RecursiveFunctionHandler(specAnalyser));

		this.types = bAstCreator.getTypes();
		this.bDefinitions = bAstCreator.getBDefinitions();
		return this.BAst = bAstCreator.getStartNode();
	}

	public void createProbFile() {
		String fileName = FileUtils.removeExtension(moduleFile.getAbsolutePath());
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

			PrintWriter outWriter = new PrintWriter(probFile, "UTF-8");
			rml.printAsProlog(new PrologTermOutput(outWriter, false));
			outWriter.close();
			System.out.println(probFile.getAbsolutePath() + " created.");

		} catch (BCompoundException | FileNotFoundException | PreParseException | UnsupportedEncodingException e) {
			System.err.println(e.getMessage());
			System.exit(-1);
		}
	}

	public void createMachineFile() {
		String bFile = FileUtils.removeExtension(moduleFile.getAbsolutePath());
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

	public RecursiveMachineLoader parseAllMachines(final Start ast, final File f, final BParser bparser) throws BCompoundException {
		final RecursiveMachineLoader rml = new RecursiveMachineLoader(f.getParent(), bparser.getContentProvider());
		rml.loadAllMachines(f, ast, bparser.getDefinitions());
		// this is required for correct positions in ProB2(-UI) when rml.printAsProlog is called
		rml.setPositionPrinter(new TlaTypePrinter(rml.getNodeIdMapping(), bAstCreator.getTypes()));
		return rml;
	}

	public Start translateExpressionIncludingModel(String tlaExpression) throws TLA2BException {
		ExpressionTranslator expressionTranslator = new ExpressionTranslator(tlaExpression, this);
		expressionTranslator.parse();
		return expressionTranslator.translateIncludingModel();
	}

	@Deprecated
	public Start translateExpression(String tlaExpression) throws TLA2BException {
		return this.translateExpressionIncludingModel(tlaExpression);
	}

	public static Start translateExpressionWithoutModel(String tlaExpression) {
		ExpressionTranslator expressionTranslator = new ExpressionTranslator(tlaExpression);
		expressionTranslator.parse();
		return expressionTranslator.translateWithoutModel();
	}

	@Deprecated
	public static Start translateTlaExpression(String tlaExpression) {
		return translateExpressionWithoutModel(tlaExpression);
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

	public Map<Node, TLAType> getTypes() {
		return this.types;
	}

}
