package de.tla2bAst;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.io.Writer;
import java.util.Date;

import de.be4.classicalb.core.parser.Definitions;
import de.be4.classicalb.core.parser.node.Start;
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
import de.tla2b.output.ASTPrettyPrinter;
import de.tla2b.pprint.BMachinePrinter;
import de.tla2b.translation.BMacroHandler;
import de.tla2b.translation.RecursiveFunctionHandler;
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

	private Definitions bDefinitions;

	// private String moduleName;
	private ModuleNode moduleNode;
	private ModelConfig modelConfig;

	private String bMachineString;

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
			throw new RuntimeException("Can not find module file: '"
					+ moduleFileName + "'");
		}
	}

	// Used for Testing
	public Translator(String moduleString, String configString)
			throws FrontEndException {
		String moduleName = "Testing";
		File dir = new File("temp/");
		dir.mkdirs();

		try {
			moduleFile = new File("temp/" + moduleName + ".tla");
			moduleFile.createNewFile();
			FileWriter fw = new FileWriter(moduleFile);
			fw.write(moduleString);
			fw.close();
			// f.deleteOnExit();
			moduleFileName = moduleFile.getAbsolutePath();
		} catch (IOException e) {
			e.printStackTrace();
		}

		modelConfig = null;
		if (configString != null) {
			configFile = new File("temp/" + moduleName + ".cfg");
			try {
				configFile.createNewFile();
				FileWriter fw = new FileWriter(configFile);
				fw.write(configString);
				fw.close();
			} catch (IOException e) {
				e.printStackTrace();
			}
			// f.deleteOnExit();
		}
		dir.deleteOnExit();

		parse();
	}

	public ModuleNode parseModule()
			throws de.tla2b.exceptions.FrontEndException {
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
					allMessagesToString(ToolIO.getAllMessages())
							+ spec.parseErrors, spec);
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
			throw new de.tla2b.exceptions.FrontEndException(
					allMessagesToString(ToolIO.getAllMessages()), spec);
		}

		return n;
	}

	public static String allMessagesToString(String[] allMessages) {
		StringBuilder sb = new StringBuilder();
		for (int i = 0; i < allMessages.length - 1; i++) {
			sb.append(allMessages[i] + "\n");
		}
		return sb.toString();
	}

	private void parse() throws FrontEndException {
		moduleNode = parseModule();

		modelConfig = null;
		if (configFile != null) {
			modelConfig = new ModelConfig(configFile.getAbsolutePath(),
					new SimpleResolver());
			modelConfig.parse();
		}

	}

	public Start translate() throws TLA2BException {
		InstanceTransformation trans = new InstanceTransformation(moduleNode);
		trans.start();

		SymbolSorter symbolSorter = new SymbolSorter(moduleNode);
		symbolSorter.sort();

		PredicateVsExpression predicateVsExpression = new PredicateVsExpression(
				moduleNode);

		SpecAnalyser specAnalyser;

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
		TypeChecker typechecker = new TypeChecker(moduleNode, conEval,
				specAnalyser);
		typechecker.start();
		// specAnalyser.evalIfThenElse();

		SymbolRenamer symRenamer = new SymbolRenamer(moduleNode, specAnalyser);
		symRenamer.start();
		// BMachinePrinter p = new BMachinePrinter(moduleNode, conEval,
		// specAnalyser);
		// bMachineString = p.start().toString();
		UsedExternalFunctions usedExternalFunctions = new UsedExternalFunctions(
				moduleNode, specAnalyser);
		RecursiveFunctionHandler recursiveFunctionHandler = new RecursiveFunctionHandler(
				specAnalyser);
		BMacroHandler bMacroHandler = new BMacroHandler(specAnalyser, conEval);
		BAstCreator bAstCreator = new BAstCreator(moduleNode, conEval,
				specAnalyser, usedExternalFunctions, predicateVsExpression,
				bMacroHandler, recursiveFunctionHandler);
		this.BAst = bAstCreator.getStartNode();
		this.bDefinitions = bAstCreator.getBDefinitions();
		return BAst;
	}

	public void createMachineFile() {
		String bFile = FileUtils.removeExtention(moduleFile.getAbsolutePath());
		bFile = bFile + "_tla.mch";

		File machineFile;
		machineFile = new File(bFile);
		if (machineFile.exists()) {
			try {
				BufferedReader in;
				in = new BufferedReader(new FileReader(machineFile));
				String firstLine = in.readLine();
				in.close();
				if (firstLine != null
						&& !firstLine.startsWith("/*@ generated by TLA2B ")) {
					System.err.println("Error: File " + machineFile.getName()
							+ " already exists"
							+ " and was not generated by TLA2B.\n"
							+ "Delete or move this file.");
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
			System.err.println(String.format("Could not create File %s.",
					machineFile.getName()));
			System.exit(-1);
		}

		ASTPrettyPrinter aP = new ASTPrettyPrinter();
		BAst.apply(aP);
		StringBuilder result = aP.getResultAsStringbuilder();
		result.insert(0, "/*@ generated by TLA2B " + VERSION + " " + new Date()
				+ " */\n");

		Writer fw = null;
		try {
			fw = new FileWriter(machineFile);
			fw.write(result.toString());
			fw.close();
			System.out.println("B-Machine " + machineFile.getAbsolutePath()
					+ " created.");
		} catch (IOException e) {
			System.err.println("Error while creating file '"
					+ machineFile.getAbsolutePath() + "'.");
			System.exit(-1);
		}

	}



	public Definitions getBDefinitions() {
		return bDefinitions;
	}

	public String getBMachineString() {
		return bMachineString;
	}

	public ModuleNode getModuleNode() {
		return moduleNode;
	}

}
