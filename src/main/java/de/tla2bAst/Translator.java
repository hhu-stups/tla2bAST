package de.tla2bAst;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;

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
import de.tla2b.pprint.BMachinePrinter;
import tla2sany.semantic.ModuleNode;
import tlc2.tool.ModelConfig;
import util.FileUtil;
import util.ToolIO;

public class Translator {
	private String moduleFileName;
	private String configFileName;

	private Definitions bDefinitions;

	private String moduleName;
	private ModuleNode moduleNode;
	private ModelConfig modelConfig;

	private String bMachineString;

	public Translator(String moduleFileName, String configFileName)
			throws FrontEndException {
		this.moduleFileName = moduleFileName;
		this.configFileName = configFileName;

		parse();
	}

	// Used for Testing
	public Translator(String moduleString, String configString, int i)
			throws FrontEndException {
		moduleName = "Testing";
		File dir = new File("temp/");
		dir.mkdirs();

		try {
			File f = new File("temp/" + moduleName + ".tla");
			f.createNewFile();
			FileWriter fw = new FileWriter(f);
			fw.write(moduleString);
			fw.close();
			// f.deleteOnExit();
			moduleFileName = f.getAbsolutePath();
		} catch (IOException e) {
			e.printStackTrace();
		}

		modelConfig = null;
		if (configString != null) {
			File f = new File("temp/" + moduleName + ".cfg");

			try {
				f.createNewFile();
				FileWriter fw = new FileWriter(f);
				fw.write(configString);
				fw.close();
			} catch (IOException e) {
				e.printStackTrace();
			}
			// f.deleteOnExit();
			configFileName = f.getAbsolutePath();
		}
		dir.deleteOnExit();

		parse();
	}

	// Used for Testing
	public Translator(String moduleString) throws FrontEndException {
		moduleName = "Testing";
		File dir = new File("temp/");
		dir.mkdirs();

		try {
			File f = new File("temp/" + moduleName + ".tla");
			f.createNewFile();
			FileWriter fw = new FileWriter(f);
			fw.write(moduleString);
			fw.close();
			// f.deleteOnExit();
			moduleFileName = f.getAbsolutePath();
		} catch (IOException e) {
			e.printStackTrace();
		}

		parseModule();
	}

	private void parseModule() throws FrontEndException {
		moduleName = evalFileName(moduleFileName);

		TLAParser tlaParser = new TLAParser(null);
		moduleNode = tlaParser.parseModule(moduleName);
	}

	private void parse() throws FrontEndException {
		moduleName = evalFileName(moduleFileName);

		TLAParser tlaParser = new TLAParser(null);
		moduleNode = tlaParser.parseModule(moduleName);

		modelConfig = null;
		if (configFileName != null) {
			File f = new File(configFileName);
			if (f.exists()) {
				modelConfig = new ModelConfig(f.getName(), null);
				modelConfig.parse();
			}
		} else {
			String fileNameWithoutSuffix = moduleFileName;
			if (fileNameWithoutSuffix.toLowerCase().endsWith(".tla")) {
				fileNameWithoutSuffix = fileNameWithoutSuffix.substring(0,
						fileNameWithoutSuffix.length() - 4);
			}
			String configFile = fileNameWithoutSuffix + ".cfg";
			File f = new File(configFile);
			if (f.exists()) {
				modelConfig = new ModelConfig(f.getName(), null);
				modelConfig.parse();
			}
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
			specAnalyser = new SpecAnalyser(moduleNode, conEval);
		} else {
			specAnalyser = new SpecAnalyser(moduleNode);
		}

		specAnalyser.start();

		TypeChecker typechecker = new TypeChecker(moduleNode, conEval,
				specAnalyser);
		typechecker.start();

		specAnalyser.evalIfThenElse();

		SymbolRenamer symRenamer = new SymbolRenamer(moduleNode, specAnalyser);
		symRenamer.start();
		BMachinePrinter p = new BMachinePrinter(moduleNode, conEval,
				specAnalyser);
		bMachineString = p.start().toString();

		UsedExternalFunctions usedExternalFunctions = new UsedExternalFunctions(
				moduleNode, specAnalyser);

		BAstCreator bAstCreator = new BAstCreator(moduleNode, conEval,
				specAnalyser, usedExternalFunctions, predicateVsExpression);

		this.bDefinitions = bAstCreator.getBDefinitions();

		return bAstCreator.getStartNode();
	}

	public static String evalFileName(String name) {
		if (name.toLowerCase().endsWith(".tla")) {
			name = name.substring(0, name.length() - 4);
		}

		if (name.toLowerCase().endsWith(".cfg")) {
			name = name.substring(0, name.length() - 4);
		}

		String sourceModuleName = name.substring(name
				.lastIndexOf(FileUtil.separator) + 1);

		String path = name.substring(0,
				name.lastIndexOf(FileUtil.separator) + 1);
		if (!path.equals(""))
			ToolIO.setUserDir(path);
		return sourceModuleName;
	}

	public Definitions getBDefinitions() {
		return bDefinitions;
	}

	public String getBMachineString() {
		return bMachineString;
	}

}
