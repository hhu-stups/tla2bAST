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
import tla2sany.drivers.SANY;
import tla2sany.modanalyzer.SpecObj;
import tla2sany.semantic.ModuleNode;
import tlc2.tool.ModelConfig;
import util.FileUtil;
import util.ToolIO;

public class Translator {
	private String moduleFileName;
	private File moduleFile;
	private File configFile;

	private Definitions bDefinitions;

	//private String moduleName;
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
		String configFileName = removeExtention(moduleFile.getAbsolutePath());
		configFileName = configFileName + ".cfg";
		configFile = new File(configFileName);
		if(!configFile.exists()){
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


	public  ModuleNode parseModule2() throws de.tla2b.exceptions.FrontEndException {
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
		moduleNode = parseModule2();
		
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
		System.out.println(bDefinitions.getDefinitionNames());
		return bAstCreator.getStartNode();
	}

	public static String removeExtention(String filePath) {
		File f = new File(filePath);

		// if it's a directory, don't remove the extention
		if (f.isDirectory())
			return filePath;

		String name = f.getName();

		// Now we know it's a file - don't need to do any special hidden
		// checking or contains() checking because of:
		final int lastPeriodPos = name.lastIndexOf('.');
		if (lastPeriodPos <= 0) {
			// No period after first character - return name as it was passed in
			return filePath;
		} else {
			// Remove the last period and everything after it
			File renamed = new File(f.getParent(), name.substring(0,
					lastPeriodPos));
			return renamed.getPath();
		}
	}
	
	public Definitions getBDefinitions() {
		return bDefinitions;
	}

	public String getBMachineString() {
		return bMachineString;
	}

}
