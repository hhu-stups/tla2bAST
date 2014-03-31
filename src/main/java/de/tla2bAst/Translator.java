package de.tla2bAst;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;

import de.be4.classicalb.core.parser.node.Node;
import de.tla2b.analysis.InstanceTransformation;
import de.tla2b.analysis.SpecAnalyser;
import de.tla2b.analysis.SymbolRenamer;
import de.tla2b.analysis.SymbolSorter;
import de.tla2b.analysis.TypeChecker;
import de.tla2b.config.ConfigfileEvaluator;
import de.tla2b.config.ModuleOverrider;
import de.tla2b.exceptions.ConfigFileErrorException;
import de.tla2b.exceptions.FrontEndException;
import de.tla2b.exceptions.NotImplementedException;
import de.tla2b.exceptions.SemanticErrorException;
import de.tla2b.exceptions.TLA2BException;
import de.tla2b.pprint.BAstCreator;
import de.tla2b.pprint.BMachinePrinter;
import tla2sany.semantic.ModuleNode;
import tlc2.tool.ModelConfig;
import util.FileUtil;
import util.ToolIO;

public class Translator {
	private String moduleFileName;
	private String configFileName;
	
	
	
	private String moduleName;
	private ModuleNode moduleNode;
	private ModelConfig modelConfig;

	public Translator(String moduleFileName, String configFileName) {
		this.moduleFileName = moduleFileName;
		this.configFileName	= configFileName;
		
		parse();
	}
	
	private void parse(){
		moduleName = evalFileName(moduleFileName);

		TLAParser tlaParser = new TLAParser(null);
		moduleNode = tlaParser.parseModule(moduleName);

		modelConfig = null;
		if (configFileName != null) {
			modelConfig = new ModelConfig(configFileName, null);
			modelConfig.parse();
		}
	}

	public Translator(String moduleString, String configString, int i) {
		moduleName = "Testing";
		File dir = new File("temp/");
		dir.mkdirs();

		try {
			File f = new File("temp/" + moduleName + ".tla");
			f.createNewFile();
			FileWriter fw = new FileWriter(f);
			fw.write(moduleString);
			fw.close();
			f.deleteOnExit();
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
			f.deleteOnExit();
			configFileName = f.getAbsolutePath();
		}
		dir.deleteOnExit();
		
		parse();
	}

	public Node translate() throws TLA2BException {
		InstanceTransformation trans = new InstanceTransformation(moduleNode);
		trans.start();

		SymbolSorter symbolSorter = new SymbolSorter(moduleNode);
		symbolSorter.sort();

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
		//System.out.println(p.start());
		BAstCreator bAstCreator = new BAstCreator(moduleNode, conEval,
				specAnalyser);
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

}
