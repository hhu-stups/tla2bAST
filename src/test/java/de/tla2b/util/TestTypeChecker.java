package de.tla2b.util;

import java.util.Hashtable;

import de.tla2b.exceptions.TLA2BException;
import de.tla2b.global.TranslationGlobals;
import de.tla2b.types.TLAType;
import de.tla2bAst.Translator;
import tla2sany.semantic.FormalParamNode;
import tla2sany.semantic.ModuleNode;
import tla2sany.semantic.OpDeclNode;
import tla2sany.semantic.OpDefNode;
import tla2sany.semantic.SemanticNode;

public class TestTypeChecker implements TranslationGlobals {

	public ModuleNode moduleNode;
	public final int toolId = 5;
	private final Hashtable<String, TLAType> constants;
	private final Hashtable<String, TLAType> variables;
	private final Hashtable<String, DefCon> definitions;

	public TestTypeChecker() {
		constants = new Hashtable<>();
		variables = new Hashtable<>();
		definitions = new Hashtable<>();
	}

	public void startTest(String moduleString, String configString)
			throws TLA2BException {
		Translator translator = new Translator(moduleString, configString);
		translator.translate();
		moduleNode = translator.getModuleNode();
		init();
	}
	
	public void start(String moduleFileName)
			throws TLA2BException {
		Translator translator = new Translator(moduleFileName);
		translator.translate();
		moduleNode = translator.getModuleNode();
		init();
	}


	private TLAType getBType(SemanticNode node){
		TLAType type = (TLAType) node.getToolObject(toolId);
		return type;
	}
	
	private void init() {
		for (int i = 0; i < moduleNode.getConstantDecls().length; i++) {
			OpDeclNode con = moduleNode.getConstantDecls()[i];
			constants.put(con.getName().toString(),
					getBType(con));
		}

		for (int i = 0; i < moduleNode.getVariableDecls().length; i++) {
			OpDeclNode var = moduleNode.getVariableDecls()[i];
			variables.put(var.getName().toString(),
					getBType(var));
		}

		for (int i = 0; i < moduleNode.getOpDefs().length; i++) {
			OpDefNode def = moduleNode.getOpDefs()[i];
			DefCon defCon = new DefCon(getBType(def));
			if (defCon.getType() == null)
				continue;

			if (STANDARD_MODULES.contains(def
					.getOriginallyDefinedInModuleNode().getName().toString())
					|| STANDARD_MODULES.contains(def.getSource()
							.getOriginallyDefinedInModuleNode().getName()
							.toString())) {
				continue;
			}

			for (int j = 0; j < def.getParams().length; j++) {
				FormalParamNode p = def.getParams()[j];
				defCon.parameters.put(p.getName().toString(),
						getBType(p));
			}
			definitions.put(def.getName().toString(), defCon);
		}
	}

	
	public String getConstantType(String conName) {
		return constants.get(conName).toString();
	}
	
	public String getVariableType(String varName){
		return variables.get(varName).toString();
	}

	public String getDefinitionType(String defName){
		return definitions.get(defName).getType().toString();
	}

	public String getDefinitionParamType(String defName, String paramName){
		return definitions.get(defName).getParams().get(paramName).toString();
	}

	public static class DefCon {
		private final Hashtable<String, TLAType> parameters;
		private TLAType type;

		private DefCon(TLAType t) {
			parameters = new Hashtable<>();
			type = t;
		}

		public Hashtable<String, TLAType> getParams() {
			return parameters;
		}

		public TLAType getType() {
			return type;
		}

		public void setType(TLAType type) {
			this.type = type;
		}
	}
}
