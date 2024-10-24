package de.tla2b.util;

import de.tla2b.exceptions.TLA2BException;
import de.tla2b.global.TranslationGlobals;
import de.tla2b.types.TLAType;
import de.tla2bAst.Translator;
import tla2sany.semantic.FormalParamNode;
import tla2sany.semantic.ModuleNode;
import tla2sany.semantic.OpDeclNode;
import tla2sany.semantic.OpDefNode;
import tla2sany.semantic.SemanticNode;

import java.util.HashMap;
import java.util.Map;

public class TestTypeChecker implements TranslationGlobals {

	public final int toolId = 5;
	private final Map<String, TLAType> constants = new HashMap<>();
	private final Map<String, TLAType> variables = new HashMap<>();
	private final Map<String, TLAType> definitionTypes = new HashMap<>();
	private final Map<String, Map<String, TLAType>> definitionParamTypes = new HashMap<>();
	public ModuleNode moduleNode;

	public void startTest(String moduleString, String configString) throws TLA2BException {
		Translator translator = new Translator(moduleString, configString);
		translator.translate();
		moduleNode = translator.getModuleNode();
		init();
	}

	public void start(String moduleFileName) throws TLA2BException {
		Translator translator = new Translator(moduleFileName);
		translator.translate();
		moduleNode = translator.getModuleNode();
		init();
	}

	private TLAType getBType(SemanticNode node) {
		return (TLAType) node.getToolObject(toolId);
	}

	private void init() {
		for (int i = 0; i < moduleNode.getConstantDecls().length; i++) {
			OpDeclNode con = moduleNode.getConstantDecls()[i];
			constants.put(con.getName().toString(), getBType(con));
		}

		for (int i = 0; i < moduleNode.getVariableDecls().length; i++) {
			OpDeclNode var = moduleNode.getVariableDecls()[i];
			variables.put(var.getName().toString(), getBType(var));
		}

		for (int i = 0; i < moduleNode.getOpDefs().length; i++) {
			OpDefNode def = moduleNode.getOpDefs()[i];
			TLAType defType = getBType(def);
			if (defType == null
				|| STANDARD_MODULES.contains(def.getOriginallyDefinedInModuleNode().getName().toString())
				|| STANDARD_MODULES.contains(def.getSource().getOriginallyDefinedInModuleNode().getName().toString())) {
				continue;
			}

			Map<String, TLAType> params = new HashMap<>();
			for (int j = 0; j < def.getParams().length; j++) {
				FormalParamNode p = def.getParams()[j];
				params.put(p.getName().toString(), getBType(p));
			}
			definitionTypes.put(def.getName().toString(), defType);
			definitionParamTypes.put(def.getName().toString(), params);
		}
	}

	public String getConstantType(String conName) {
		return constants.get(conName).toString();
	}

	public String getVariableType(String varName) {
		return variables.get(varName).toString();
	}

	public String getDefinitionType(String defName) {
		return definitionTypes.get(defName).toString();
	}

	public String getDefinitionParamType(String defName, String paramName) {
		return definitionParamTypes.get(defName).get(paramName).toString();
	}
}
