package de.tla2b.translation;

import java.util.ArrayList;

import tla2sany.semantic.ModuleNode;
import tla2sany.semantic.OpDefNode;
import de.tla2b.analysis.AbstractASTVisitor;
import de.tla2b.analysis.SpecAnalyser;
import de.tla2b.config.ConfigfileEvaluator;

public class BMacroHandler extends AbstractASTVisitor {

	public BMacroHandler(SpecAnalyser specAnalyser, ConfigfileEvaluator conEval) {
		ModuleNode moduleNode = specAnalyser.getModuleNode();
		ArrayList<OpDefNode> bDefs = new ArrayList<OpDefNode>();
		for (int i = 0; i < moduleNode.getOpDefs().length; i++) {
			OpDefNode def = moduleNode.getOpDefs()[i];
			if (specAnalyser.getBDefinitions().contains(def)) {
				if (conEval != null
						&& conEval.getConstantOverrideTable()
								.containsValue(def)) {
					continue;
				}
				bDefs.add(def);
			}
		}
		for (OpDefNode opDefNode : bDefs) {
			visitDefinition(opDefNode);
		}
	}
	
	@Override
	public void visitDefinition(OpDefNode def){
		
	}
	
}
