package de.tla2b.translation;

import java.util.Collection;
import java.util.HashSet;

import tla2sany.semantic.ASTConstants;
import tla2sany.semantic.ModuleNode;
import tla2sany.semantic.OpApplNode;
import tla2sany.semantic.OpDefNode;
import tlc2.tool.ToolGlobals;
import de.tla2b.analysis.AbstractASTVisitor;
import de.tla2b.analysis.SpecAnalyser;
import de.tla2b.global.BBuiltInOPs;
import de.tla2b.global.TranslationGlobals;
import de.tla2b.types.IType;

public class UsedDefinitionsFinder extends AbstractASTVisitor implements
		ASTConstants, ToolGlobals, IType, TranslationGlobals {

	private final HashSet<OpDefNode> usedDefinitions = new HashSet<OpDefNode>();
	
	public UsedDefinitionsFinder(SpecAnalyser specAnalyser) {
		
		if(specAnalyser.getConfigFileEvaluator() != null){
			Collection<OpDefNode> cons = specAnalyser.getConfigFileEvaluator().getConstantOverrideTable().values();
			for (OpDefNode def : cons) {
				visitExprNode(def.getBody());
			}
			Collection<OpDefNode> ops = specAnalyser.getConfigFileEvaluator().getOperatorOverrideTable().values();
			for (OpDefNode def : cons) {
				visitExprNode(def.getBody());
			}
			usedDefinitions.addAll(cons);
			usedDefinitions.addAll(ops);
		}
		
		visitAssumptions(specAnalyser.getModuleNode().getAssumptions());
	
		
		if(specAnalyser.getNext() != null){
			visitExprNode(specAnalyser.getNext());
		}

		if (specAnalyser.getInits() != null) {
			for (int i = 0; i < specAnalyser.getInits().size(); i++) {
				visitExprNode(specAnalyser.getInits().get(i));
			}
		}
	
		if (specAnalyser.getInvariants() != null) {
			for (int i = 0; i < specAnalyser.getInvariants().size(); i++) {
				OpDefNode def = specAnalyser.getInvariants().get(i);
				usedDefinitions.add(def);
				visitExprNode(def.getBody());
			}
		}
	}

	public HashSet<OpDefNode> getUsedDefinitions(){
		return usedDefinitions;
	}
	
	@Override
	public void visitUserDefinedNode(OpApplNode n) {
		super.visitUserDefinedNode(n);
		
		OpDefNode def = (OpDefNode) n.getOperator();
		ModuleNode moduleNode = def.getSource()
				.getOriginallyDefinedInModuleNode();
		if (moduleNode.getName().toString().equals("TLA2B")) {
			return;
		}
		if (BBuiltInOPs.contains(def.getName())
				&& STANDARD_MODULES.contains(def.getSource()
						.getOriginallyDefinedInModuleNode().getName()
						.toString())) {
			return;
		}
		if (usedDefinitions.add(def)) {
			visitExprNode(def.getBody());
		}


	}
}
