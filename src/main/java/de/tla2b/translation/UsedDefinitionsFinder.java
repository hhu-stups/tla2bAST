package de.tla2b.translation;

import de.be4.classicalb.core.parser.util.Utils;
import de.tla2b.analysis.AbstractASTVisitor;
import de.tla2b.analysis.SpecAnalyser;
import de.tla2b.global.BBuiltInOPs;
import de.tla2b.global.TranslationGlobals;
import tla2sany.semantic.ASTConstants;
import tla2sany.semantic.ModuleNode;
import tla2sany.semantic.OpApplNode;
import tla2sany.semantic.OpDefNode;
import tlc2.tool.ToolGlobals;

import java.util.Collection;
import java.util.HashSet;

public class UsedDefinitionsFinder extends AbstractASTVisitor implements ASTConstants, ToolGlobals, TranslationGlobals {

	private final HashSet<OpDefNode> usedDefinitions = new HashSet<>();

	public UsedDefinitionsFinder(SpecAnalyser specAnalyser) {

		if (specAnalyser.getConfigFileEvaluator() != null) {
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

		if (specAnalyser.getNext() != null) {
			visitExprNode(specAnalyser.getNext());
		}

		if (specAnalyser.getInitDef() != null) {
			usedDefinitions.add(specAnalyser.getInitDef());
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

		for (OpDefNode opDef : specAnalyser.getModuleNode().getOpDefs()) {
			String defName = opDef.getName().toString();
			// GOAL, ANIMATION_FUNCTION, ANIMATION_IMGxx, SET_PREF_xxx, etc.
			if (Utils.isProBSpecialDefinitionName(defName)) {
				usedDefinitions.add(opDef);
			}
		}
	}

	public HashSet<OpDefNode> getUsedDefinitions() {
		return usedDefinitions;
	}

	@Override
	public void visitUserDefinedNode(OpApplNode n) {
		super.visitUserDefinedNode(n);

		OpDefNode def = (OpDefNode) n.getOperator();
		ModuleNode moduleNode = def.getSource().getOriginallyDefinedInModuleNode();
		if (moduleNode.getName().toString().equals("TLA2B")) {
			return;
		}
		if (BBuiltInOPs.contains(def.getName())
			&& STANDARD_MODULES.contains(def.getSource().getOriginallyDefinedInModuleNode().getName().toString())) {
			return;
		}
		if (usedDefinitions.add(def)) {
			visitExprNode(def.getBody());
		}

	}
}
