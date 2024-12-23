package de.tla2b.translation;

import de.be4.classicalb.core.parser.util.Utils;
import de.tla2b.analysis.AbstractASTVisitor;
import de.tla2b.analysis.BOperation;
import de.tla2b.analysis.SpecAnalyser;
import de.tla2b.global.TranslationGlobals;
import tla2sany.semantic.*;
import tlc2.tool.ToolGlobals;

import java.util.HashSet;
import java.util.Set;

public class BDefinitionsFinder extends AbstractASTVisitor implements ASTConstants, ToolGlobals, TranslationGlobals {
	private final Set<OpDefNode> bDefinitionsSet = new HashSet<>();

	public BDefinitionsFinder(SpecAnalyser specAnalyser) {
		if (specAnalyser.getConfigFileEvaluator() != null) {
			bDefinitionsSet.addAll(specAnalyser.getConfigFileEvaluator().getConstantOverrides().values());
			bDefinitionsSet.addAll(specAnalyser.getConfigFileEvaluator().getOperatorOverrides().values());
		}

		for (BOperation op : specAnalyser.getBOperations()) {
			visitExprNode(op.getNode());
			for (OpApplNode opApplNode : op.getExistQuans()) {
				ExprNode[] bdedQuantBounds = opApplNode.getBdedQuantBounds();
				for (ExprNode exprNode : bdedQuantBounds) {
					visitExprNode(exprNode);
				}
			}
		}

		if (specAnalyser.getInits() != null) {
			for (int i = 0; i < specAnalyser.getInits().size(); i++) {
				visitExprNode(specAnalyser.getInits().get(i));
			}
		}

		for (AssumeNode assume : specAnalyser.getModuleNode().getAssumptions()) {
			visitAssumeNode(assume);
		}

		bDefinitionsSet.addAll(specAnalyser.getInvariants());

		for (OpDefNode opDef : specAnalyser.getModuleNode().getOpDefs()) {
			String defName = opDef.getName().toString();
			// GOAL, ANIMATION_FUNCTION, ANIMATION_IMGxx, SET_PREF_xxx, etc.
			if (Utils.isProBSpecialDefinitionName(defName)) {
				bDefinitionsSet.add(opDef);
			}
		}

		Set<OpDefNode> temp = new HashSet<>(bDefinitionsSet);
		for (OpDefNode opDefNode : temp) {
			visitExprNode(opDefNode.getBody());
		}

	}

	@Override
	public void visitUserDefinedNode(OpApplNode n) {
		OpDefNode def = (OpDefNode) n.getOperator();
		if (bDefinitionsSet.add(def)) {
			// visit body only once
			visitExprNode(def.getBody());
		}
		for (ExprOrOpArgNode exprOrOpArgNode : n.getArgs()) {
			visitExprOrOpArgNode(exprOrOpArgNode);
		}
	}

	public Set<OpDefNode> getBDefinitionsSet() {
		return bDefinitionsSet;
	}

}
