package de.tla2b.translation;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Set;

import tla2sany.semantic.ASTConstants;
import tla2sany.semantic.AssumeNode;
import tla2sany.semantic.ExprNode;
import tla2sany.semantic.ExprOrOpArgNode;
import tla2sany.semantic.OpApplNode;
import tla2sany.semantic.OpDefNode;
import tlc2.tool.ToolGlobals;
import de.tla2b.analysis.AbstractASTVisitor;
import de.tla2b.analysis.BOperation;
import de.tla2b.analysis.SpecAnalyser;
import de.tla2b.global.TranslationGlobals;

public class BDefinitionsFinder extends AbstractASTVisitor implements ASTConstants, ToolGlobals, TranslationGlobals {
	private final HashSet<OpDefNode> bDefinitionsSet = new HashSet<>();

	public BDefinitionsFinder(SpecAnalyser specAnalyser) {
		if (specAnalyser.getConfigFileEvaluator() != null) {
			bDefinitionsSet.addAll(specAnalyser.getConfigFileEvaluator().getConstantOverrideTable().values());
			bDefinitionsSet.addAll(specAnalyser.getConfigFileEvaluator().getOperatorOverrideTable().values());
		}

		for (BOperation op : specAnalyser.getBOperations()) {
			visitExprNode(op.getNode());
			ArrayList<OpApplNode> existQuans = op.getExistQuans();
			for (OpApplNode opApplNode : existQuans) {
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

		for (OpDefNode def : specAnalyser.getInvariants()) {
			bDefinitionsSet.add(def);
		}

		for (OpDefNode opDef : specAnalyser.getModuleNode().getOpDefs()) {
			String defName = opDef.getName().toString();
			// GOAL, ANIMATION_FUNCTION, ANIMATION_IMGxx, SET_PREF_xxx,
			if (defName.equals("GOAL") || defName.startsWith("ANIMATION_") || defName.startsWith("CUSTOM_GRAPH_")
			        || defName.startsWith("ASSERT_CTL") || defName.startsWith("ASSERT_LTL") 
					|| defName.startsWith("SET_PREF_") || defName.startsWith("HEURISTIC_FUNCTION")
					|| defName.startsWith("VISB_SVG_")  // VISB_SVG_OBJECTS, VISB_SVG_UPDATES, VISB_SVG_HOVERS
					|| defName.equals("VISB_JSON_FILE")
					|| defName.startsWith("GAME_")  // GAME_OVER, GAME_PLAYER, GAME_MCTS_RUNS
					|| defName.startsWith("SCOPE") || defName.startsWith("scope_")) {
				bDefinitionsSet.add(opDef);
			}
		}

		HashSet<OpDefNode> temp = new HashSet<>(bDefinitionsSet);
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
