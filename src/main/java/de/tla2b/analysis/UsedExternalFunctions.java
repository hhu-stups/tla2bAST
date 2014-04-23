package de.tla2b.analysis;

import java.util.HashSet;
import java.util.Hashtable;
import java.util.Set;

import tla2sany.semantic.ASTConstants;
import tla2sany.semantic.AssumeNode;
import tla2sany.semantic.ExprNode;
import tla2sany.semantic.ExprOrOpArgNode;
import tla2sany.semantic.LetInNode;
import tla2sany.semantic.ModuleNode;
import tla2sany.semantic.OpApplNode;
import tla2sany.semantic.OpDefNode;
import tla2sany.semantic.SemanticNode;
import tlc2.tool.BuiltInOPs;

public class UsedExternalFunctions extends BuiltInOPs implements ASTConstants {

	public enum EXTERNAL_FUNCTIONS {
		CHOOSE
	}

	private final Set<EXTERNAL_FUNCTIONS> usedExternalFunctions;

	public Set<EXTERNAL_FUNCTIONS> getUsedExternalFunctions() {
		return usedExternalFunctions;
	}

	public UsedExternalFunctions(ModuleNode moduleNode,
			SpecAnalyser specAnalyser) {
		usedExternalFunctions = new HashSet<UsedExternalFunctions.EXTERNAL_FUNCTIONS>();

		AssumeNode[] assumes = moduleNode.getAssumptions();
		for (int i = 0; i < assumes.length; i++) {
			AssumeNode assume = assumes[i];
			visitSemanticNode(assume.getAssume());
		}

		for (OpDefNode def : specAnalyser.getUsedDefinitions()) {
			visitSemanticNode(def.getBody());
		}

	}

	private void findExternalFunctions(Hashtable<Integer, SemanticNode> table) {
		for (SemanticNode sNode : table.values()) {
			if (sNode instanceof OpApplNode) {
				OpApplNode opApplNode = (OpApplNode) sNode;
				int kind = opApplNode.getOperator().getKind();
				if (kind == BuiltInKind) {
					switch (getOpCode(opApplNode.getOperator().getName())) {
					case OPCODE_case: {
						usedExternalFunctions.add(EXTERNAL_FUNCTIONS.CHOOSE);
					}
					case OPCODE_bc: {
						usedExternalFunctions.add(EXTERNAL_FUNCTIONS.CHOOSE);
					}
					}

				}
			}
		}
	}

	private void visitSemanticNode(SemanticNode s) {
		if (s == null)
			return;
		if (s instanceof OpApplNode) {
			OpApplNode opApplNode = (OpApplNode) s;
			int kind = opApplNode.getOperator().getKind();
			if (kind == BuiltInKind) {
				switch (getOpCode(opApplNode.getOperator().getName())) {
				case OPCODE_case:
				case OPCODE_bc:
				case OPCODE_uc: {
					usedExternalFunctions.add(EXTERNAL_FUNCTIONS.CHOOSE);
					break;
				}
				}

			}
			for (SemanticNode arg : opApplNode.getArgs()) {
				visitSemanticNode(arg);
			}

		}

		SemanticNode[] children = s.getChildren();
		if (children != null) {
			for (SemanticNode semanticNode : children) {
				visitSemanticNode(semanticNode);
			}
		}
	}

}
