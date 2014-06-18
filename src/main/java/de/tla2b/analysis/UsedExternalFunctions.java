package de.tla2b.analysis;

import java.util.HashSet;
import java.util.Set;

import de.tla2b.global.BBuildIns;
import de.tla2b.global.BBuiltInOPs;
import tla2sany.semantic.ExprNode;
import tla2sany.semantic.ExprOrOpArgNode;
import tla2sany.semantic.ModuleNode;
import tla2sany.semantic.OpApplNode;
import tla2sany.semantic.OpDefNode;

public class UsedExternalFunctions extends AbstractASTVisitor implements BBuildIns{

	public enum EXTERNAL_FUNCTIONS {
		CHOOSE, ASSERT
	}

	private final Set<EXTERNAL_FUNCTIONS> usedExternalFunctions;

	public Set<EXTERNAL_FUNCTIONS> getUsedExternalFunctions() {
		return usedExternalFunctions;
	}

	public UsedExternalFunctions(ModuleNode moduleNode,
			SpecAnalyser specAnalyser) {
		usedExternalFunctions = new HashSet<UsedExternalFunctions.EXTERNAL_FUNCTIONS>();

		visitAssumptions(moduleNode.getAssumptions());

		for (OpDefNode def : specAnalyser.getUsedDefinitions()) {
			visitDefinition(def);
		}

	}

	@Override
	public void visitBuiltInNode(OpApplNode n) {
		switch (getOpCode(n.getOperator().getName())) {
		case OPCODE_case:
		case OPCODE_uc:
		case OPCODE_bc: {
			usedExternalFunctions.add(EXTERNAL_FUNCTIONS.CHOOSE);
		}
		default:
		}

		ExprNode[] in = n.getBdedQuantBounds();
		for (ExprNode exprNode : in) {
			visitExprNode(exprNode);
		}

		ExprOrOpArgNode[] arguments = n.getArgs();
		for (ExprOrOpArgNode exprOrOpArgNode : arguments) {
			// exprOrOpArgNode == null in case the OTHER construct
			if (exprOrOpArgNode != null) {
				visitExprOrOpArgNode(exprOrOpArgNode);
			}
		}
	}
	
	@Override
	public void visitBBuiltinsNode(OpApplNode n) {
		switch (BBuiltInOPs.getOpcode(n.getOperator().getName())) {
		
		case B_OPCODE_assert: {
			usedExternalFunctions.add(EXTERNAL_FUNCTIONS.ASSERT);
		}
		}
		
		
		ExprNode[] in = n.getBdedQuantBounds();
		for (ExprNode exprNode : in) {
			visitExprNode(exprNode);
		}

		ExprOrOpArgNode[] arguments = n.getArgs();
		for (ExprOrOpArgNode exprOrOpArgNode : arguments) {
			visitExprOrOpArgNode(exprOrOpArgNode);
		}
	}

}
