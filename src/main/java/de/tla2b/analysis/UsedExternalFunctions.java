package de.tla2b.analysis;

import java.util.HashSet;
import java.util.Set;

import de.be4.classicalb.core.parser.Definitions;
import de.be4.classicalb.core.parser.IDefinitions;
import de.be4.classicalb.core.parser.util.ASTBuilder;
import de.tla2b.global.BBuiltIns;
import de.tla2b.global.BBuiltInOPs;

import tla2sany.semantic.*;

import tlc2.tool.BuiltInOPs;
import tlc2.tool.ToolGlobals;

public class UsedExternalFunctions extends AbstractASTVisitor {

	private final Set<String> usedExternalFunctions = new HashSet<>();

	public static IDefinitions createDefinitions(SpecAnalyser specAnalyser) {
		UsedExternalFunctions externalFunctions = new UsedExternalFunctions(specAnalyser);
		IDefinitions definitions = new Definitions();
		if (externalFunctions.usedExternalFunctions.contains(ASTBuilder.CHOOSE)) {
			ASTBuilder.addChooseDefinition(definitions);
		}
		if (externalFunctions.usedExternalFunctions.contains(ASTBuilder.ASSERT_TRUE)) {
			ASTBuilder.addAssertTrueDefinition(definitions);
		}
		return definitions;
	}

	private UsedExternalFunctions(SpecAnalyser specAnalyser) {
		visitAssumptions(specAnalyser.getModuleNode().getAssumptions());
		for (OpDefNode def : specAnalyser.getUsedDefinitions()) {
			visitDefinition(def);
		}
	}

	@Override
	public void visitBuiltInNode(OpApplNode n) {
		switch (BuiltInOPs.getOpCode(n.getOperator().getName())) {
			case ToolGlobals.OPCODE_case:
			case ToolGlobals.OPCODE_uc:
			case ToolGlobals.OPCODE_bc: {
				usedExternalFunctions.add(ASTBuilder.CHOOSE);
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
		if (BBuiltInOPs.getOpcode(n.getOperator().getName()) == BBuiltIns.B_OPCODE_assert) {
			usedExternalFunctions.add(ASTBuilder.ASSERT_TRUE);
		}

		for (ExprNode exprNode : n.getBdedQuantBounds()) {
			visitExprNode(exprNode);
		}

		ExprOrOpArgNode[] arguments = n.getArgs();
		for (ExprOrOpArgNode exprOrOpArgNode : arguments) {
			visitExprOrOpArgNode(exprOrOpArgNode);
		}
	}
}
