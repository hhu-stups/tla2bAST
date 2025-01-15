package de.tla2b.analysis;

import de.be4.classicalb.core.parser.Definitions;
import de.be4.classicalb.core.parser.IDefinitions;
import de.tla2b.global.BBuildIns;
import de.tla2b.global.BBuiltInOPs;
import tla2sany.semantic.*;

import java.util.HashSet;
import java.util.Set;

import static de.be4.classicalb.core.parser.util.ASTBuilder.*;

public class UsedExternalFunctions extends AbstractASTVisitor implements BBuildIns {

	private final Set<String> usedExternalFunctions = new HashSet<>();

	public static IDefinitions createDefinitions(SpecAnalyser specAnalyser) {
		UsedExternalFunctions externalFunctions = new UsedExternalFunctions(specAnalyser);
		IDefinitions definitions = new Definitions();
		if (externalFunctions.usedExternalFunctions.contains(CHOOSE)) {
			addChooseDefinition(definitions);
		}
		if (externalFunctions.usedExternalFunctions.contains(ASSERT_TRUE)) {
			addAssertTrueDefinition(definitions);
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
		switch (getOpCode(n.getOperator().getName())) {
			case OPCODE_case:
			case OPCODE_uc:
			case OPCODE_bc: {
				usedExternalFunctions.add(CHOOSE);
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
		if (BBuiltInOPs.getOpcode(n.getOperator().getName()) == B_OPCODE_assert) {
			usedExternalFunctions.add(ASSERT_TRUE);
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
