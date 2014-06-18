package de.tla2b.analysis;

import de.tla2b.global.BBuiltInOPs;
import tla2sany.semantic.ASTConstants;
import tla2sany.semantic.AssumeNode;
import tla2sany.semantic.AtNode;
import tla2sany.semantic.ExprNode;
import tla2sany.semantic.ExprOrOpArgNode;
import tla2sany.semantic.LetInNode;
import tla2sany.semantic.ModuleNode;
import tla2sany.semantic.NumeralNode;
import tla2sany.semantic.OpApplNode;
import tla2sany.semantic.OpDefNode;
import tla2sany.semantic.StringNode;
import tla2sany.semantic.SubstInNode;
import tlc2.tool.BuiltInOPs;

public class AbstractASTVisitor extends BuiltInOPs implements ASTConstants {

	public void visitModuleNode(ModuleNode moduleNode) {

		visitDefinitions(moduleNode.getOpDefs());

		visitAssumptions(moduleNode.getAssumptions());
	}

	public void visitDefinitions(OpDefNode[] opDefs) {
		for (OpDefNode opDefNode : opDefs) {
			visitDefinition(opDefNode);
		}
	}

	public void visitAssumptions(AssumeNode[] assumptions) {
		for (AssumeNode assumeNode : assumptions) {
			visitAssumeNode(assumeNode);
		}
	}

	public void visitAssumeNode(AssumeNode assumeNode) {
		visitExprNode(assumeNode.getAssume());
	}

	public void visitDefinition(OpDefNode opDefNode) {
		visitExprNode(opDefNode.getBody());
	}

	public void visitExprOrOpArgNode(ExprOrOpArgNode n) {
		if (n instanceof ExprNode) {
			visitExprNode((ExprNode) n);
		} else {
			throw new RuntimeException("Should not appear.");
		}

	}

	public void visitExprNode(ExprNode node) {
		switch (node.getKind()) {
		case OpApplKind: {
			visitOpApplNode((OpApplNode) node);
			return;
		}
		case NumeralKind: {
			visitNumeralNode((NumeralNode) node);
			return;
		}
		case StringKind: {
			visitStringNode((StringNode) node);
			return;
		}
		case SubstInKind: {
			visitStubstInNode((SubstInNode) node);
			return;
		}
		case AtNodeKind: { // @
			visitAtNode((AtNode) node);
			return;
		}
		case LetInKind: {
			visitLetInNode((LetInNode) node);
			return;
		}
		}
	}

	public void visitOpApplNode(OpApplNode node) {
		switch (node.getOperator().getKind()) {
		case VariableDeclKind: {
			visitVariableNode(node);
			return;
		}
		case ConstantDeclKind: {
			visitConstantNode(node);
			return;
		}

		case FormalParamKind: {
			visitFormalParamNode(node);
			return;
		}

		case BuiltInKind: {
			visitBuiltInNode(node);
			return;
		}

		case UserDefinedOpKind: {
			if (BBuiltInOPs.contains(node.getOperator().getName())) {
				visitBBuiltinsNode(node);
				return;
			} else {
				visitUserDefinedNode(node);
				return;
			}

		}
		}

	}

	public void visitBBuiltinsNode(OpApplNode n) {
		ExprNode[] in = n.getBdedQuantBounds();
		for (ExprNode exprNode : in) {
			visitExprNode(exprNode);
		}

		ExprOrOpArgNode[] arguments = n.getArgs();
		for (ExprOrOpArgNode exprOrOpArgNode : arguments) {
			visitExprOrOpArgNode(exprOrOpArgNode);
		}
	}

	public void visitBuiltInNode(OpApplNode n) {
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

	public void visitLetInNode(LetInNode node) {
		OpDefNode[] lets = node.getLets();
		for (OpDefNode opDefNode : lets) {
			visitLocalDefinition(opDefNode);
		}
		visitExprNode(node.getBody());
	}

	public void visitLocalDefinition(OpDefNode opDefNode) {
		visitExprNode(opDefNode.getBody());
	}

	public void visitAtNode(AtNode n) {
	}

	public void visitStubstInNode(SubstInNode n) {
		visitExprNode(n.getBody());
		return;
	}

	public void visitUserDefinedNode(OpApplNode n) {
		for (ExprOrOpArgNode exprOrOpArgNode : n.getArgs()) {
			visitExprOrOpArgNode(exprOrOpArgNode);
		}
	}

	public void visitFormalParamNode(OpApplNode n) {
	}

	public void visitConstantNode(OpApplNode n) {
	}

	public void visitVariableNode(OpApplNode n) {
	}

	public void visitStringNode(StringNode n) {
	}

	public void visitNumeralNode(NumeralNode n) {
	}

}
