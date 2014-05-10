package de.tla2b.translation;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Hashtable;

import tla2sany.semantic.ExprNode;
import tla2sany.semantic.ExprOrOpArgNode;
import tla2sany.semantic.FormalParamNode;
import tla2sany.semantic.OpApplNode;
import tla2sany.semantic.OpDefNode;
import tla2sany.semantic.SemanticNode;
import tla2sany.semantic.SymbolNode;
import de.tla2b.analysis.AbstractASTVisitor;
import de.tla2b.analysis.SpecAnalyser;

public class RecursiveFunctionHandler extends AbstractASTVisitor {

	private ArrayList<FormalParamNode> paramList;
	private ArrayList<FormalParamNode> ignoreParamList;
	private ArrayList<SymbolNode> externParams;

	private HashSet<OpApplNode> recursiveFunctions = new HashSet<OpApplNode>();
	private Hashtable<SemanticNode, ArrayList<SymbolNode>> additionalParamsTable = new Hashtable<SemanticNode, ArrayList<SymbolNode>>();

	public RecursiveFunctionHandler(SpecAnalyser specAnalyser) {
		for (OpDefNode recFunc : specAnalyser.getRecursiveFunctions()) {
			OpApplNode body = (OpApplNode) recFunc.getBody();
			recursiveFunctions.add(body);
			FormalParamNode[][] params = body.getBdedQuantSymbolLists();

			paramList = new ArrayList<FormalParamNode>();
			FormalParamNode self = body.getUnbdedQuantSymbols()[0];
			paramList.add(self);
			for (int i = 0; i < params.length; i++) {
				for (int j = 0; j < params[i].length; j++) {
					paramList.add(params[i][j]);
				}
			}
			externParams = new ArrayList<SymbolNode>();
			ignoreParamList = new ArrayList<FormalParamNode>();
			visitExprNode(recFunc.getBody());
			paramList = null;
			additionalParamsTable.put(body, externParams);
			additionalParamsTable.put(recFunc, externParams);
			additionalParamsTable.put(self, externParams);
		}
	}

	public void visitFormalParamNode(OpApplNode n) {
		FormalParamNode param = (FormalParamNode) n.getOperator();
		if (!paramList.contains(param) && !ignoreParamList.contains(param)) {
			externParams.add(param);
		}
	}

	public void visitVariableNode(OpApplNode n) {
		externParams.add(n.getOperator());
	}

	public ArrayList<SymbolNode> getAdditionalParams(SemanticNode n) {
		return additionalParamsTable.get(n);
	}

	public boolean isRecursiveFunction(SemanticNode n) {
		return additionalParamsTable.containsKey(n);
	}

	@Override
	public void visitBuiltInNode(OpApplNode n) {
		switch (getOpCode(n.getOperator().getName())) {
		case OPCODE_rfs:
		case OPCODE_nrfs:
		case OPCODE_fc: // Represents [x \in S |-> e]
		case OPCODE_be: // \E x \in S : P
		case OPCODE_bf: // \A x \in S : P
		case OPCODE_bc: // CHOOSE x \in S: P
		case OPCODE_sso: // $SubsetOf Represents {x \in S : P}
		case OPCODE_soa: // $SetOfAll Represents {e : p1 \in S, p2,p3 \in S2}
		{
			FormalParamNode[][] params = n.getBdedQuantSymbolLists();
			HashSet<FormalParamNode> set = new HashSet<FormalParamNode>();
			for (int i = 0; i < params.length; i++) {
				for (int j = 0; j < params[i].length; j++) {
					FormalParamNode param = params[i][j];
					set.add(param);
				}
			}
			ignoreParamList.addAll(set);
			ExprNode[] in = n.getBdedQuantBounds();
			for (ExprNode exprNode : in) {
				visitExprNode(exprNode);
			}
			ExprOrOpArgNode[] arguments = n.getArgs();
			for (ExprOrOpArgNode exprOrOpArgNode : arguments) {
				visitExprOrOpArgNode(exprOrOpArgNode);
			}
			return;
		}
		default: {
			super.visitBuiltInNode(n);
			return;
		}

		}

	}

}
