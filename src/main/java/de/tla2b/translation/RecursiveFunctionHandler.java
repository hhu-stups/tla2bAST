package de.tla2b.translation;

import de.tla2b.analysis.AbstractASTVisitor;
import de.tla2b.analysis.SpecAnalyser;
import tla2sany.semantic.*;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.Hashtable;

public class RecursiveFunctionHandler extends AbstractASTVisitor {

	private ArrayList<FormalParamNode> paramList;
	private ArrayList<FormalParamNode> ignoreParamList;
	private ArrayList<SymbolNode> externParams;

	private final HashSet<OpApplNode> recursiveFunctions = new HashSet<>();
	private final Hashtable<SemanticNode, ArrayList<SymbolNode>> additionalParamsTable = new Hashtable<>();

	public RecursiveFunctionHandler(SpecAnalyser specAnalyser) {
		for (OpDefNode recFunc : specAnalyser.getRecursiveFunctions()) {
			OpApplNode body = (OpApplNode) recFunc.getBody();
			recursiveFunctions.add(body);
			FormalParamNode[][] params = body.getBdedQuantSymbolLists();

			paramList = new ArrayList<>();
			FormalParamNode self = body.getUnbdedQuantSymbols()[0];
			paramList.add(self);
			for (FormalParamNode[] param : params) {
				Collections.addAll(paramList, param);
			}
			externParams = new ArrayList<>();
			ignoreParamList = new ArrayList<>();
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
				HashSet<FormalParamNode> set = new HashSet<>();
				for (FormalParamNode[] param : params) {
					Collections.addAll(set, param);
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
			}

		}

	}

}
