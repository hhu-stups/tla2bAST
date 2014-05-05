package de.tla2b.translation;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Hashtable;

import tla2sany.semantic.FormalParamNode;
import tla2sany.semantic.OpApplNode;
import tla2sany.semantic.OpDefNode;
import tla2sany.semantic.SemanticNode;
import tla2sany.semantic.SymbolNode;
import de.tla2b.analysis.AbstractASTVisitor;
import de.tla2b.analysis.SpecAnalyser;

public class RecursiveFunctionHandler extends AbstractASTVisitor {

	private ArrayList<FormalParamNode> paramList;
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
			visitExprNode(recFunc.getBody());
			paramList = null;
			additionalParamsTable.put(body, externParams);
			additionalParamsTable.put(recFunc, externParams);
			additionalParamsTable.put(self, externParams);
		}
	}

	public void visitFormalParamNode(OpApplNode n) {
		FormalParamNode param = (FormalParamNode) n.getOperator();
		if (!paramList.contains(param)) {
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
	
}
