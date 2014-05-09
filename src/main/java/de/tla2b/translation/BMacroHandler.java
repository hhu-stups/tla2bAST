package de.tla2b.translation;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.Hashtable;
import java.util.Set;

import tla2sany.semantic.AssumeNode;
import tla2sany.semantic.ExprNode;
import tla2sany.semantic.ExprOrOpArgNode;
import tla2sany.semantic.FormalParamNode;
import tla2sany.semantic.ModuleNode;
import tla2sany.semantic.OpApplNode;
import tla2sany.semantic.OpDefNode;
import tla2sany.semantic.SymbolNode;
import de.tla2b.analysis.AbstractASTVisitor;
import de.tla2b.analysis.SpecAnalyser;
import de.tla2b.config.ConfigfileEvaluator;

public class BMacroHandler extends AbstractASTVisitor {

	private final Hashtable<FormalParamNode, String> renamingTable = new Hashtable<FormalParamNode, String>();

	public BMacroHandler(SpecAnalyser specAnalyser, ConfigfileEvaluator conEval) {
		ModuleNode moduleNode = specAnalyser.getModuleNode();
		ArrayList<OpDefNode> bDefs = new ArrayList<OpDefNode>();
		for (int i = 0; i < moduleNode.getOpDefs().length; i++) {
			OpDefNode def = moduleNode.getOpDefs()[i];
			if (specAnalyser.getUsedDefinitions().contains(def)) {
				if (conEval != null
						&& conEval.getConstantOverrideTable()
								.containsValue(def)) {
					continue;
				}
				bDefs.add(def);
			}
		}

		for (OpDefNode opDefNode : bDefs) {
			visitDefinition(opDefNode);
		}

		visitAssumptions(moduleNode.getAssumptions());
	}

	public BMacroHandler() {
	}

	private HashSet<FormalParamNode> definitionParameters;
	private HashSet<FormalParamNode> localVariables;
	private final Hashtable<FormalParamNode, Set<FormalParamNode>> parameterContext = new Hashtable<FormalParamNode, Set<FormalParamNode>>();

	@Override
	public void visitDefinition(OpDefNode def) {
		definitionParameters = new HashSet<FormalParamNode>();
		definitionParameters.addAll(Arrays.asList(def.getParams()));
		for (FormalParamNode param : definitionParameters) {
			parameterContext.put(param, new HashSet<FormalParamNode>());
		}
		localVariables = new HashSet<FormalParamNode>();

		visitExprNode(def.getBody());

		definitionParameters = null;
		localVariables = null;
	}

	@Override
	public void visitAssumeNode(AssumeNode assumeNode) {
		definitionParameters = new HashSet<FormalParamNode>();
		localVariables = new HashSet<FormalParamNode>();

		visitExprNode(assumeNode.getAssume());

		definitionParameters = null;
		localVariables = null;

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
			localVariables.addAll(set);
			ExprNode[] in = n.getBdedQuantBounds();
			for (ExprNode exprNode : in) {
				visitExprNode(exprNode);
			}
			ExprOrOpArgNode[] arguments = n.getArgs();
			for (ExprOrOpArgNode exprOrOpArgNode : arguments) {
				visitExprOrOpArgNode(exprOrOpArgNode);
			}
			localVariables.removeAll(set);
			return;
		}
		default: {
			super.visitBuiltInNode(n);
			return;
		}

		}

	}

	private Set<String> getStringSet(Set<FormalParamNode> set) {
		HashSet<String> stringSet = new HashSet<String>();
		for (FormalParamNode formalParamNode : set) {
			stringSet.add(formalParamNode.getName().toString());
		}
		return stringSet;
	}

	private HashSet<FormalParamNode> illegalParams;

	private void addToIllegalParams(Set<FormalParamNode> set) {
		if (illegalParams == null) {
			illegalParams = new HashSet<FormalParamNode>(set);
		} else {
			illegalParams.addAll(set);
		}
	}

	private Set<FormalParamNode> getContextOfParam(FormalParamNode param) {
		Set<FormalParamNode> set = parameterContext.get(param);
		if (set == null) {
			set = new HashSet<FormalParamNode>();
		}
		return set;
	}

	public void visitUserDefinedNode(OpApplNode n) {
		OpDefNode operator = (OpDefNode) n.getOperator();
		FormalParamNode[] params = operator.getParams();

		ExprOrOpArgNode[] arguments = n.getArgs();
		for (int i = 0; i < arguments.length; i++) {
			Set<FormalParamNode> set = getContextOfParam(params[i]);
			addToIllegalParams(set);
			visitExprOrOpArgNode(arguments[i]);
			illegalParams.removeAll(set);
		}
	}

	@Override
	public void visitFormalParamNode(OpApplNode n) {
		FormalParamNode param = (FormalParamNode) n.getOperator();
		if (definitionParameters.contains(param)) {
			parameterContext.get(param).addAll(localVariables);
		}

		hasSymbolAValidName(n);
	}

	public void visitConstantNode(OpApplNode n) {
		hasSymbolAValidName(n);
	}

	public void visitVariableNode(OpApplNode n) {
		hasSymbolAValidName(n);
	}

	private void hasSymbolAValidName(OpApplNode n) {
		SymbolNode symbol = n.getOperator();
		String symbolName = symbol.getName().toString();
		if (illegalParams != null) {
			for (FormalParamNode illegalParam : illegalParams) {
				if (symbolName.equals(illegalParam.getName().toString())) {
					Set<String> illgalNames = getStringSet(illegalParams);
					String newName = incName(symbolName, illgalNames);
					renamingTable.put(illegalParam, newName);
				}
			}
		}
	}

	Set<String> globalNames = new HashSet<String>();

	private Boolean existingName(String name) {
		if (globalNames.contains(name)) {
			return true;
		} else
			return false;
	}

	private String incName(String name, Set<String> tempSet) {
		String res = name;
		for (int i = 1; existingName(res) || tempSet.contains(res); i++) {
			res = name + "_" + i;
		}
		return res;
	}

	public boolean containsSymbolNode(SymbolNode s) {
		return renamingTable.containsKey(s);
	}

	public String getNewName(SymbolNode s) {
		return renamingTable.get(s);
	}

}
