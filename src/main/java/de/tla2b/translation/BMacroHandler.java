package de.tla2b.translation;

import de.tla2b.analysis.AbstractASTVisitor;
import de.tla2b.analysis.SpecAnalyser;
import de.tla2b.config.ConfigfileEvaluator;
import tla2sany.semantic.*;

import java.util.*;

public class BMacroHandler extends AbstractASTVisitor {

	private final Hashtable<FormalParamNode, String> renamingTable = new Hashtable<>();

	public BMacroHandler(SpecAnalyser specAnalyser, ConfigfileEvaluator conEval) {
		ModuleNode moduleNode = specAnalyser.getModuleNode();
		ArrayList<OpDefNode> bDefs = new ArrayList<>();
		for (int i = 0; i < moduleNode.getOpDefs().length; i++) {
			OpDefNode def = moduleNode.getOpDefs()[i];
			if (specAnalyser.getUsedDefinitions().contains(def)) {
				if (conEval != null
					&& conEval.getConstantOverrides()
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
	private final Hashtable<FormalParamNode, Set<FormalParamNode>> parameterContext = new Hashtable<>();

	@Override
	public void visitDefinition(OpDefNode def) {
		definitionParameters = new HashSet<>();
		definitionParameters.addAll(Arrays.asList(def.getParams()));
		for (FormalParamNode param : definitionParameters) {
			parameterContext.put(param, new HashSet<>());
		}
		localVariables = new HashSet<>();

		visitExprNode(def.getBody());

		definitionParameters = null;
		localVariables = null;
	}

	@Override
	public void visitAssumeNode(AssumeNode assumeNode) {
		definitionParameters = new HashSet<>();
		localVariables = new HashSet<>();

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
				HashSet<FormalParamNode> set = new HashSet<>();
				for (FormalParamNode[] param : params) {
					Collections.addAll(set, param);
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
			}

		}

	}

	private Set<String> getStringSet(Set<FormalParamNode> set) {
		HashSet<String> stringSet = new HashSet<>();
		for (FormalParamNode formalParamNode : set) {
			stringSet.add(formalParamNode.getName().toString());
		}
		return stringSet;
	}

	private HashSet<FormalParamNode> illegalParams;

	private void addToIllegalParams(Set<FormalParamNode> set) {
		if (illegalParams == null) {
			illegalParams = new HashSet<>(set);
		} else {
			illegalParams.addAll(set);
		}
	}

	private Set<FormalParamNode> getContextOfParam(FormalParamNode param) {
		Set<FormalParamNode> set = parameterContext.get(param);
		if (set == null) {
			set = new HashSet<>();
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

	final Set<String> globalNames = new HashSet<>();

	private Boolean existingName(String name) {
		return globalNames.contains(name);
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
