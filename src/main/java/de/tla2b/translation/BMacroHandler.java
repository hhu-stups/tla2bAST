package de.tla2b.translation;

import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.tla2b.analysis.AbstractASTVisitor;
import de.tla2b.analysis.SpecAnalyser;
import de.tla2b.config.ConfigfileEvaluator;

import tla2sany.semantic.*;

import tlc2.tool.BuiltInOPs;

import static tlc2.tool.ToolGlobals.*;

public class BMacroHandler extends AbstractASTVisitor {

	private final Map<FormalParamNode, String> renamingTable = new HashMap<>();

	public BMacroHandler(SpecAnalyser specAnalyser, ConfigfileEvaluator conEval) {
		ModuleNode moduleNode = specAnalyser.getModuleNode();
		List<OpDefNode> bDefs = Arrays.stream(moduleNode.getOpDefs())
				.filter(def -> specAnalyser.getUsedDefinitions().contains(def))
				.filter(def -> conEval == null || !conEval.getConstantOverrides().containsValue(def))
				.collect(Collectors.toList());
		for (OpDefNode opDefNode : bDefs) {
			visitDefinition(opDefNode);
		}
		visitAssumptions(moduleNode.getAssumptions());
	}

	public BMacroHandler() {
	}

	private Set<FormalParamNode> definitionParameters;
	private Set<FormalParamNode> localVariables;
	private final Map<FormalParamNode, Set<FormalParamNode>> parameterContext = new HashMap<>();

	@Override
	public void visitDefinition(OpDefNode def) {
		definitionParameters = new HashSet<>(Arrays.asList(def.getParams()));
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
		switch (BuiltInOPs.getOpCode(n.getOperator().getName())) {
			case OPCODE_rfs:
			case OPCODE_nrfs:
			case OPCODE_fc: // Represents [x \in S |-> e]
			case OPCODE_be: // \E x \in S : P
			case OPCODE_bf: // \A x \in S : P
			case OPCODE_bc: // CHOOSE x \in S: P
			case OPCODE_sso: // $SubsetOf Represents {x \in S : P}
			case OPCODE_soa: { // $SetOfAll Represents {e : p1 \in S, p2,p3 \in S2}
				Set<FormalParamNode> set = new HashSet<>();
				for (FormalParamNode[] param : n.getBdedQuantSymbolLists()) {
					Collections.addAll(set, param);
				}
				localVariables.addAll(set);
				for (ExprNode exprNode : n.getBdedQuantBounds()) { // in
					visitExprNode(exprNode);
				}
				for (ExprOrOpArgNode argument : n.getArgs()) {
					visitExprOrOpArgNode(argument);
				}
				localVariables.removeAll(set);
				return;
			}
			default:
				super.visitBuiltInNode(n);
		}
	}

	private Set<String> getStringSet(Set<FormalParamNode> set) {
		return set.stream().map(s -> s.getName().toString()).collect(Collectors.toSet());
	}

	private Set<FormalParamNode> illegalParams;

	private void addToIllegalParams(Set<FormalParamNode> set) {
		if (illegalParams == null) {
			illegalParams = new HashSet<>();
		}
		illegalParams.addAll(set);
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
