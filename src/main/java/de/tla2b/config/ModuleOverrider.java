package de.tla2b.config;

import tla2sany.semantic.*;
import tlc2.tool.BuiltInOPs;

import java.util.Map;

/**
 * Apply overrides specified in the configuration file.
 */
public class ModuleOverrider extends BuiltInOPs {

	private final ModuleNode moduleNode;
	private final ConfigfileEvaluator conEval;

	private ModuleOverrider(ModuleNode moduleNode, ConfigfileEvaluator conEval) {
		this.moduleNode = moduleNode;
		if (conEval == null) {
			throw new IllegalArgumentException("ConfigfileEvaluator cannot be null");
		}
		this.conEval = conEval;
	}

	public static void run(ModuleNode moduleNode, ConfigfileEvaluator conEval) {
		new ModuleOverrider(moduleNode, conEval).start();
	}

	private void start() {
		Map<OpDefNode, TLCValueNode> operatorAssignments = conEval.getOperatorAssignments();
		for (OpDefNode def : moduleNode.getOpDefs()) {
			if (operatorAssignments.containsKey(def)) {
				def.setBody(operatorAssignments.get(def));
			} else if (operatorAssignments.containsKey(def.getSource())) {
				def.setBody(operatorAssignments.get(def.getSource()));
			}
		}

		for (OpDefNode def : moduleNode.getOpDefs()) {
			OpApplNode res = visitExprNode(def.getBody());
			if (res != null) {
				def.setBody(res);
			}
		}

		AssumeNode[] assumes = moduleNode.getAssumptions();
		for (int i = 0; i < assumes.length; i++) {
			OpApplNode res = visitExprNode(assumes[i].getAssume());
			if (res != null) {
				assumes[i] = new AssumeNode(assumes[i].stn, res, null, null);
			}
		}
	}

	private OpApplNode visitExprOrOpArgNode(ExprOrOpArgNode n) {
		if (n instanceof ExprNode) {
			return visitExprNode((ExprNode) n);
		} else {
			throw new RuntimeException("OpArgNode not implemented yet");
		}
	}

	private OpApplNode visitExprNode(ExprNode n) {
		switch (n.getKind()) {
			case OpApplKind:
				return visitOpApplNode((OpApplNode) n);
			case StringKind:
			case AtNodeKind: // @
			case NumeralKind:
			case DecimalKind:
				return null;
			case LetInKind: {
				LetInNode l = (LetInNode) n;
				for (OpDefNode let : l.getLets()) {
					visitExprNode(let.getBody());
				}

				OpApplNode res = visitExprNode(l.getBody());
				if (res != null) {
					throw new RuntimeException();
				}
				return null;
			}
		}
		return null;
	}

	private OpApplNode visitOpApplNode(OpApplNode n) {
		SymbolNode s = n.getOperator();
		switch (s.getKind()) {
			case ConstantDeclKind: {
				if (conEval.getConstantOverrides().containsKey((OpDeclNode) s) && s.getArity() > 0) {
					SymbolNode newOperator = conEval.getConstantOverrides().get((OpDeclNode) s);
					OpApplNode newNode;
					try {
						newNode = new OpApplNode(newOperator, n.getArgs(), n.getTreeNode(), null);
					} catch (AbortException e) {
						throw new RuntimeException(e);
					}
					// n.setOperator(constantOverrideTable.get(s));
					return newNode;
				}
				break;
			}
			case FormalParamKind: // Params are not global in the module
			case VariableDeclKind: // TODO try to override variable
				break;

			case BuiltInKind: // Buildin operator can not be overridden by in the configuration file
				replaceArgs(n.getBdedQuantBounds()); // ins
				break;

			case UserDefinedOpKind: {
				Map<OpDefNode, OpDefNode> operatorOverrides = conEval.getOperatorOverrides();
				OpDefNode operator = (OpDefNode) n.getOperator();
				if (!operatorOverrides.containsKey(operator.getSource()) && !operatorOverrides.containsKey(operator))
					break;

				SymbolNode newOperator;
				// IF there are two override statements in the configuration file
				//(a: Add <- (Rule) Add2, b: R1!Add <- Add3)
				// TLC uses variant a) overriding the source definition
				if (operatorOverrides.containsKey(operator.getSource())) {
					newOperator = operatorOverrides.get(operator.getSource());
				} else {
					newOperator = operatorOverrides.get(operator);
				}
				OpApplNode newNode;
				try {
					newNode = new OpApplNode(newOperator, n.getArgs(), n.getTreeNode(),
							((OpDefNode) n.getOperator()).getOriginallyDefinedInModuleNode());
				} catch (AbortException e) {
					throw new RuntimeException(e);
				}
				// n.setOperator(constantOverrideTable.get(s));
				return newNode;
			}
		}
		replaceArgs(n.getArgs());
		return null;
	}

	private void replaceArgs(ExprOrOpArgNode[] args) {
		if (args != null) {
			for (int i = 0; i < args.length; i++) {
				if (args[i] != null) {
					OpApplNode res = visitExprOrOpArgNode(args[i]);
					if (res != null) {
						args[i] = res;
					}
				}
			}
		}
	}

}
