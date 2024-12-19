package de.tla2b.config;

import tla2sany.semantic.*;
import tlc2.tool.BuiltInOPs;

import java.util.Map;

public class ModuleOverrider extends BuiltInOPs implements ASTConstants {

	private final ModuleNode moduleNode;
	private final Map<OpDeclNode, OpDefNode> constantOverrideTable;
	private final Map<OpDefNode, OpDefNode> operatorOverrideTable;
	private final Map<OpDefNode, ValueObj> operatorAssignments;

	private ModuleOverrider(ModuleNode moduleNode, ConfigfileEvaluator conEval) {
		this.moduleNode = moduleNode;
		this.constantOverrideTable = conEval.getConstantOverrides();
		this.operatorOverrideTable = conEval.getOperatorOverrides();
		this.operatorAssignments = conEval.getOperatorAssignments();
	}

	public static void run(ModuleNode moduleNode, ConfigfileEvaluator conEval) {
		new ModuleOverrider(moduleNode, conEval).start();
	}

	private void start() {
		OpDefNode[] defs = moduleNode.getOpDefs();
		for (OpDefNode def : defs) {
			if (operatorAssignments.containsKey(def)) {
				ExprNode oldExpr = def.getBody();
				TLCValueNode valueNode;
				try {
					valueNode = new TLCValueNode(operatorAssignments.get(def),
						oldExpr.getTreeNode());
				} catch (AbortException e) {
					throw new RuntimeException();
				}
				def.setBody(valueNode);
			} else if (operatorAssignments.containsKey(def.getSource())) {
				ExprNode oldExpr = def.getBody();
				TLCValueNode valueNode;
				try {
					valueNode = new TLCValueNode(operatorAssignments.get(def
						.getSource()), oldExpr.getTreeNode());
				} catch (AbortException e) {
					throw new RuntimeException();
				}
				def.setBody(valueNode);
			}

		}

		for (OpDefNode def : defs) {
			OpApplNode res = visitExprNode(def.getBody());
			if (res != null) {
				def.setBody(res);
			}
		}

		AssumeNode[] assumes = moduleNode.getAssumptions();
		for (int i = 0; i < assumes.length; i++) {
			AssumeNode assume = assumes[i];
			OpApplNode res = visitExprNode(assume.getAssume());
			if (res != null) {

				AssumeNode newAssume = new AssumeNode(assume.stn, res, null,
					null);
				assumes[i] = newAssume;
			}
		}
	}

	private OpApplNode visitExprOrOpArgNode(ExprOrOpArgNode n) {
		if (n instanceof ExprNode) {

			return visitExprNode((ExprNode) n);
		} else {
			throw new RuntimeException("OpArgNode not implemented jet");
		}
	}

	private OpApplNode visitExprNode(ExprNode n) {

		switch (n.getKind()) {
			case OpApplKind:
				return visitOpApplNode((OpApplNode) n);

			case StringKind:
			case AtNodeKind: // @
			case NumeralKind:
			case DecimalKind: {
				return null;
			}

			case LetInKind: {
				LetInNode l = (LetInNode) n;
				for (int i = 0; i < l.getLets().length; i++) {
					visitExprNode(l.getLets()[i].getBody());
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
				if (constantOverrideTable.containsKey(s) && s.getArity() > 0) {
					SymbolNode newOperator = constantOverrideTable.get(s);
					OpApplNode newNode;
					try {
						newNode = new OpApplNode(newOperator, n.getArgs(),
							n.getTreeNode(), null);
					} catch (AbortException e) {
						throw new RuntimeException();
					}
					for (int i = 0; i < n.getArgs().length; i++) {
						if (n.getArgs()[i] != null) {
							OpApplNode res = visitExprOrOpArgNode(n.getArgs()[i]);
							if (res != null) {
								n.getArgs()[i] = res;
							}
						}
					}
					// n.setOperator(constantOverrideTable.get(s));
					return newNode;
				}
				break;

			}
			case FormalParamKind: // Params are not global in the module
			case VariableDeclKind: // TODO try to override variable
				break;

			case BuiltInKind:// Buildin operator can not be overridden by in the
				// configuration file
				ExprNode[] ins = n.getBdedQuantBounds();
				if (ins != null) {
					for (int i = 0; i < ins.length; i++) {

						OpApplNode res = visitExprOrOpArgNode(ins[i]);
						if (res != null) {
							ins[i] = res;
						}
					}
				}

				break;

			case UserDefinedOpKind: {
				OpDefNode operator = (OpDefNode) n.getOperator();
				if (!operatorOverrideTable.containsKey(operator.getSource())
					&& !operatorOverrideTable.containsKey(operator))
					break;

				SymbolNode newOperator;
				// IF there are two override statements in the configuration file
				//(a: Add <- (Rule) Add2, b: R1!Add <- Add3)
				// TLC uses variant a) overriding the source definition
				if (operatorOverrideTable.containsKey(operator.getSource())) {
					newOperator = operatorOverrideTable.get(operator.getSource());
				} else {
					newOperator = operatorOverrideTable.get(operator);
				}
				OpApplNode newNode = null;
				OpDefNode def = (OpDefNode) n.getOperator();
				try {
					newNode = new OpApplNode(newOperator, n.getArgs(),
						n.getTreeNode(), def.getOriginallyDefinedInModuleNode());
				} catch (AbortException e) {
					e.printStackTrace();
				}
				for (int i = 0; i < n.getArgs().length; i++) {
					if (n.getArgs()[i] != null) {
						OpApplNode res = visitExprOrOpArgNode(n.getArgs()[i]);
						if (res != null) {
							n.getArgs()[i] = res;
						}
					}

				}
				// n.setOperator(constantOverrideTable.get(s));
				return newNode;
			}
		}

		for (int i = 0; i < n.getArgs().length; i++) {
			if (n.getArgs()[i] != null) {
				ExprOrOpArgNode arg = n.getArgs()[i];
				if (arg != null) {
					OpApplNode res = visitExprOrOpArgNode(n.getArgs()[i]);
					if (res != null) {
						n.getArgs()[i] = res;
					}
				}
			}

		}
		return null;
	}

}
