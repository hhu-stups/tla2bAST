package de.tla2b.analysis;

import de.tla2b.global.BBuiltInOPs;
import de.tla2b.util.TlaUtils;
import tla2sany.semantic.*;
import tla2sany.st.TreeNode;
import tlc2.tool.BuiltInOPs;
import util.UniqueString;

import java.util.Arrays;
import java.util.Map;

/**
 * This class handles substitutions during module instantiation, e.g.
 * <p>
 *      M1 == INSTANCE Counter WITH x &lt;- c, start &lt;- 0
 * <p>
 * Example for usage in module:
 *      OpDef == M1!Init
 * <p>
 * cf. <a href="https://lamport.azurewebsites.net/tla/newmodule.html">https://lamport.azurewebsites.net/tla/newmodule.html</a>
 */
public class InstanceTransformation extends BuiltInOPs implements ASTConstants {

	private final Map<String, OpDefNode> defs;
	private final int substitutionId = 11;

	private InstanceTransformation(ModuleNode moduleNode) {
		this.defs = TlaUtils.getOpDefsMap(moduleNode.getOpDefs());
	}

	public static void run(ModuleNode moduleNode) {
		new InstanceTransformation(moduleNode).start();
	}

	/**
	 * replace all definitions M1!Op1 by the real Op1 and add included definitions from instances
	 */
	private void start() {
		for (OpDefNode def : defs.values()) {
			if (def.getSource() != def && !BBuiltInOPs.contains(def.getSource().getName())
					&& def.getBody() instanceof SubstInNode) {
				// name of the definition in the instance:
				String defName = def.getName().toString();
				String prefix = defName.substring(0, defName.lastIndexOf('!') + 1);
				def.setParams(copyParams(def.getParams()));
				def.setBody(copyExprNode(def.getBody(), prefix));
			}
		}
	}

	private ExprNode copyExprNode(ExprNode n, String prefix) {
		switch (n.getKind()) {
			case OpApplKind: {
				return copyOpApplNode((OpApplNode) n, prefix);
			}

			case NumeralKind: {
				try {
					return new NumeralNode(n.toString(), n.getTreeNode());
				} catch (AbortException e) {
					throw new RuntimeException("Error while creating NumeralNode: " + e);
				}
			}

			case DecimalKind: {
				String[] image = n.toString().split("\\.");
				if (image.length != 2) {
					throw new IllegalStateException("expected '.' in decimal number");
				}
				return new DecimalNode(image[0], image[1], n.getTreeNode());
			}

			case StringKind: {
				return new StringNode(n.getTreeNode(), false);
			}

			case SubstInKind: {
				SubstInNode substInNode = (SubstInNode) n;
				for (Subst sub : substInNode.getSubsts()) {
					sub.getOp().setToolObject(substitutionId, sub.getExpr());
				}
				return copyExprNode(substInNode.getBody(), prefix);
			}

			case AtNodeKind: { // @
				AtNode old = (AtNode) n;
				return new AtNode((OpApplNode) old.getExceptRef().getToolObject(substitutionId),
						(OpApplNode) old.getExceptComponentRef().getToolObject(substitutionId));
			}

			case LetInKind: {
				LetInNode oldLetNode = (LetInNode) n;
				Context cc = oldLetNode.context;
				OpDefNode[] newLets = Arrays.stream(oldLetNode.getLets())
						.map(let -> {
							UniqueString newName = UniqueString.uniqueStringOf(prefix + let.getName().toString());
							OpDefNode newLet = new OpDefNode(newName, let.getKind(),
									copyParams(let.getParams()), let.isLocal(),
									copyExprNode(let.getBody(), prefix),
									let.getOriginallyDefinedInModuleNode(), null,
									let.getTreeNode(), true, let.getSource());
							let.setToolObject(substitutionId, newLet);
							cc.addSymbolToContext(newName, newLet);
							return newLet;
						})
						.toArray(OpDefNode[]::new);

				return new LetInNode(oldLetNode.getTreeNode(), newLets, null,
						copyExprNode(oldLetNode.getBody(), prefix), cc);
			}
		}
		throw new IllegalArgumentException("unknown ExprNode kind " + n.getKind());
	}

	private ExprNode copyOpApplNode(OpApplNode n, String prefix) {
		switch (n.getOperator().getKind()) {
			case VariableDeclKind:
			case ConstantDeclKind: {
				ExprOrOpArgNode e = (ExprOrOpArgNode) n.getOperator().getToolObject(substitutionId);
				if (e != null) {
					if (e instanceof ExprNode) {
						// TODO newprefix, witout last prefix
						return copyExprNode((ExprNode) e, "");
					} else {
						OpArgNode opArg = (OpArgNode) e;
						while (opArg.getOp().getToolObject(substitutionId) != null) {
							opArg = (OpArgNode) opArg.getOp().getToolObject(substitutionId);
						}
						return createOpApplNode(opArg.getOp(), copyArgs(n.getArgs(), prefix), n.getTreeNode());
					}
				} else {
					return createOpApplNode(n.getOperator(), copyArgs(n.getArgs(), prefix), n.getTreeNode());
				}
			}

			case FormalParamKind: {
				FormalParamNode f = (FormalParamNode) n.getOperator().getToolObject(substitutionId);
				if (f == null) {
					throw new RuntimeException();
				}
				return createOpApplNode(f, copyArgs(n.getArgs(), prefix), n.getTreeNode());
			}

			case BuiltInKind: {
				return copyBuiltInNode(n, prefix);
			}

			case UserDefinedOpKind: {
				// in case of a call of a LetInNode
				OpDefNode letOp = (OpDefNode) n.getOperator().getToolObject(substitutionId);
				if (letOp != null) {
					return createOpApplNode(letOp, copyArgs(n.getArgs(), prefix), n.getTreeNode());
				}

				// in case of a call of BBuiltInOp e.g. +, -
				if (BBuiltInOPs.contains(n.getOperator().getName())) {
					return createOpApplNode(n.getOperator(), copyArgs(n.getArgs(), prefix), n.stn);
				}

				// normal userdefined Operator
				String opName = prefix + n.getOperator().getName().toString();
				OpDefNode op = defs.get(opName);
				if (op == null) {
					throw new RuntimeException("user-defined operator " + opName + " not found");
				}
				return createOpApplNode(op, copyArgs(n.getArgs(), prefix), n.getTreeNode());
			}
		}
		throw new RuntimeException("OpApplkind not implemented yet");
	}

	private ExprNode copyBuiltInNode(OpApplNode n, String prefix) {
		switch (getOpCode(n.getOperator().getName())) {
			case OPCODE_exc: { // Except
				OpApplNode newNode = new OpApplNode(n.getOperator().getName(), null, n.getTreeNode(), null);
				n.setToolObject(substitutionId, newNode); // needed for @ node
				ExprOrOpArgNode[] newArgs = new ExprOrOpArgNode[n.getArgs().length];
				newArgs[0] = copyExprOrOpArgNode(n.getArgs()[0], prefix);

				for (int i = 1; i < n.getArgs().length; i++) {
					OpApplNode pair = (OpApplNode) n.getArgs()[i];
					OpApplNode newPair = new OpApplNode(pair.getOperator().getName(), null, pair.getTreeNode(), null);
					// needed for @ node: we have to set a reference from the old pair to the new pair
					// before evaluating the arguments which may contain an @ node
					pair.setToolObject(substitutionId, newPair);
					newPair.setArgs(copyArgs(pair.getArgs(), prefix));
					newArgs[i] = newPair;
				}
				newNode.setArgs(newArgs);
				return newNode;
			}

			case OPCODE_uc: { // CHOOSE x : P
				return new OpApplNode(n.getOperator().getName(), copyParams(n.getUnbdedQuantSymbols()),
						copyArgs(n.getArgs(), prefix), null, null, null, n.getTreeNode(), null);
			}

			case OPCODE_rfs:
			case OPCODE_nrfs:
			case OPCODE_fc: // Represents [x \in S |-> e]
			case OPCODE_be: // \E x \in S : P
			case OPCODE_bf: // \A x \in S : P
			case OPCODE_bc: // CHOOSE x \in S: P
			case OPCODE_sso: // $SubsetOf Represents {x \in S : P}
			case OPCODE_soa: // $SetOfAll Represents {e : p1 \in S, p2,p3 \in S2}
			{
				// new formalparamnodes
				FormalParamNode[][] newParams = Arrays.stream(n.getBdedQuantSymbolLists())
						.map(this::copyParams)
						.toArray(FormalParamNode[][]::new);

				// new ranges
				ExprNode[] ranges = Arrays.stream(n.getBdedQuantBounds())
						.map(b -> copyExprNode(b,prefix))
						.toArray(ExprNode[]::new);

				return new OpApplNode(n.getOperator().getName(), null, copyArgs(n.getArgs(), prefix),
						newParams, n.isBdedQuantATuple(), ranges, n.getTreeNode(), null);
			}

			default: { // =
				return createOpApplNode(n.getOperator(), copyArgs(n.getArgs(), prefix), n.getTreeNode());
			}
		}
	}

	private ExprOrOpArgNode copyExprOrOpArgNode(ExprOrOpArgNode n, String prefix) {
		if (n instanceof ExprNode) {
			return copyExprNode((ExprNode) n, prefix);
		} else {
			throw new RuntimeException("OpArgNode not implemented yet");
		}
	}

	private ExprOrOpArgNode[] copyArgs(ExprOrOpArgNode[] args, String prefix) {
		return Arrays.stream(args)
				.map(arg -> copyExprOrOpArgNode(arg, prefix))
				.toArray(ExprOrOpArgNode[]::new);
	}

	private FormalParamNode[] copyParams(FormalParamNode[] oldParams) {
		return Arrays.stream(oldParams)
				.map(oldParam -> {
					FormalParamNode newParam = new FormalParamNode(
							oldParam.getName(),
							oldParam.getArity(),
							oldParam.getTreeNode(),
							null,
							null
					);
					// set reference of the old param to the new
					oldParam.setToolObject(substitutionId, newParam);
					return newParam;
				})
				.toArray(FormalParamNode[]::new);
	}

	private static OpApplNode createOpApplNode(SymbolNode operator, ExprOrOpArgNode[] args, TreeNode treeNode) {
		try {
			return new OpApplNode(operator, args, treeNode, null);
		} catch (AbortException e) {
			throw new RuntimeException("Error while creating OpApplNode: " + e);
		}
	}
}
