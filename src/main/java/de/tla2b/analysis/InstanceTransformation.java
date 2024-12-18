package de.tla2b.analysis;

import de.tla2b.global.BBuiltInOPs;
import de.tla2b.util.TlaUtils;
import tla2sany.semantic.*;
import tlc2.tool.BuiltInOPs;
import util.UniqueString;

import java.util.Map;

/**
 * This class handles substitutions during module instantiation, e.g.
 * <p>
 *      M1 == INSTANCE Counter WITH x &lt;- c, start &lt;- 0
 * <p>
 * Example for usage in module:
 *      OpDef == /\ M1!Init
 * <p>
 * cf. <a href="https://lamport.azurewebsites.net/tla/newmodule.html">https://lamport.azurewebsites.net/tla/newmodule.html</a>
 */
public class InstanceTransformation extends BuiltInOPs implements ASTConstants {

	private final OpDefNode[] defs;
	private final Map<String, OpDefNode> defsHash;
	private final int substitutionId = 11;

	private InstanceTransformation(ModuleNode moduleNode) {
		this.defs = moduleNode.getOpDefs();
		this.defsHash = TlaUtils.getOpDefsMap(defs);
	}

	public static void run(ModuleNode moduleNode) {
		new InstanceTransformation(moduleNode).start();
	}

	/**
	 * replace all substitutions M1!Op1 by the real Op1 (?)
	 */
	private void start() {
		for (OpDefNode def : defs) {
			if (def.getSource() != def && !BBuiltInOPs.contains(def.getSource().getName())) {
				// instance
				String defName = def.getName().toString();

				if (def.getBody() instanceof SubstInNode) {
					String prefix = defName.substring(0, defName.lastIndexOf('!') + 1);
					def.setParams(generateNewParams(def.getParams()));
					ExprNode body;
					try {
						body = generateNewExprNode(def.getBody(), prefix);
					} catch (AbortException e) {
						throw new RuntimeException();
					}
					def.setBody(body);
				}
			}
		}
	}

	private ExprOrOpArgNode generateNewExprOrOpArgNode(ExprOrOpArgNode n, String prefix) throws AbortException {
		if (n instanceof ExprNode) {
			return generateNewExprNode((ExprNode) n, prefix);
		} else {
			throw new RuntimeException("OpArgNode not implemented yet");
		}
	}

	private ExprNode generateNewExprNode(ExprNode n, String prefix) throws AbortException {
		switch (n.getKind()) {
			case OpApplKind: {
				return generateNewOpApplNode((OpApplNode) n, prefix);
			}

			case NumeralKind: {
				return new NumeralNode(n.toString(), n.getTreeNode());
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
				return generateNewExprNode(substInNode.getBody(), prefix);
			}

			case AtNodeKind: { // @
				AtNode old = (AtNode) n;
				return new AtNode((OpApplNode) old.getExceptRef().getToolObject(substitutionId),
						(OpApplNode) old.getExceptComponentRef().getToolObject(substitutionId));
			}

			case LetInKind: {
				LetInNode oldLetNode = (LetInNode) n;
				OpDefNode[] newLets = new OpDefNode[oldLetNode.getLets().length];
				Context cc = oldLetNode.context;
				for (int i = 0; i < oldLetNode.getLets().length; i++) {
					OpDefNode let = oldLetNode.getLets()[i];
					UniqueString newName = UniqueString.uniqueStringOf(prefix + let.getName().toString());
					OpDefNode newLet = new OpDefNode(newName, let.getKind(),
						generateNewParams(let.getParams()), let.isLocal(),
						generateNewExprNode(let.getBody(), prefix),
						let.getOriginallyDefinedInModuleNode(), null,
						let.getTreeNode(), true, let.getSource());
					let.setToolObject(substitutionId, newLet);
					newLets[i] = newLet;
					cc.addSymbolToContext(newName, newLet);
				}

				return new LetInNode(oldLetNode.getTreeNode(), newLets, null,
						generateNewExprNode(oldLetNode.getBody(), prefix), cc);
			}
		}
		throw new IllegalArgumentException("unknown ExprNode kind " + n.getKind());
	}

	private ExprNode generateNewOpApplNode(OpApplNode n, String prefix) throws AbortException {
		switch (n.getOperator().getKind()) {
			case VariableDeclKind:
			case ConstantDeclKind: {
				ExprOrOpArgNode e = (ExprOrOpArgNode) n.getOperator().getToolObject(substitutionId);
				if (e != null) {
					if (e instanceof ExprNode) {
						// TODO newprefix, witout last prefix
						return generateNewExprNode((ExprNode) e, "");
					} else {
						OpArgNode opArg = (OpArgNode) e;
						while (opArg.getOp().getToolObject(substitutionId) != null) {
							opArg = (OpArgNode) opArg.getOp().getToolObject(substitutionId);
						}
						return new OpApplNode(opArg.getOp(), generateNewArgs(
							n.getArgs(), prefix), n.getTreeNode(), null);
					}
				} else {
					return new OpApplNode(n.getOperator(), generateNewArgs(
						n.getArgs(), prefix), n.getTreeNode(), null);
				}
			}

			case FormalParamKind: {
				FormalParamNode f = (FormalParamNode) n.getOperator().getToolObject(substitutionId);
				if (f == null) {
					throw new RuntimeException();
				}
				return new OpApplNode(f, generateNewArgs(n.getArgs(), prefix), n.getTreeNode(), null);
			}

			case BuiltInKind: {
				return generateNewBuiltInNode(n, prefix);
			}

			case UserDefinedOpKind: {
				// in case of a call of a LetInNode
				OpDefNode letOp = (OpDefNode) n.getOperator().getToolObject(substitutionId);
				if (letOp != null) {
					return new OpApplNode(letOp, generateNewArgs(n.getArgs(), prefix), n.getTreeNode(), null);
				}

				// in case of a call of BBuiltInOp e.g. +, -
				if (BBuiltInOPs.contains(n.getOperator().getName())) {
					return new OpApplNode(n.getOperator(), generateNewArgs(n.getArgs(), prefix), n.stn, null);
				}

				// normal userdefined Operator
				String opName = prefix + n.getOperator().getName().toString();
				OpDefNode op = defsHash.get(opName);
				if (op == null) {
					throw new RuntimeException();
				}
				return new OpApplNode(op, generateNewArgs(n.getArgs(), prefix), n.getTreeNode(), null);
			}
		}
		throw new RuntimeException("OpApplkind not implemented yet");
	}

	private ExprNode generateNewBuiltInNode(OpApplNode n, String prefix) throws AbortException {
		switch (getOpCode(n.getOperator().getName())) {
			case OPCODE_exc: { // Except
				OpApplNode newNode = new OpApplNode(n.getOperator().getName(), null, n.getTreeNode(), null);
				n.setToolObject(substitutionId, newNode); // needed for @ node
				ExprOrOpArgNode[] newArgs = new ExprOrOpArgNode[n.getArgs().length];
				newArgs[0] = generateNewExprOrOpArgNode(n.getArgs()[0], prefix);

				for (int i = 1; i < n.getArgs().length; i++) {
					OpApplNode pair = (OpApplNode) n.getArgs()[i];
					OpApplNode newPair = new OpApplNode(pair.getOperator().getName(), null, pair.getTreeNode(), null);
					// needed for @ node: we have to set a reference from the old
					// pair to the new pair
					// before evaluation the arguments which may be contains a @
					// node
					pair.setToolObject(substitutionId, newPair);
					newPair.setArgs(generateNewArgs(pair.getArgs(), prefix));
					newArgs[i] = newPair;
				}
				newNode.setArgs(newArgs);
				return newNode;

			}
			case OPCODE_uc: { // CHOOSE x : P
				FormalParamNode[] oldSymbols = n.getUnbdedQuantSymbols();
				FormalParamNode[] newSymbols = new FormalParamNode[oldSymbols.length];
				for (int i = 0; i < n.getUnbdedQuantSymbols().length; i++) {
					FormalParamNode f = oldSymbols[i];
					newSymbols[i] = new FormalParamNode(f.getName(), f.getArity(),
						f.getTreeNode(), null, null);
					f.setToolObject(substitutionId, newSymbols[i]);
				}
				return new OpApplNode(n.getOperator().getName(),
					newSymbols, generateNewArgs(n.getArgs(), prefix), null,
					null, null, n.getTreeNode(), null);
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
				FormalParamNode[][] oldParams = n.getBdedQuantSymbolLists();
				FormalParamNode[][] newParams = new FormalParamNode[oldParams.length][0];
				for (int i = 0; i < oldParams.length; i++) {
					FormalParamNode[] temp = new FormalParamNode[oldParams[i].length];
					for (int j = 0; j < oldParams[i].length; j++) {
						FormalParamNode f = oldParams[i][j];
						temp[j] = new FormalParamNode(f.getName(), f.getArity(), f.getTreeNode(), null, null);
						// set reference the old param to the new
						f.setToolObject(substitutionId, temp[j]);
					}
					newParams[i] = temp;
				}

				// new ranges
				ExprNode[] ranges = new ExprNode[n.getBdedQuantBounds().length];
				for (int i = 0; i < n.getBdedQuantBounds().length; i++) {
					ranges[i] = generateNewExprNode(n.getBdedQuantBounds()[i], prefix);
				}
				return new OpApplNode(n.getOperator().getName(),
					null, generateNewArgs(n.getArgs(), prefix), newParams,
					n.isBdedQuantATuple(), ranges, n.getTreeNode(), null);
			}

			default: { // =
				return new OpApplNode(n.getOperator(), generateNewArgs(n.getArgs(), prefix), n.getTreeNode(), null);
			}
		}
	}

	private ExprOrOpArgNode[] generateNewArgs(ExprOrOpArgNode[] args, String prefix) throws AbortException {
		ExprOrOpArgNode[] res = new ExprOrOpArgNode[args.length];
		for (int i = 0; i < args.length; i++) {
			res[i] = generateNewExprOrOpArgNode(args[i], prefix);
		}
		return res;
	}

	private FormalParamNode[] generateNewParams(FormalParamNode[] oldParams) {
		FormalParamNode[] newParams = new FormalParamNode[oldParams.length];
		for (int i = 0; i < oldParams.length; i++) {
			FormalParamNode oldParam = oldParams[i];
			FormalParamNode newParam = new FormalParamNode(oldParam.getName(),
				oldParam.getArity(), oldParam.getTreeNode(), null, null);
			// set reference to the old param to the new
			oldParam.setToolObject(substitutionId, newParam);
			newParams[i] = newParam;
		}
		return newParams;
	}
}
