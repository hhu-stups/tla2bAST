package de.tla2b.analysis;

import de.tla2b.global.BBuildIns;
import de.tla2b.global.BBuiltInOPs;
import tla2sany.semantic.*;
import tlc2.tool.BuiltInOPs;

import java.util.HashMap;
import java.util.Map;

public class PredicateVsExpression extends BuiltInOPs implements BBuildIns {

	private final Map<OpDefNode, DefinitionType> definitionsTypeMap = new HashMap<>();

	public enum DefinitionType {
		PREDICATE, EXPRESSION
	}

	public PredicateVsExpression(ModuleNode moduleNode) {
		for (OpDefNode def : moduleNode.getOpDefs()) {
			definitionsTypeMap.put(def, visitSemanticNode(def.getBody()));
		}
	}

	public DefinitionType getDefinitionType(OpDefNode def) {
		return definitionsTypeMap.get(def);
	}

	private DefinitionType visitSemanticNode(SemanticNode s) {
		switch (s.getKind()) {
			case OpApplKind:
				return visitOpApplNode((OpApplNode) s);

			case LetInKind:
				return visitSemanticNode(((LetInNode) s).getBody());
		}
		return DefinitionType.EXPRESSION;
	}

	private DefinitionType visitOpApplNode(OpApplNode opApplNode) {
		int kind = opApplNode.getOperator().getKind();

		if (kind == BuiltInKind) {
			switch (getOpCode(opApplNode.getOperator().getName())) {
				case OPCODE_eq: // =
				case OPCODE_noteq: // /=
				case OPCODE_cl: // $ConjList
				case OPCODE_land: // \land
				case OPCODE_dl: // $DisjList
				case OPCODE_lor: // \/
				case OPCODE_equiv: // \equiv
				case OPCODE_implies: // =>
				case OPCODE_lnot: // \lnot
				case OPCODE_be: // \E x \in S : P
				case OPCODE_bf: // \A x \in S : P
				case OPCODE_in: // \in
				case OPCODE_subseteq: // \subseteq {1,2} <: {1,2,3}
				case OPCODE_unchanged:
					return DefinitionType.PREDICATE;

				case OPCODE_ite: // IF THEN ELSE
					return visitSemanticNode(opApplNode.getArgs()[1]);

				case OPCODE_case: { // CASE p1 -> e1 [] p2 -> e2
					OpApplNode pair = (OpApplNode) opApplNode.getArgs()[0];
					return visitSemanticNode(pair.getArgs()[1]);
				}

				default: {
					return DefinitionType.EXPRESSION;
				}
			}
		} else if (kind == UserDefinedOpKind) {
			return visitUserdefinedOp(opApplNode);
		}
		return DefinitionType.EXPRESSION;
	}

	private DefinitionType visitUserdefinedOp(OpApplNode s) {
		OpDefNode def = (OpDefNode) s.getOperator();
		if (BBuiltInOPs.isBBuiltInOp(def)) {
			switch (BBuiltInOPs.getOpcode(def.getName())) {
				case B_OPCODE_lt: // <
				case B_OPCODE_gt: // >
				case B_OPCODE_leq: // <=
				case B_OPCODE_geq: // >=
				case B_OPCODE_finite:
					return DefinitionType.PREDICATE;
				default:
					return DefinitionType.EXPRESSION;
			}
		}
		return getDefinitionType(def);
	}
}
