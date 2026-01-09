package de.tla2b.global;

import java.util.HashSet;
import java.util.Set;

import static de.tla2b.global.BBuildIns.*;
import static tlc2.tool.ToolGlobals.*;

public final class OperatorTypes {
	private static final Set<Integer> TLA_Predicate_Operators;
	private static final Set<Integer> BBuiltIn_Predicate_Operators;

	static {
		TLA_Predicate_Operators = new HashSet<>();
		TLA_Predicate_Operators.add(OPCODE_eq);
		TLA_Predicate_Operators.add(OPCODE_land);
		TLA_Predicate_Operators.add(OPCODE_lor);
		TLA_Predicate_Operators.add(OPCODE_implies);
		TLA_Predicate_Operators.add(OPCODE_equiv);
		TLA_Predicate_Operators.add(OPCODE_subseteq);
		TLA_Predicate_Operators.add(OPCODE_in);
		TLA_Predicate_Operators.add(OPCODE_notin);
		TLA_Predicate_Operators.add(OPCODE_neg);// ?
		TLA_Predicate_Operators.add(OPCODE_cl);
		TLA_Predicate_Operators.add(OPCODE_dl);
		TLA_Predicate_Operators.add(OPCODE_lnot);
		TLA_Predicate_Operators.add(OPCODE_be);
		TLA_Predicate_Operators.add(OPCODE_bf);
		TLA_Predicate_Operators.add(OPCODE_noteq);

		BBuiltIn_Predicate_Operators = new HashSet<>();
		BBuiltIn_Predicate_Operators.add(B_OPCODE_lt);
		BBuiltIn_Predicate_Operators.add(B_OPCODE_gt);
		BBuiltIn_Predicate_Operators.add(B_OPCODE_leq);
		BBuiltIn_Predicate_Operators.add(B_OPCODE_geq);
		BBuiltIn_Predicate_Operators.add(B_OPCODE_finite);
		BBuiltIn_Predicate_Operators.add(B_OPCODE_assert);
	}

	private OperatorTypes() {
		throw new AssertionError("Utility class");
	}

	public static boolean tlaOperatorIsPredicate(int opcode) {
		return TLA_Predicate_Operators.contains(opcode);
	}

	public static boolean bbuiltInOperatorIsPredicate(int opcode) {
		return BBuiltIn_Predicate_Operators.contains(opcode);
	}

}
