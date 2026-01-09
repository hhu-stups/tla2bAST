package de.tla2b.global;

import java.util.HashMap;
import java.util.Map;

import tla2sany.semantic.OpDefNode;

import tlc2.tool.ToolGlobals;

import util.UniqueString;

import static de.tla2b.global.BBuildIns.*;

public final class BBuiltInOPs {
	private static final Map<UniqueString, Integer> B_Opcodes = new HashMap<>();

	static {
		B_Opcodes.put(ToolGlobals.OP_dotdot, B_OPCODE_dotdot);
		B_Opcodes.put(ToolGlobals.OP_plus, B_OPCODE_plus);
		B_Opcodes.put(ToolGlobals.OP_minus, B_OPCODE_minus);
		B_Opcodes.put(ToolGlobals.OP_times, B_OPCODE_times);
		B_Opcodes.put(OP_div, B_OPCODE_div);
		B_Opcodes.put(OP_realdiv, B_OPCODE_realdiv);
		B_Opcodes.put(OP_mod, B_OPCODE_mod);
		B_Opcodes.put(OP_exp, B_OPCODE_exp);
		B_Opcodes.put(OP_uminus, B_OPCODE_uminus);

		B_Opcodes.put(ToolGlobals.OP_lt, B_OPCODE_lt);
		B_Opcodes.put(ToolGlobals.OP_leq, B_OPCODE_leq);
		B_Opcodes.put(ToolGlobals.OP_gt, B_OPCODE_gt);
		B_Opcodes.put(ToolGlobals.OP_geq, B_OPCODE_geq);
		B_Opcodes.put(OP_bool, B_OPCODE_bool);
		B_Opcodes.put(OP_true, B_OPCODE_true);
		B_Opcodes.put(OP_false, B_OPCODE_false);
		B_Opcodes.put(OP_nat, B_OPCODE_nat);
		B_Opcodes.put(OP_int, B_OPCODE_int);
		B_Opcodes.put(OP_real, B_OPCODE_real);
		B_Opcodes.put(OP_infinity, B_OPCODE_infinity);
		B_Opcodes.put(OP_string, B_OPCODE_string);

		B_Opcodes.put(OP_finite, B_OPCODE_finite);
		B_Opcodes.put(OP_card, B_OPCODE_card);

		B_Opcodes.put(OP_len, B_OPCODE_len);
		B_Opcodes.put(OP_append, B_OPCODE_append);
		B_Opcodes.put(OP_seq, B_OPCODE_seq);
		B_Opcodes.put(OP_head, B_OPCODE_head);
		B_Opcodes.put(OP_tail, B_OPCODE_tail);
		B_Opcodes.put(OP_subseq, B_OPCODE_subseq);
		B_Opcodes.put(OP_conc, B_OPCODE_conc);

		B_Opcodes.put(OP_min, B_OPCODE_min);
		B_Opcodes.put(OP_max, B_OPCODE_max);
		B_Opcodes.put(OP_setprod, B_OPCODE_setprod);
		B_Opcodes.put(OP_setsum, B_OPCODE_setsum);
		B_Opcodes.put(OP_permseq, B_OPCODE_permseq);

		B_Opcodes.put(OP_pow1, B_OPCODE_pow1);

		//relations
		B_Opcodes.put(OP_rel_inverse, B_OPCODE_rel_inverse);

		B_Opcodes.put(OP_assert, B_OPCODE_assert);
	}

	private BBuiltInOPs() {
		throw new AssertionError("Utility class");
	}

	public static boolean contains(UniqueString s) {
		return B_Opcodes.containsKey(s);
	}

	public static boolean isBBuiltInOp(OpDefNode def) {
		return contains(def.getName()) && TranslationGlobals.STANDARD_MODULES.contains(def.getSource().getOriginallyDefinedInModuleNode().getName().toString());
	}

	public static int getOpcode(UniqueString s) {
		return B_Opcodes.get(s);
	}
}
