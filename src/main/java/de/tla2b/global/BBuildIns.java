package de.tla2b.global;

import util.UniqueString;

public interface BBuildIns {
	UniqueString OP_dotdot = UniqueString
			.uniqueStringOf("..");
	UniqueString OP_plus = UniqueString.uniqueStringOf("+");
	UniqueString OP_minus = UniqueString
			.uniqueStringOf("-");
	UniqueString OP_times = UniqueString
			.uniqueStringOf("*");
	UniqueString OP_div = UniqueString
			.uniqueStringOf("\\div");
	UniqueString OP_mod = UniqueString.uniqueStringOf("%");
	UniqueString OP_exp = UniqueString.uniqueStringOf("^");

	UniqueString OP_uminus = UniqueString
			.uniqueStringOf("-.");

	UniqueString OP_lt = UniqueString.uniqueStringOf("<");
	UniqueString OP_leq = UniqueString
			.uniqueStringOf("\\leq");
	UniqueString OP_gt = UniqueString.uniqueStringOf(">");
	UniqueString OP_geq = UniqueString
			.uniqueStringOf("\\geq");

	UniqueString OP_nat = UniqueString
			.uniqueStringOf("Nat");
	UniqueString OP_int = UniqueString
			.uniqueStringOf("Int");
	UniqueString OP_real = UniqueString
			.uniqueStringOf("Real");
	UniqueString OP_bool = UniqueString
			.uniqueStringOf("BOOLEAN");
	UniqueString OP_true = UniqueString
			.uniqueStringOf("TRUE");
	UniqueString OP_false = UniqueString
			.uniqueStringOf("FALSE");
	UniqueString OP_string = UniqueString
			.uniqueStringOf("STRING");

	// Sets
	UniqueString OP_card = UniqueString
			.uniqueStringOf("Cardinality");
	UniqueString OP_finite = UniqueString
			.uniqueStringOf("IsFiniteSet");

	// Sequences
	UniqueString OP_len = UniqueString
			.uniqueStringOf("Len");
	UniqueString OP_append = UniqueString
			.uniqueStringOf("Append");
	UniqueString OP_seq = UniqueString
			.uniqueStringOf("Seq");
	UniqueString OP_head = UniqueString
			.uniqueStringOf("Head");
	UniqueString OP_tail = UniqueString
			.uniqueStringOf("Tail");
	UniqueString OP_subseq = UniqueString
			.uniqueStringOf("SubSeq");
	UniqueString OP_conc = UniqueString
	.uniqueStringOf("\\o");
	
	//TLA2B
	UniqueString OP_min = UniqueString
			.uniqueStringOf("MinOfSet");
	UniqueString OP_max = UniqueString
			.uniqueStringOf("MaxOfSet");
	UniqueString OP_setprod = UniqueString
			.uniqueStringOf("SetProduct");
	UniqueString OP_setsum = UniqueString
			.uniqueStringOf("SetSummation");
	UniqueString OP_permseq = UniqueString
			.uniqueStringOf("PermutedSequences");

	//BBuildIns
	UniqueString OP_pow1 = UniqueString
			.uniqueStringOf("POW1");
	
	
	//Relations
	UniqueString OP_rel_inverse = UniqueString
			.uniqueStringOf("rel_inverse");
	
	//TLC
	UniqueString OP_assert = UniqueString
	.uniqueStringOf("Assert");
	
	int B_OPCODE_dotdot = 1;
	int B_OPCODE_plus = 2;
	int B_OPCODE_minus = 3;
	int B_OPCODE_times = 4;
	int B_OPCODE_div = 5;
	int B_OPCODE_exp = 6;
	int B_OPCODE_uminus = 7;
	int B_OPCODE_mod = 8;

	int B_OPCODE_lt = B_OPCODE_mod + 1;
	int B_OPCODE_leq = B_OPCODE_mod + 2;
	int B_OPCODE_gt = B_OPCODE_mod + 3;
	int B_OPCODE_geq = B_OPCODE_mod + 4;

	int B_OPCODE_nat = B_OPCODE_geq + 1;
	int B_OPCODE_bool = B_OPCODE_geq + 2;
	int B_OPCODE_true = B_OPCODE_geq + 3;
	int B_OPCODE_false = B_OPCODE_geq + 4;
	int B_OPCODE_int = B_OPCODE_geq + 5;
	int B_OPCODE_string = B_OPCODE_geq + 6;

	int B_OPCODE_finite = B_OPCODE_string + 1;
	int B_OPCODE_card = B_OPCODE_string + 2;

	int B_OPCODE_len = B_OPCODE_card + 1;
	int B_OPCODE_append = B_OPCODE_card + 2;
	int B_OPCODE_seq = B_OPCODE_card + 3;
	int B_OPCODE_head = B_OPCODE_card + 4;
	int B_OPCODE_tail = B_OPCODE_card + 5;
	int B_OPCODE_subseq = B_OPCODE_card + 6;
	int B_OPCODE_conc = B_OPCODE_card + 7;

	int B_OPCODE_min = B_OPCODE_conc + 1;
	int B_OPCODE_max = B_OPCODE_conc + 2;
	int B_OPCODE_setprod = B_OPCODE_conc + 3;
	int B_OPCODE_setsum = B_OPCODE_conc + 4;
	int B_OPCODE_permseq = B_OPCODE_conc + 5;
	
	int B_OPCODE_pow1 = B_OPCODE_permseq + 1;
	
	
	int B_OPCODE_rel_inverse = B_OPCODE_pow1 + 1;
	
	int B_OPCODE_assert = B_OPCODE_rel_inverse + 1;

	int B_OPCODE_real = B_OPCODE_assert + 1;
}
