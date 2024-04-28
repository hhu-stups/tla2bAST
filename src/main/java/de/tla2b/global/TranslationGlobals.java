package de.tla2b.global;

import tla2sany.semantic.FrontEnd;

import java.util.ArrayList;
import java.util.Arrays;

public interface TranslationGlobals {
	String VERSION_NUMBER = VersionHelper.VERSION;

	int TLCValueKind = 100;

	int USED = FrontEnd.getToolId();
	int OVERRIDE_SUBSTITUTION_ID = 17;
	int CONSTANT_OBJECT = 18;
	int DEF_OBJECT = 19;
	int PRINT_DEFINITION = 11;
	int TYPE_ID = 5;
	int EXCEPT_BASE = 6;
	int LET_PARAMS_ID = 13;
	int NEW_NAME = 20;

	int SUBSTITUTE_PARAM = 29;
	int TUPLE = 30;

	String CHOOSE = " CHOOSE(X) == \"a member of X\"; EXTERNAL_FUNCTION_CHOOSE(T) == (POW(T)-->T)";
	String IF_THEN_ELSE = " IF_THEN_ELSE(P, a, b) == (%t_.(t_ = TRUE & P = TRUE | a )\\/%t_.(t_= TRUE & not(P= TRUE) | b ))(TRUE)";

	ArrayList<String> STANDARD_MODULES = new ArrayList<>(
		Arrays.asList("Naturals", "FiniteSets", "Integers", "Reals",
			"Sequences", "TLC", "Relations", "TLA2B", "BBuildIns"));
}
