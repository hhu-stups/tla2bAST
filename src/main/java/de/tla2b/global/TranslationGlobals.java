package de.tla2b.global;

import java.util.ArrayList;
import java.util.Arrays;

import tla2sany.semantic.FrontEnd;

public interface TranslationGlobals {
	final String VERSION_NUMBER = VersionHelper.VERSION;

	final int TLCValueKind = 100;

	final int USED = FrontEnd.getToolId();
	final int OVERRIDE_SUBSTITUTION_ID = 17;
	final int CONSTANT_OBJECT = 18;
	final int DEF_OBJECT = 19;
	final int PRINT_DEFINITION = 11;
	final int TYPE_ID = 5;
	final int EXCEPT_BASE = 6;
	final int LET_PARAMS_ID = 13;
	final int NEW_NAME = 20;
	
	final int SUBSTITUTE_PARAM = 29;
	final int TUPLE = 30;

	final String CHOOSE = " CHOOSE(X) == \"a member of X\"; EXTERNAL_FUNCTION_CHOOSE(T) == (POW(T)-->T)";
	final String IF_THEN_ELSE = " IF_THEN_ELSE(P, a, b) == (%t_.(t_ = TRUE & P = TRUE | a )\\/%t_.(t_= TRUE & not(P= TRUE) | b ))(TRUE)";

	final ArrayList<String> STANDARD_MODULES = new ArrayList<String>(
			Arrays.asList(new String[] { "Naturals", "FiniteSets", "Integers",
					"Sequences", "TLC", "Relations", "TLA2B", "BBuildIns" }));
}
