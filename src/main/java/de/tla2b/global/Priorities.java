package de.tla2b.global;

public interface Priorities {
	int P_max = 300;

	int P_record_acc = 250;
	int P_uminus = 210;
	int P_exp = 200;

	int P_times = 190;
	int P_div = 190;
	int P_mod = 190;


	int P_plus = 180;
	int P_minus = 180;
	int P_setdiff = 180;

	int P_dotdot = 170;

	int P_maplet = 160;

	int P_take_first = 160;
	int P_drop_last = 160;
	int P_conc = 160;

	int P_intersect = 140;
	int P_union = 140;


	int P_append = 130;

	int P_total_f = 125;

	int P_comma = 115;


	int P_rel_overriding = 90;

	int P_in = 60;
	int P_notin = 60;
	int P_subseteq = 60;

	int P_equals = 50;
	int P_noteq = 50;
	int P_gt = 50;
	int P_lt = 50;
	int P_leq = 50;
	int P_geq = 50;

	int P_equiv = 60;

	int P_and = 40;
	int P_or = 40;


	int P_implies = 30;

	int P_min = 0;


}
