package de.tla2b.types;

import de.tla2b.output.TypeVisitorInterface;

public interface IType {
	int UNTYPED = 0;
	int INTEGER = 1;
	int BOOL = 2;
	int STRING = 3;
	int MODELVALUE = 4;
	int POW = 5;
	int PAIR = 6;
	int STRUCT = 7;
	int TUPLEORSEQ = 8;
	int STRUCT_OR_FUNCTION = 9;
	int FUNCTION = 10;
	int TUPLE = 11;
	int TUPLE_OR_FUNCTION = 12;
	int REAL = 13;


	void apply(TypeVisitorInterface visitor);
}
