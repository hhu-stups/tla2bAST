package de.tla2b.types;

import de.tla2b.output.TypeVisitorInterface;

public interface IType {
	public final int UNTYPED = 0;
	public final int INTEGER = 1;
	public final int BOOL = 2;
	public final int STRING = 3;
	public final int MODELVALUE = 4;
	public final int POW = 5;
	public final int PAIR = 6;
	public final int STRUCT = 7;
	public final int TUPLEORSEQ  =8;
	public final int STRUCT_OR_FUNCTION = 9;
	public final int FUNCTION = 10;
	public final int TUPLE = 11;
	public final int TUPLE_OR_FUNCTION =12;
	
	void apply(TypeVisitorInterface visitor);
}
