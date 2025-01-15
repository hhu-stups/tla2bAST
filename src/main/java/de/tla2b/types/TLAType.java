package de.tla2b.types;

import de.be4.classicalb.core.parser.node.PExpression;
import de.tla2b.exceptions.UnificationException;
import de.tla2b.output.TypeVisitorInterface;

public abstract class TLAType {

	static int UNTYPED = 0;
	static int INTEGER = 1;
	static int BOOL = 2;
	static int STRING = 3;
	static int MODELVALUE = 4;
	static int POW = 5;
	static int PAIR = 6;
	static int STRUCT = 7;
	static int TUPLEORSEQ = 8;
	static int STRUCT_OR_FUNCTION = 9;
	static int FUNCTION = 10;
	static int TUPLE = 11;
	static int TUPLE_OR_FUNCTION = 12;
	static int REAL = 13;

	private final int kind;

	public TLAType(int t) {
		this.kind = t;
	}

	public final int getKind() {
		return kind;
	}

	public abstract PExpression getBNode();

	public abstract boolean compare(TLAType o);

	public abstract boolean contains(TLAType o);

	public abstract boolean isUntyped();

	public abstract TLAType cloneTLAType();

	public abstract TLAType unify(TLAType o) throws UnificationException;

	public TLAType unityAll(TLAType[] types) throws UnificationException {
		TLAType current = this;
		for (TLAType type : types) {
			current = current.unify(type);
		}
		return current;
	}

	public abstract void apply(TypeVisitorInterface visitor);

}
