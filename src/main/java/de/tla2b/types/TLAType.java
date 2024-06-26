package de.tla2b.types;

import de.be4.classicalb.core.parser.node.PExpression;
import de.tla2b.exceptions.UnificationException;

public abstract class TLAType implements IType {
	private final int kind;

	public TLAType(int t) {
		this.kind = t;
	}

	public final int getKind() {
		return kind;
	}

	public abstract String toString();

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

	public final String printObjectToString() {
		return super.toString();
	}
}
