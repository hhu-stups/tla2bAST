package de.tla2b.types;

import de.be4.classicalb.core.parser.node.AIntegerSetExpression;
import de.be4.classicalb.core.parser.node.PExpression;
import de.tla2b.exceptions.UnificationException;
import de.tla2b.output.TypeVisitorInterface;

public class IntType extends TLAType {

	private static final IntType instance = new IntType();

	private IntType() {
		super(INTEGER);
	}

	public static IntType getInstance() {
		return instance;
	}

	@Override
	public String toString() {
		return "INTEGER";
	}

	@Override
	public boolean isUntyped() {
		return false;
	}

	@Override
	public boolean compare(TLAType o) {
		return o.getKind() == UNTYPED || o.getKind() == INTEGER;
	}

	@Override
	public IntType unify(TLAType o) throws UnificationException {
		if (o.getKind() == INTEGER) {
			return this;
		} else if (o instanceof UntypedType) {
			((UntypedType) o).setFollowersTo(this);
			return this;
		} else
			throw new UnificationException();
	}

	@Override
	public IntType cloneTLAType() {
		return this;
	}

	@Override
	public boolean contains(TLAType o) {
		return false;
	}

	@Override
	public PExpression getBNode() {
		return new AIntegerSetExpression();
	}

	public void apply(TypeVisitorInterface visitor) {
		visitor.caseIntegerType(this);
	}

}
