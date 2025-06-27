package de.tla2b.types;

import de.be4.classicalb.core.parser.node.PExpression;
import de.tla2b.exceptions.UnificationException;
import de.tla2b.output.TypeVisitorInterface;

public final class IntegerOrRealType extends AbstractHasFollowers implements IDefaultableType {

	public IntegerOrRealType() {
		super(INTEGER_OR_REAL);
	}

	@Override
	public String toString() {
		return "IntegerOrReal";
	}

	@Override
	public boolean isUntyped() {
		return true;
	}

	@Override
	public boolean compare(TLAType o) {
		return o.getKind() == UNTYPED || o.getKind() == INTEGER || o.getKind() == REAL || o.getKind() == INTEGER_OR_REAL;
	}

	@Override
	public TLAType unify(TLAType o) throws UnificationException {
		if (o.getKind() == REAL || o.getKind() == INTEGER) {
			this.setFollowersTo(o);
			return o;
		} else if (o.getKind() == INTEGER_OR_REAL || o instanceof UntypedType) {
			((AbstractHasFollowers) o).setFollowersTo(this);
			return this;
		} else {
			throw new UnificationException();
		}
	}

	@Override
	public IntegerOrRealType cloneTLAType() {
		return new IntegerOrRealType();
	}

	@Override
	public boolean contains(TLAType o) {
		return false;
	}

	@Override
	public TLAType setToDefault() {
		TLAType type = IntType.getInstance();
		this.setFollowersTo(type);
		return type;
	}

	@Override
	public PExpression getBNode() {
		throw new UnsupportedOperationException("IntegerOrRealType has no corresponding B node");
	}

	public void apply(TypeVisitorInterface visitor) {
		visitor.caseIntegerOrRealType(this);
	}
}
