package de.tla2b.types;

import de.be4.classicalb.core.parser.node.PExpression;
import de.tla2b.exceptions.UnificationException;
import de.tla2b.output.TypeVisitorInterface;

public final class UntypedType extends AbstractHasFollowers {

	public UntypedType() {
		super(UNTYPED);
	}

	public TLAType unify(TLAType o) throws UnificationException {
		if (!this.compare(o)) {
			throw new UnificationException();
		}

		// if the other type is just an empty untyped one we can return this
		if (o instanceof UntypedType && !((UntypedType) o).hasFollowers()) {
			return this;
		}

		// u2 contains more or equal type information than untyped (this)
		this.setFollowersTo(o);
		//this.deleteFollowers();
		return o;
	}

	@Override
	public boolean compare(TLAType o) {
		return !o.contains(this);
	}

	@Override
	public boolean contains(TLAType o) {
		return false;
	}

	@Override
	public String toString() {
		return "UNTYPED_" + hashCode();
	}

	@Override
	public boolean isUntyped() {
		return true;
	}

	@Override
	public UntypedType cloneTLAType() {
		return new UntypedType();
	}

	@Override
	public PExpression getBNode() {
		return null;
	}

	public void apply(TypeVisitorInterface visitor) {
		visitor.caseUntyped(this);
	}
}
