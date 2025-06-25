package de.tla2b.types;

import de.be4.classicalb.core.parser.node.APowSubsetExpression;
import de.be4.classicalb.core.parser.node.PExpression;
import de.tla2b.exceptions.UnificationException;
import de.tla2b.output.TypeVisitorInterface;

public class SetType extends AbstractHasFollowers {
	private TLAType subType;

	public SetType(TLAType t) {
		super(POW);
		setSubType(t);
	}

	public TLAType getSubType() {
		return subType;
	}

	public void setSubType(TLAType t) {
		this.subType = t;
		if (t instanceof AbstractHasFollowers) {
			// set new reference
			((AbstractHasFollowers) t).addFollower(this);
		}

		// setting subType can lead to a completely typed type
		if (!this.isUntyped()) {
			// this type is completely typed
			this.deleteFollowers();
		}
	}

	public void update(TLAType oldType, TLAType newType) {
		if (this.subType == oldType) {
			this.setSubType(newType);
		}
	}

	public SetType unify(TLAType o) throws UnificationException {
		if (!this.compare(o) || this.contains(o)) {
			throw new UnificationException();
		}
		// if o has followers than switch pointer to this
		if (o instanceof AbstractHasFollowers) {
			((AbstractHasFollowers) o).setFollowersTo(this);
		}

		if (o instanceof StructOrFunctionType) {
			return (SetType) o.unify(this);
		}
		if (o instanceof SetType) {
			SetType p = (SetType) o;
			this.subType = this.subType.unify(p.subType);

//			if (this.subType instanceof AbstractHasFollowers) {
//				((AbstractHasFollowers) this.subType).removeFollower(p);
//			}
		}
		return this;
	}

	@Override
	public boolean compare(TLAType o) {
		if (this.contains(o))
			return false;

		if (o.getKind() == UNTYPED)
			return true;

		if (o instanceof SetType) {
			SetType p = (SetType) o;
			// test sub types compatibility
			return this.subType.compare(p.subType);
		} else
			return false;
	}

	@Override
	public String toString() {
		return "POW(" + this.getSubType() + ")";
	}

	@Override
	public boolean isUntyped() {
		return subType.isUntyped();
	}

	@Override
	public SetType cloneTLAType() {
		return new SetType(this.subType.cloneTLAType());
	}


	@Override
	public boolean contains(TLAType o) {
		return this.getSubType().equals(o) || this.getSubType().contains(o);
	}

	@Override
	public PExpression getBNode() {
		return new APowSubsetExpression(this.getSubType().getBNode());
	}

	public void apply(TypeVisitorInterface visitor) {
		visitor.caseSetType(this);
	}

}
