package de.tla2b.types;

import de.be4.classicalb.core.parser.node.ARealSetExpression;
import de.be4.classicalb.core.parser.node.PExpression;
import de.tla2b.exceptions.UnificationException;
import de.tla2b.output.TypeVisitorInterface;

public class RealType extends TLAType {

	private static final RealType instance = new RealType();

	private RealType() {
		super(REAL);
	}

	public static RealType getInstance() {
		return instance;
	}

	@Override
	public String toString() {
		return "REAL";
	}

	@Override
	public boolean isUntyped() {
		return false;
	}

	@Override
	public boolean compare(TLAType o) {
		return o.getKind() == UNTYPED || o.getKind() == REAL;
	}

	@Override
	public RealType unify(TLAType o) throws UnificationException {
		if (o.getKind() == REAL) {
			return this;
		} else if (o instanceof UntypedType) {
			((UntypedType) o).setFollowersTo(this);
			return this;
		} else
			throw new UnificationException();
	}

	@Override
	public RealType cloneTLAType() {
		return this;
	}

	@Override
	public boolean contains(TLAType o) {
		return false;
	}

	@Override
	public PExpression getBNode() {
		return new ARealSetExpression();
	}

	public void apply(TypeVisitorInterface visitor) {
		visitor.caseRealType(this);
	}

}
