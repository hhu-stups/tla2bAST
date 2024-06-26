package de.tla2b.types;

import de.be4.classicalb.core.parser.node.ABoolSetExpression;
import de.be4.classicalb.core.parser.node.PExpression;
import de.tla2b.exceptions.UnificationException;
import de.tla2b.output.TypeVisitorInterface;

public class BoolType extends TLAType {

	private static final BoolType instance = new BoolType();

	private BoolType() {
		super(BOOL);
	}

	public static BoolType getInstance() {
		return instance;
	}

	@Override
	public String toString() {
		return "BOOL";
	}

	@Override
	public boolean isUntyped() {
		return false;
	}

	@Override
	public boolean compare(TLAType o) {
		return o.getKind() == UNTYPED || o.getKind() == BOOL;
	}

	@Override
	public BoolType unify(TLAType o) throws UnificationException {
		if (o.getKind() == BOOL) {
			return this;
		} else if (o instanceof UntypedType) {
			((UntypedType) o).setFollowersTo(this);
			return this;
		} else
			throw new UnificationException();
	}

	@Override
	public BoolType cloneTLAType() {
		return this;
	}

	@Override
	public boolean contains(TLAType o) {
		return false;
	}

	@Override
	public PExpression getBNode() {
		return new ABoolSetExpression();
	}

	public void apply(TypeVisitorInterface t) {
		t.caseBoolType(this);
	}

}
