package de.tla2b.types;

import de.be4.classicalb.core.parser.node.PExpression;
import de.tla2b.exceptions.UnificationException;
import de.tla2b.output.TypeVisitorInterface;

public class ModelValueType extends TLAType {

	private static final ModelValueType instance = new ModelValueType();

	private ModelValueType() {
		super(MODELVALUE);
	}

	public static ModelValueType getInstance() {
		return instance;
	}


	@Override
	public String toString() {
		return "ENUM";
	}

	@Override
	public boolean isUntyped() {
		return false;
	}
	
	@Override
	public boolean compare(TLAType o) {
		return o.getKind() == UNTYPED || o.getKind() == MODELVALUE;
	}
	
	@Override
	public ModelValueType unify(TLAType o) throws UnificationException {
		if (o.getKind() == MODELVALUE) {
			return this;
		} else if (o instanceof UntypedType) {
			((UntypedType) o).setFollowersTo(this);
			return this;
		} else
			throw new UnificationException();
	}

	@Override
	public ModelValueType cloneTLAType() {
		return this;
	}
	
	@Override
	public boolean contains(TLAType o) {
		return false;
	}

	@Override
	public PExpression getBNode() {
		// TODO Auto-generated method stub
		return null;
	}

	public void apply(TypeVisitorInterface visitor) {
		visitor.caseModelValueType(this);
	}
}
