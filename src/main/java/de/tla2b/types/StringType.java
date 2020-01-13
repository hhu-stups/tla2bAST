package de.tla2b.types;

import de.be4.classicalb.core.parser.node.AStringSetExpression;
import de.be4.classicalb.core.parser.node.PExpression;
import de.tla2b.exceptions.UnificationException;
import de.tla2b.output.TypeVisitorInterface;

public class StringType extends TLAType {

	public StringType() {
		super(STRING);
	}

	private static StringType instance = new StringType();

	public static StringType getInstance() {
		return instance;
	}

	@Override
	public boolean compare(TLAType o) {
		if (o.getKind() == UNTYPED || o.getKind() == STRING)
			return true;
		else if (o instanceof FunctionType) {
			return o.compare(this);
		} else
			return false;

	}

	@Override
	public boolean isUntyped() {
		return false;
	}

	@Override
	public StringType unify(TLAType o) throws UnificationException {
		if (!this.compare(o)) {
			throw new UnificationException();
		}
		if (o.getKind() == STRING) {
			return this;
		} else if (o instanceof UntypedType) {
			((UntypedType) o).setFollowersTo(this);
			((UntypedType) o).deleteFollowers();
			return this;
		} else if (o instanceof FunctionType) {
			// function
			if (o instanceof AbstractHasFollowers) {
				((AbstractHasFollowers) o).setFollowersTo(this);
				((AbstractHasFollowers) o).deleteFollowers();
			}
			return this;
		} else {
			throw new UnificationException();
		}
	}

	@Override
	public StringType cloneTLAType() {
		return this;
	}

	@Override
	public boolean contains(TLAType o) {
		return false;
	}

	@Override
	public PExpression getBNode() {
		return new AStringSetExpression();
	}

	public void apply(TypeVisitorInterface visitor) {
		visitor.caseStringType(this);
	}

	@Override
	public String toString() {
		return "STRING";
	}

}
