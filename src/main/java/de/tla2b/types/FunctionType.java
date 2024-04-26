package de.tla2b.types;

import de.be4.classicalb.core.parser.node.APartialFunctionExpression;
import de.be4.classicalb.core.parser.node.PExpression;
import de.tla2b.exceptions.UnificationException;
import de.tla2b.output.TypeVisitorInterface;

public class FunctionType extends AbstractHasFollowers {
	private TLAType domain;
	private TLAType range;

	public FunctionType(TLAType domain, TLAType range) {
		super(FUNCTION);
		this.setDomain(domain);
		this.setRange(range);
	}

	public FunctionType() {
		super(FUNCTION);
		this.setDomain(new UntypedType());
		this.setRange(new UntypedType());
	}

	public FunctionType(int string) {
		super(string);
	}

	public void update(TLAType oldType, TLAType newType) {
		if (domain == oldType)
			setDomain(newType);
		if (range == oldType)
			setRange(newType);
	}

	@Override
	public boolean compare(TLAType other) {
		if (this.contains(other))
			return false;
		if (other.getKind() == UNTYPED)
			return true;
		if (other instanceof StringType
				&& domain.compare(IntType.getInstance())
				&& range instanceof UntypedType) {
			return true;
		}
		if (other instanceof FunctionType) {
			FunctionType f = (FunctionType) other;
			return domain.compare(f.domain) && range.compare(f.range);
		}
		if (other instanceof TupleType) {
			return other.compare(this);
		}
		if (other instanceof TupleOrFunction) {
			return other.compare(this);
		}
		return false;
	}

	@Override
	public boolean contains(TLAType o) {
		return domain.equals(o) || domain.contains(o) || range.equals(o)
				|| range.contains(o);
	}

	@Override
	public boolean isUntyped() {
		return domain.isUntyped() || range.isUntyped();
	}

	@Override
	public TLAType cloneTLAType() {
		return new FunctionType(domain.cloneTLAType(), range.cloneTLAType());
	}

	@Override
	public TLAType unify(TLAType other) throws UnificationException {
		if (other == null || !this.compare(other)) {
			throw new UnificationException();
		}

		if (other instanceof StringType) {
			this.setFollowersTo(other);
			return StringType.getInstance();
		}

		if (other instanceof UntypedType) {
			((UntypedType) other).setFollowersTo(this);
			return this;
		}
		if (other instanceof FunctionType) {
			domain = domain.unify(((FunctionType) other).domain);
			range = range.unify(((FunctionType) other).range);
			return this;
		}
		if (other instanceof TupleType) {
			return other.unify(this);
		}
		if (other instanceof TupleOrFunction) {
			return other.unify(this);
		}

		throw new RuntimeException();
	}

	public TLAType getDomain() {
		return domain;
	}

	public TLAType getRange() {
		return range;
	}

	public void setDomain(TLAType domain) {
		this.domain = domain;
		if (domain instanceof AbstractHasFollowers) {
			((AbstractHasFollowers) domain).addFollower(this);
		}
	}

	public void setRange(TLAType range) {
		this.range = range;
		if (range instanceof AbstractHasFollowers) {
			((AbstractHasFollowers) range).addFollower(this);
		}
	}

	@Override
	public String toString() {
		String res = "POW(" + domain + "*";
		if (range instanceof TupleType) {
			res += "(" + range + ")";
		} else {
			res += range;
		}
		res += ")";
		return res;
	}

	@Override
	public PExpression getBNode() {
		return new APartialFunctionExpression(domain.getBNode(),
				range.getBNode());
	}

	public void apply(TypeVisitorInterface vistor) {
		vistor.caseFunctionType(this);
	}

}
