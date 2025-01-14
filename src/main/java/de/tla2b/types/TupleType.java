package de.tla2b.types;

import de.be4.classicalb.core.parser.node.PExpression;
import de.be4.classicalb.core.parser.util.ASTBuilder;
import de.tla2b.exceptions.UnificationException;
import de.tla2b.output.TypeVisitorInterface;
import de.tla2bAst.BAstCreator;

import java.util.ArrayList;
import java.util.List;
import java.util.stream.Collectors;

public class TupleType extends AbstractHasFollowers {
	private List<TLAType> types;

	public TupleType(List<TLAType> typeList) {
		super(TUPLE);
		setTypes(typeList);
	}

	public TupleType(int size) {
		super(TUPLE);
		ArrayList<TLAType> list = new ArrayList<>();
		for (int i = 0; i < size; i++) {
			list.add(new UntypedType());
		}
		setTypes(list);
	}

	public List<TLAType> getTypes() {
		return new ArrayList<>(types);
	}

	public void setTypes(List<TLAType> types) {
		this.types = types;
		types = new ArrayList<>(types);
		for (TLAType tlaType : types) {
			if (tlaType instanceof AbstractHasFollowers) {
				((AbstractHasFollowers) tlaType).addFollower(this);
			}
		}
	}

	public void update(TLAType oldType, TLAType newType) {
		for (int i = 0; i < types.size(); i++) {
			TLAType t = types.get(i);
			if (oldType == t) {
				types.set(i, newType);
			}
		}
		if (oldType instanceof AbstractHasFollowers)
			((AbstractHasFollowers) oldType).addFollower(this);
	}

	@Override
	public boolean compare(TLAType o) {
		if (this.contains(o))
			return false;
		if (o.getKind() == UNTYPED)
			return true;
		if (o instanceof TupleType) {
			TupleType t = (TupleType) o;
			if (this.types.size() != t.types.size()) {
				return false;
			}
			for (int i = 0; i < types.size(); i++) {
				if (!types.get(i).compare(t.types.get(i)))
					return false;
			}
			return true;
		}

		if (o instanceof TupleOrFunction) {
			return o.compare(this);
		}

		return false;
	}

	@Override
	public boolean contains(TLAType o) {
		for (TLAType tlaType : types) {
			if (tlaType.equals(o) || tlaType.contains(o))
				return true;
		}
		return false;
	}

	@Override
	public boolean isUntyped() {
		for (TLAType tlaType : types) {
			if (tlaType.isUntyped())
				return true;
		}
		return false;
	}

	@Override
	public TLAType cloneTLAType() {
		List<TLAType> list = new ArrayList<>();
		for (TLAType tlaType : types) {
			list.add(tlaType.cloneTLAType());
		}
		return new TupleType(list);
	}

	@Override
	public TLAType unify(TLAType o) throws UnificationException {
		if (!this.compare(o)) {
			throw new UnificationException();
		}
		if (o instanceof UntypedType) {
			((UntypedType) o).setFollowersTo(this);
			return this;
		}
		if (o instanceof TupleType) {
			TupleType tuple = (TupleType) o;

			for (int i = 0; i < types.size(); i++) {
				TLAType res = types.get(i).unify(tuple.types.get(i));
				types.set(i, res);
				if (res instanceof AbstractHasFollowers)
					((AbstractHasFollowers) res).addFollower(this);
			}
			return this;
		}

		if (o instanceof TupleOrFunction) {
			return o.unify(this);
		}
		throw new RuntimeException();
	}

	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder();
		for (int i = 0; i < types.size(); i++) {
			if (types.get(i) instanceof TupleType && i != 0) {
				sb.append("(").append(types.get(i)).append(")");
			} else
				sb.append(types.get(i));
			if (i < types.size() - 1) {
				sb.append("*");
			}
		}
		return sb.toString();
	}

	@Override
	public PExpression getBNode() {
		return ASTBuilder.createNestedMultOrCard(types.stream().map(TLAType::getBNode).collect(Collectors.toList()));
	}

	public void apply(TypeVisitorInterface visitor) {
		visitor.caseTupleType(this);
	}

}
