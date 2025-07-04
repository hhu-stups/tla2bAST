package de.tla2b.types;

import de.be4.classicalb.core.parser.node.PExpression;
import de.tla2b.exceptions.UnificationException;
import de.tla2b.output.TypeVisitorInterface;

import java.util.Arrays;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.Map;

public class StructOrFunctionType extends AbstractHasFollowers {
	private final Map<String, TLAType> types = new LinkedHashMap<>();

	public StructOrFunctionType(String name, TLAType type) {
		super(STRUCT_OR_FUNCTION);
		types.put(name, type);
	}

	public StructOrFunctionType() {
		super(STRUCT_OR_FUNCTION);
	}

	public void setNewType(TLAType oldType, TLAType newType) {
		types.forEach((name, type) -> {
			if (type == oldType) {
				types.put(name, newType);
				if (newType instanceof AbstractHasFollowers) { // set new reference
					((AbstractHasFollowers) newType).addFollower(this);
				}
			}
		});
		testRecord();
	}

	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder();
		sb.append("StructOrFunction(");
		for (Iterator<String> keys = types.keySet().iterator(); keys.hasNext(); ) {
			String key = keys.next();
			sb.append("\"").append(key).append("\"");
			sb.append(" : ").append(types.get(key));
			if (keys.hasNext())
				sb.append(", ");
		}
		sb.append(")");
		return sb.toString();
	}

	@Override
	public boolean compare(TLAType o) {
		if (this.contains(o) || o.contains(this))
			return false;
		if (o.getKind() == UNTYPED)
			return true;
		if (o instanceof StructType) {
			StructType s = (StructType) o;
			for (String fieldName : types.keySet()) {
				if (s.getFields().contains(fieldName)) {
					if (!this.types.get(fieldName).compare(s.getType(fieldName))) {
						return false;
					}
				}
			}
			return true;
		}

		if (o instanceof StructOrFunctionType) {
			StructOrFunctionType s = (StructOrFunctionType) o;

			for (String fieldName : types.keySet()) {
				if (s.types.containsKey(fieldName)) {
					if (!this.types.get(fieldName).compare(
						s.types.get(fieldName))) {
						return false;
					}
				}
			}
			return true;
		}
		return false;
	}

	@Override
	public boolean contains(TLAType o) {
		for (String fieldName : types.keySet()) {
			TLAType type = this.types.get(fieldName);
			if (type.equals(o) || type.contains(o))
				return true;
		}
		return false;
	}

	@Override
	public boolean isUntyped() {
		return true;
	}

	@Override
	public TLAType cloneTLAType() {
		StructOrFunctionType res = new StructOrFunctionType();
		for (String field : types.keySet()) {
			res.types.put(field, this.types.get(field));
		}
		return res;
	}

	@Override
	public TLAType unify(TLAType o) throws UnificationException {
		if (!this.compare(o))
			throw new UnificationException();

		if (o instanceof UntypedType) {
			((UntypedType) o).setFollowersTo(this);
			return this;
		}

		if (o instanceof SetType) {
			Iterator<TLAType> itr = types.values().iterator();
			TLAType temp = itr.next();
			while (itr.hasNext()) {
				temp = temp.unify(itr.next());
			}
			SetType found = new SetType(new TupleType(Arrays.asList(StringType.getInstance(), temp)));
			return found.unify(o);
		}
		if (o instanceof StructType) {
			StructType res = StructType.getIncompleteStruct();

			for (String field : types.keySet()) {
				res.add(field, this.types.get(field));
			}
			return o.unify(res);
		}
		if (o instanceof StructOrFunctionType) {
			StructOrFunctionType other = (StructOrFunctionType) o;
			for (String field : other.types.keySet()) {
				TLAType type = other.types.get(field);
				if (this.types.containsKey(field)) {
					TLAType res = this.types.get(field).unify(type);
					this.types.put(field, res);
				} else {
					if (type instanceof AbstractHasFollowers) {
						((AbstractHasFollowers) type).addFollower(this);
					}
					this.types.put(field, type);
				}
			}
			return testRecord();
		}
		return this;
	}

	private TLAType testRecord() {
		Iterator<TLAType> itr = types.values().iterator();
		TLAType temp = itr.next().cloneTLAType();
		while (itr.hasNext()) {
			TLAType next = itr.next().cloneTLAType();
			try {
				temp.unify(next);
			} catch (UnificationException e) {
				StructType res = new StructType();
				for (String field : this.types.keySet()) {
					res.add(field, this.types.get(field));
				}
				this.setFollowersTo(res);
				return res;
			}
		}
		return this;
	}

	public SetType getFunction() {
		Iterator<TLAType> itr = types.values().iterator();
		return new SetType(new TupleType(Arrays.asList(StringType.getInstance(), itr.next())));
	}

	@Override
	public PExpression getBNode() {
		throw new UnsupportedOperationException("StructOrFunctionType has no corresponding B node");
	}

	public void apply(TypeVisitorInterface visitor) {
		visitor.caseStructOrFunction(this);
	}

}
