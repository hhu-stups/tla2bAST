package de.tla2b.types;

import java.util.Collections;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.Map.Entry;

import de.be4.classicalb.core.parser.node.PExpression;
import de.tla2b.exceptions.TypeErrorException;
import de.tla2b.exceptions.UnificationException;
import de.tla2b.output.TypeVisitorInterface;

public class TupleOrFunction extends AbstractHasFollowers {
	private final LinkedHashMap<Integer, TLAType> types = new LinkedHashMap<Integer, TLAType>();

	public TupleOrFunction(Integer index, TLAType type) {
		super(TUPLE_OR_FUNCTION);
		types.put(index, type);
		if (type instanceof AbstractHasFollowers) {
			((AbstractHasFollowers) type).addFollower(this);
		}
	}

	public TupleOrFunction() {
		super(TUPLE_OR_FUNCTION);
	}

	public void apply(TypeVisitorInterface visitor) {
		throw new RuntimeException("Type " + this + " is not a complete type.");
	}

	@Override
	public String toString() {
		FunctionType func = new FunctionType();
		func.setDomain(IntType.getInstance());
		func.setRange(new UntypedType());
		FunctionType res;
		try {
			res = func.unify(this);
		} catch (UnificationException e) {
			StringBuilder sb = new StringBuilder();
			sb.append("TupleOrFunction(");
			for (Iterator<Integer> keys = types.keySet().iterator(); keys.hasNext();) {
				Integer key = keys.next();
				sb.append(key);
				sb.append(" : ").append(types.get(key));
				if (keys.hasNext())
					sb.append(", ");
			}
			sb.append(")");
			throw new RuntimeException("Type "+ sb + "is incomplete");
		}
		
		return res.toString();
		

	}

	@Override
	public PExpression getBNode() {
		return null;
	}

	@Override
	public boolean compare(TLAType o) {
		if (this.contains(o) || o.contains(this))
			return false;
		if (o.getKind() == UNTYPED)
			return true;
		if (o instanceof TupleOrFunction) {
			TupleOrFunction t = (TupleOrFunction) o;
			for (Entry<Integer, TLAType> entry : types.entrySet()) {
				if (t.types.containsKey(entry.getKey())
						&& entry.getValue()
								.compare(t.types.get(entry.getKey()))) {
					return false;
				}
			}
		}
		if (o instanceof FunctionType) {
			FunctionType t = (FunctionType) o;
			if (!t.getDomain().compare(IntType.getInstance())) {
				return false;
			}
			for (TLAType type : this.types.values()) {
				if (!type.compare(t.getRange())) {
					return false;
				}
			}
			return true;
		}
		if (o instanceof TupleType) {
			TupleType t = (TupleType) o;
			for (int i = 0; i < t.getTypes().size(); i++) {
				if (this.types.containsKey(i + 1)) {
					if (!t.getTypes().get(i).compare(this.types.get(i + 1))) {
						return false;
					}
				}
			}
			return true;
		}
		// this type is not comparable with all other types
		return false;
	}

	@Override
	public boolean contains(TLAType o) {
		for (TLAType type : this.types.values()) {
			if (type.equals(o) || type.contains(o)) {
				return true;
			}
		}
		return false;
	}

	@Override
	public boolean isUntyped() {
		for (TLAType type : types.values()) {
			if (type.isUntyped())
				return true;
		}
		FunctionType func = new FunctionType();
		func.setDomain(IntType.getInstance());
		func.setRange(new UntypedType());
		if (func.compare(this)) {
			return false;
		} else {
			return true;
		}
	}

	@Override
	public TLAType cloneTLAType() {
		TupleOrFunction res = new TupleOrFunction();
		for (Entry<Integer, TLAType> entry : this.types.entrySet()) {
			res.types.put(new Integer(entry.getKey().intValue()), entry
					.getValue().cloneTLAType());
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
		if (o instanceof FunctionType) {
			FunctionType funcType = (FunctionType) o;
			TLAType res = funcType.getRange();
			for (TLAType type : types.values()) {
				if (type instanceof AbstractHasFollowers) {
					((AbstractHasFollowers) type).removeFollower(this);
				}
				res = res.unify(type);
			}
			return funcType;
		}
		if (o instanceof TupleType) {
			TupleType tupleType = (TupleType) o;
			int max = Collections.max(types.keySet());
			if (max <= tupleType.getTypes().size()) {
				for (Entry<Integer, TLAType> entry : this.types.entrySet()) {
					int index = entry.getKey();
					TLAType type = entry.getValue();
					if (type instanceof AbstractHasFollowers) {
						((AbstractHasFollowers) type).removeFollower(this);
					}
					TLAType elementOfTuple = tupleType.getTypes()
							.get(index - 1);
					elementOfTuple.unify(type);
				}
				return tupleType;
			} else {
				TLAType range = new UntypedType();
				for (TLAType type : types.values()) {
					if (type instanceof AbstractHasFollowers) {
						((AbstractHasFollowers) type).removeFollower(this);
					}
					range = range.unify(type);
				}
				FunctionType funcType = new FunctionType(IntType.getInstance(),
						range);
				return funcType.unify(tupleType);
			}
		}
		throw new RuntimeException();
	}

	public void setNewType(AbstractHasFollowers oldType,
			TLAType newType) {
		LinkedHashMap<Integer, TLAType> temp = new LinkedHashMap<Integer, TLAType>(types);
		for (Entry<Integer, TLAType> entry : temp.entrySet()) {
			if(entry.getValue().equals(oldType)){
				types.put(entry.getKey(), newType);
				if (newType instanceof AbstractHasFollowers) {
					((AbstractHasFollowers) newType).addFollower(this);;
				}
			}
		}
		
	}

}
