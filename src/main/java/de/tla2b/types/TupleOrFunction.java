package de.tla2b.types;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map.Entry;

import de.be4.classicalb.core.parser.node.PExpression;
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

	public static TLAType createTupleOrFunctionType(List<TLAType> list) {
		TupleOrFunction tOrF = new TupleOrFunction();
		tOrF.add(list);
		return tOrF.update();
	}

	public void add(List<TLAType> list) {
		for (int i = 0; i < list.size(); i++) {
			TLAType type = list.get(i);
			types.put(i + 1, type);
			if (type instanceof AbstractHasFollowers) {
				((AbstractHasFollowers) type).addFollower(this);
			}
		}
	}

	public void apply(TypeVisitorInterface visitor) {
		throw new RuntimeException("Type " + this + " is not a complete type.");
	}

	@Override
	public String toString() {

		StringBuilder sb = new StringBuilder();
		sb.append("TupleOrFunction");
		sb.append("(");
		for (Iterator<Integer> keys = types.keySet().iterator(); keys.hasNext();) {
			Integer key = keys.next();
			sb.append(key);
			sb.append(" : ").append(types.get(key));
			if (keys.hasNext())
				sb.append(", ");
		}
		sb.append(")");
		return sb.toString();
		// throw new RuntimeException("Type " + sb + "is incomplete");
	}

	@Override
	public PExpression getBNode() {
		FunctionType func = new FunctionType();
		func.setDomain(IntType.getInstance());
		func.setRange(new UntypedType());
		FunctionType res;
		try {
			res = (FunctionType) func.unify(this);
			return res.getBNode();
		} catch (UnificationException e) {
			// tuple
			boolean isTuple = true;
			ArrayList<TLAType> typeList = new ArrayList<TLAType>();
			for (int i = 1; i <= types.keySet().size(); i++) {
				if (types.keySet().contains(i)) {
					typeList.add(types.get(i));
				} else {
					isTuple = false;
					break;
				}
			}

			if (isTuple) {
				return new TupleType(typeList).getBNode();
			} else {
				StringBuilder sb = new StringBuilder();
				sb.append("(");
				for (Iterator<Integer> keys = types.keySet().iterator(); keys
						.hasNext();) {
					Integer key = keys.next();
					sb.append(key);
					sb.append(" : ").append(types.get(key));
					if (keys.hasNext())
						sb.append(", ");
				}
				sb.append(")");
				throw new RuntimeException("Type " + sb + "is incomplete");
			}

		}

	}

	@Override
	public boolean compare(TLAType o) {
		if (this.contains(o) || o.contains(this)) {
			return false;
		}
		if (o.getKind() == UNTYPED)
			return true;

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
			TupleType tupleType = (TupleType) o;
			for (Integer index : this.types.keySet()) {
				if (index >= 1
						&& index <= tupleType.getTypes().size()
						&& this.types.get(index).compare(
								tupleType.getTypes().get(index + -1))) {
				} else {
					return false;
				}
			}
			return true;
		}
		if (o instanceof TupleOrFunction) {
			TupleOrFunction other = (TupleOrFunction) o;
			if (isTupleOrFunction(this, other)) {
				return true;
			}

			try {
				for (int i = 1; i <= types.keySet().size(); i++) {
					if (!types.get(i).compare(other.types.get(i))) {
						return false;
					}
				}
			} catch (Exception e) {
				return false;
			}

			return true;
		}

		// this type is not comparable to all other types
		return false;
	}

	private static boolean isTupleOrFunction(TupleOrFunction t1,
			TupleOrFunction t2) {
		List<TLAType> typeList = new ArrayList<TLAType>();
		typeList.addAll(t1.types.values());
		typeList.addAll(t2.types.values());
		if (comparable(typeList)) {
			return true;
		}
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
		// if (complete == false) {
		// return true;
		// }
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
			res.types.put(Integer.valueOf(entry.getKey().intValue()), entry
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

			List<TLAType> typeList = new ArrayList<TLAType>();
			for (int i = 0; i < tupleType.getTypes().size(); i++) {
				if (this.types.containsKey(i + 1)) {
					TLAType res = tupleType.getTypes().get(i)
							.unify(this.types.get(i + 1));
					typeList.add(res);
				} else {
					typeList.add(tupleType.getTypes().get(i));
				}
			}
			TupleType r = new TupleType(typeList);
			this.setFollowersTo(r);
			tupleType.setFollowersTo(r);
			return r;
		}

		if (o instanceof TupleOrFunction) {
			TupleOrFunction other = (TupleOrFunction) o;
			for (Integer i : other.types.keySet()) {
				if (this.types.containsKey(i)) {
					TLAType res = other.types.get(i).unify(this.types.get(i));
					if (res instanceof AbstractHasFollowers)
						((AbstractHasFollowers) res).addFollower(this);
					this.types.put(i, res);
				} else {
					TLAType res = other.types.get(i);
					if (res instanceof AbstractHasFollowers)
						((AbstractHasFollowers) res).addFollower(this);
					this.types.put(i, res);
				}

			}
			other.setFollowersTo(this);
			return this;
			// if (isTupleOrFunction(this, other)) {
			// for (Integer i : this.types.keySet()) {
			// if (other.types.containsKey(i)) {
			// TLAType res = this.types.get(i).unify(
			// other.types.get(i));
			// if (res instanceof AbstractHasFollowers) {
			// ((AbstractHasFollowers) res).addFollower(this);
			// }
			// this.types.put(i, res);
			// }
			// }
			// for (Integer i : other.types.keySet()) {
			// if (!this.types.containsKey(i)) {
			// TLAType res = other.types.get(i);
			// if (res instanceof AbstractHasFollowers) {
			// ((AbstractHasFollowers) res).addFollower(this);
			// }
			// this.types.put(i, res);
			// }
			// }
			// return this;
			// } else {
			// ArrayList<TLAType> list1 = new ArrayList<TLAType>();
			// for (int i = 1; i <= types.keySet().size(); i++) {
			// list1.add(types.get(i));
			// }
			// TupleType tuple1 = new TupleType(list1);
			//
			// ArrayList<TLAType> list2 = new ArrayList<TLAType>();
			// for (int i = 1; i <= other.types.keySet().size(); i++) {
			// list2.add(other.types.get(i));
			// }
			// TupleType tuple2 = new TupleType(list2);
			// return tuple1.unify(tuple2);
			// }

		}

		throw new RuntimeException();
	}

	public void setNewType(AbstractHasFollowers oldType, TLAType newType) {
		LinkedHashMap<Integer, TLAType> temp = new LinkedHashMap<Integer, TLAType>(
				types);
		for (Entry<Integer, TLAType> entry : temp.entrySet()) {
			if (entry.getValue().equals(oldType)) {
				types.put(entry.getKey(), newType);
				if (newType instanceof AbstractHasFollowers) {
					((AbstractHasFollowers) newType).addFollower(this);
					;
				}
			}
		}

		update();
	}

	public TLAType getFinalType() {
		List<TLAType> list = new ArrayList<TLAType>(this.types.values());

		if (comparable(list)) {
			FunctionType func = new FunctionType(IntType.getInstance(),
					new UntypedType());
			try {
				func = (FunctionType) func.unify(this);
				this.setFollowersTo(func);
				return func;
			} catch (UnificationException e) {
				throw new RuntimeException();
			}
		} else {
			TupleType tuple = new TupleType(list);
			this.setFollowersTo(tuple);
			return tuple;
		}

	}

	private TLAType update() {
		List<TLAType> list = new ArrayList<TLAType>(this.types.values());
		// if (allTyped(list) && comparable(list)) {
		// FunctionType func = new FunctionType(IntType.getInstance(),
		// new UntypedType());
		// try {
		// func = func.unify(this);
		// this.setFollowersTo(func);
		// return func;
		// } catch (UnificationException e) {
		// throw new RuntimeException();
		// }
		// } else
		if (!comparable(list)) {
			TupleType tuple = new TupleType(list);
			this.setFollowersTo(tuple);
			return tuple;

			// boolean isTuple = true;
			// ArrayList<TLAType> typeList = new ArrayList<TLAType>();
			// for (int i = 1; i <= types.keySet().size(); i++) {
			// if (types.keySet().contains(i)) {
			// typeList.add(types.get(i));
			// } else {
			// isTuple = false;
			// break;
			// }
			// }
			//
			// if (isTuple) {
			// return new TupleType(typeList).toString();
		}
		return this;
	}

	private static boolean comparable(List<TLAType> typeList) {
		for (int i = 0; i < typeList.size() - 1; i++) {
			TLAType t1 = typeList.get(i);
			for (int j = 1; j < typeList.size(); j++) {
				TLAType t2 = typeList.get(j);
				if (!t1.compare(t2))
					return false; // tuple
			}
		}
		return true;
	}
}
