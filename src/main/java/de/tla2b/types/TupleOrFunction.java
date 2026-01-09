package de.tla2b.types;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

import de.be4.classicalb.core.parser.node.PExpression;
import de.tla2b.exceptions.UnificationException;
import de.tla2b.output.TypeVisitorInterface;

public final class TupleOrFunction extends AbstractHasFollowers implements IDefaultableType {

	private final Map<Integer, TLAType> types = new HashMap<>();

	private TupleOrFunction() {
		super(TUPLE_OR_FUNCTION);
	}

	public TupleOrFunction(int index, TLAType type) {
		this();
		if (index <= 0) {
			throw new IllegalArgumentException("tuples are 1-indexed");
		}
		types.put(index, type);
		if (type instanceof AbstractHasFollowers) {
			((AbstractHasFollowers) type).addFollower(this);
		}
	}

	public static TLAType createTupleOrFunctionType(List<TLAType> list) {
		TupleOrFunction tOrF = new TupleOrFunction();
		for (int i = 0; i < list.size(); i++) {
			TLAType type = list.get(i);
			tOrF.types.put(i + 1, type);
			if (type instanceof AbstractHasFollowers) {
				((AbstractHasFollowers) type).addFollower(tOrF);
			}
		}
		return tOrF.update();
	}

	public void apply(TypeVisitorInterface visitor) {
		visitor.caseTupleOrFunctionType(this);
	}

	@Override
	public String toString() {
		return "TupleOrFunction(" + types.entrySet().stream()
				.sorted(Map.Entry.comparingByKey())
				.map(entry -> entry.getKey() + " : " + entry.getValue())
				.collect(Collectors.joining(", ")) + ")";
	}

	@Override
	public PExpression getBNode() {
		throw new UnsupportedOperationException("TupleOrFunction has no corresponding B node");
	}

	@Override
	public boolean compare(TLAType o) {
		if (this.contains(o) || o.contains(this)) {
			return false;
		} else if (o.getKind() == UNTYPED) {
			return true;
		} else if (o instanceof FunctionType) {
			FunctionType t = (FunctionType) o;
			return t.getDomain().compare(IntType.getInstance()) &&
				this.types.values().stream().allMatch(type -> type.compare(t.getRange()));
		} else if (o instanceof TupleType) {
			TupleType tupleType = (TupleType) o;
			List<TLAType> myTypes = typesAsContiguousList();
			List<TLAType> otherTypes = tupleType.getTypes();
			if (myTypes.size() > otherTypes.size()) {
				// we have more type information, not unifiable
				return false;
			}
			for (int i = 0; i < myTypes.size(); i++) {
				if (!myTypes.get(i).compare(otherTypes.get(i))) {
					return false;
				}
			}
			// all overhang is padded with Untyped which is comparable to anything
			return true;
		} else if (o instanceof TupleOrFunction) {
			TupleOrFunction other = (TupleOrFunction) o;
			List<TLAType> myTypes = typesAsContiguousList();
			List<TLAType> otherTypes = other.typesAsContiguousList();
			for (int i = 0; i < Math.min(myTypes.size(), otherTypes.size()); i++) {
				if (!myTypes.get(i).compare(otherTypes.get(i))) {
					return false;
				}
			}
			// all overhang is padded with Untyped which is comparable to anything
			return true;
		}
		// this type is not comparable to all other types
		return false;
	}

	@Override
	public boolean contains(TLAType o) {
		return this.types.values().stream().anyMatch(type -> type.equals(o) || type.contains(o));
	}

	@Override
	public boolean isUntyped() {
		return true;
	}

	@Override
	public TLAType cloneTLAType() {
		TupleOrFunction res = new TupleOrFunction();
		types.forEach((i, type) -> {
			TLAType cloned = type.cloneTLAType();
			res.types.put(i, cloned);
			if (cloned instanceof AbstractHasFollowers) {
				((AbstractHasFollowers) cloned).addFollower(res);
			}
		});
		return res;
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
		if (o instanceof FunctionType) {
			FunctionType funcType = (FunctionType) o;
			TLAType res = funcType.getRange();
			for (TLAType type : types.values()) {
				res = res.unify(type);
			}
			this.setFollowersTo(funcType);
			return funcType;
		}
		if (o instanceof TupleType) {
			TupleType tupleType = (TupleType) o;
			List<TLAType> myTypes = typesAsContiguousList();
			List<TLAType> otherTypes = tupleType.getTypes();
			for (int i = 0; i < myTypes.size(); i++) {
				otherTypes.get(i).unify(myTypes.get(i));
			}
			this.setFollowersTo(tupleType);
			return tupleType;
		}
		if (o instanceof TupleOrFunction) {
			TupleOrFunction other = (TupleOrFunction) o;
			for (int otherI : new HashSet<>(other.types.keySet())) {
				TLAType otherType = other.types.get(otherI);
				if (types.containsKey(otherI)) {
					types.get(otherI).unify(otherType);
				} else {
					types.put(otherI, otherType);
					if (otherType instanceof AbstractHasFollowers) {
						((AbstractHasFollowers) otherType).addFollower(this);
					}
				}
			}
			other.setFollowersTo(this);
			return this.update();
		}
		throw new RuntimeException();
	}

	public void setNewType(AbstractHasFollowers oldType, TLAType newType) {
		new HashMap<>(types).forEach((key, value) -> {
			if (value == oldType) {
				types.put(key, newType);
				if (newType instanceof AbstractHasFollowers) {
					((AbstractHasFollowers) newType).addFollower(this);
				}
			}
		});
		update();
	}

	@Override
	public TLAType setToDefault() {
		List<TLAType> types = typesAsContiguousList();
		if (allTypesComparableStrict(types)) {
			FunctionType func = new FunctionType(IntType.getInstance(), types.isEmpty() ? new UntypedType() : types.get(0));
			this.setFollowersTo(func);
			return func;
		}

		TupleType tuple = new TupleType(types);
		this.setFollowersTo(tuple);
		return tuple;
	}

	private TLAType update() {
		List<TLAType> types = typesAsContiguousList();
		if (!allTypesComparable(types)) {
			TupleType tuple = new TupleType(types);
			this.setFollowersTo(tuple);
			return tuple;
		}
		return this;
	}

	private List<TLAType> typesAsContiguousList() {
		List<TLAType> list = new ArrayList<>();
		types.forEach((iBoxed, type) -> {
			if (iBoxed == null || iBoxed <= 0 || type == null) {
				throw new IllegalStateException();
			}
			int i = iBoxed - 1;
			if (i < list.size()) {
				TLAType current = list.get(i);
				if (current instanceof UntypedType && !(((AbstractHasFollowers) current).hasFollowers())) {
					list.set(i, type);
				} else {
					throw new IllegalStateException();
				}
			} else {
				for (int j = list.size(); j < i; j++) {
					list.add(new UntypedType());
				}
				list.add(type);
			}
		});
		return list;
	}

	private static boolean allTypesComparable(List<TLAType> typeList) {
		for (int i = 0; i < typeList.size() - 1; i++) {
			TLAType t1 = typeList.get(i);
			for (int j = i + 1; j < typeList.size(); j++) {
				TLAType t2 = typeList.get(j);
				if (!t1.compare(t2)) {
					return false;
				}
			}
		}
		return true;
	}

	private static boolean allTypesComparableStrict(List<TLAType> typeList) {
		for (int i = 0; i < typeList.size() - 1; i++) {
			TLAType t1 = typeList.get(i);
			for (int j = i + 1; j < typeList.size(); j++) {
				TLAType t2 = typeList.get(j);
				if ((t1.isUntyped() || t2.isUntyped()) && t1 != t2) {
					// untyped could become different types
					// technically this is too strict, nested untypedness could also be the same untyped vars
					return false;
				}
				if (!t1.compare(t2)) {
					return false;
				}
			}
		}
		return true;
	}
}
