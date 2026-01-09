package de.tla2b.types;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

import de.be4.classicalb.core.parser.node.*;
import de.tla2b.exceptions.UnificationException;
import de.tla2b.output.TypeVisitorInterface;

public class StructType extends AbstractHasFollowers {
	private final Map<String, TLAType> types = new LinkedHashMap<>();
	private boolean extensible;
	private boolean incompleteStruct;

	public StructType() {
		super(STRUCT);
		extensible = false;
		incompleteStruct = false;
	}

	public static StructType getIncompleteStruct() {
		StructType s = new StructType();
		s.incompleteStruct = true;
		return s;
	}

	public boolean isExtensible() {
		return extensible;
	}

	public TLAType getType(String fieldName) {
		return types.get(fieldName);
	}

	public void add(String name, TLAType type) {
		types.put(name, type);
		if (type instanceof AbstractHasFollowers) { // set new reference
			((AbstractHasFollowers) type).addFollower(this);
		}
	}

	public void setNewType(TLAType old, TLAType newType) {
		types.forEach((name, type) -> {
			if (type == old) {
				add(name, newType);
			}
		});
	}

	@Override
	public boolean isUntyped() {
		for (TLAType bType : types.values()) {
			if (bType.isUntyped())
				return true;
		}
		return false;
	}

	public boolean compare(TLAType o) {
		if (this.contains(o) || o.contains(this)) {
			return false;
		}
		if (o.getKind() == UNTYPED)
			return true;
		if (o instanceof StructOrFunctionType) {
			return o.compare(this);
		}
		if (o instanceof StructType) {
			StructType s = (StructType) o;
			return types.keySet().stream()
					.filter(s.types::containsKey)
					.allMatch(fieldName -> this.types.get(fieldName).compare(s.types.get(fieldName)));
		}
		return false;
	}

	public StructType unify(TLAType o) throws UnificationException {
		if (!this.compare(o)) {
			throw new UnificationException();
		}
		if (o instanceof AbstractHasFollowers)
			((AbstractHasFollowers) o).setFollowersTo(this);

		if (o instanceof StructOrFunctionType) {
			return (StructType) o.unify(this);
		}

		if (o instanceof StructType) {
			StructType otherStruct = (StructType) o;

			boolean extendStruct;
			if (this.incompleteStruct && otherStruct.incompleteStruct) {
				extendStruct = false;
			} else if (this.incompleteStruct) {
				extendStruct = !otherStruct.types.keySet().containsAll(this.types.keySet());
			} else if (otherStruct.incompleteStruct) {
				extendStruct = !this.types.keySet().containsAll(otherStruct.types.keySet());
			} else {
				extendStruct = !otherStruct.types.keySet().equals(this.types.keySet());
			}
			this.extensible = this.extensible || otherStruct.extensible || extendStruct;

			for (String fieldName : otherStruct.types.keySet()) {
				TLAType sType = otherStruct.types.get(fieldName);
				if (this.types.containsKey(fieldName)) {
					TLAType res = this.types.get(fieldName).unify(sType);
					this.types.put(fieldName, res);
				} else {
					add(fieldName, sType);
				}
				this.incompleteStruct = false;
			}
			return this;
		}
		return this;
	}

	@Override
	public StructType cloneTLAType() {
		StructType clone = new StructType();
		this.types.forEach((field, type) -> clone.add(field, type.cloneTLAType()));
		return clone;
	}

	public List<String> getFields() {
		return new ArrayList<>(this.types.keySet());
	}

	@Override
	public boolean contains(TLAType o) {
		return types.values().stream().anyMatch(bType -> bType.equals(o) || bType.contains(o));
	}

	@Override
	public String toString() {
		if (types.isEmpty())
			return "struct(...)";

		return "struct(" + types.entrySet().stream()
				.map(entry -> entry.getKey() + ":" + entry.getValue())
				.collect(Collectors.joining(",")) + ")";
	}

	@Override
	public PExpression getBNode() {
		List<PRecEntry> recList = new ArrayList<>();
		types.forEach((id, type) -> {
			PExpression value = extensible
					? new APowSubsetExpression(new AMultOrCartExpression(new ABoolSetExpression(), type.getBNode()))
					: type.getBNode();
			recList.add(new ARecEntry(new TIdentifierLiteral(id), value));
		});
		return new AStructExpression(recList);
	}

	public void apply(TypeVisitorInterface visitor) {
		visitor.caseStructType(this);
	}

	public Map<String, TLAType> getTypes() {
		return this.types;
	}

}
