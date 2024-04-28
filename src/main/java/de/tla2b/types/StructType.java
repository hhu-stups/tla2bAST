package de.tla2b.types;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map.Entry;
import java.util.Set;

import de.be4.classicalb.core.parser.node.ABoolSetExpression;
import de.be4.classicalb.core.parser.node.AMultOrCartExpression;
import de.be4.classicalb.core.parser.node.APowSubsetExpression;
import de.be4.classicalb.core.parser.node.ARecEntry;
import de.be4.classicalb.core.parser.node.AStructExpression;
import de.be4.classicalb.core.parser.node.PExpression;
import de.be4.classicalb.core.parser.node.PRecEntry;
import de.tla2b.exceptions.UnificationException;
import de.tla2b.output.TypeVisitorInterface;
import de.tla2bAst.BAstCreator;

public class StructType extends AbstractHasFollowers {
	private final LinkedHashMap<String, TLAType> types;
	private boolean extensible;
	private boolean incompleteStruct;

	public StructType() {
		super(STRUCT);
		types = new LinkedHashMap<>();
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
		if (type instanceof AbstractHasFollowers) {
			// set new reference
			((AbstractHasFollowers) type).addFollower(this);
		}
		types.put(name, type);
	}

	public void setNewType(TLAType old, TLAType New) {
		Set<Entry<String, TLAType>> set = types.entrySet();

		for (Entry<String, TLAType> entry : set) {
			if (entry.getValue() == old) {
				String key = entry.getKey();
				if (New instanceof AbstractHasFollowers) {
					// set new reference
					((AbstractHasFollowers) New).addFollower(this);
				}
				types.put(key, New);
			}
		}
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
			boolean extendStruct = false;

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
					if (sType instanceof AbstractHasFollowers) {
						// set new reference
						((AbstractHasFollowers) sType).addFollower(this);
					}
					this.types.put(fieldName, sType);
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

		Set<Entry<String, TLAType>> set = this.types.entrySet();

		for (Entry<String, TLAType> entry : set) {
			String field = entry.getKey();
			TLAType type = entry.getValue().cloneTLAType();
			clone.add(field, type);
		}

		return clone;
	}

	public ArrayList<String> getFields() {
		ArrayList<String> fields = new ArrayList<>(this.types.keySet());
		return fields;
	}

	@Override
	public boolean contains(TLAType o) {
		for (TLAType bType : types.values()) {
			if (bType.equals(o) || bType.contains(o))
				return true;
		}
		return false;
	}

	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder();
		sb.append("struct(");
		Iterator<String> keys = types.keySet().iterator();
		if (!keys.hasNext()) {
			sb.append("...");
		}
		while (keys.hasNext()) {
			String fieldName = keys.next();
			sb.append(fieldName).append(":").append(types.get(fieldName));
			if (keys.hasNext())
				sb.append(",");
		}
		sb.append(")");
		return sb.toString();
	}

	@Override
	public PExpression getBNode() {
		List<PRecEntry> recList = new ArrayList<>();
		for (Entry<String, TLAType> entry : types.entrySet()) {
			ARecEntry rec = new ARecEntry();
			rec.setIdentifier(BAstCreator.createIdentifierNode(entry.getKey()));
			if (extensible) {

				AMultOrCartExpression cart = new AMultOrCartExpression();
				cart.setLeft(new ABoolSetExpression());
				cart.setRight(entry.getValue().getBNode());
				APowSubsetExpression pow = new APowSubsetExpression(cart);
				rec.setValue(pow);
			} else {
				rec.setValue(entry.getValue().getBNode());
			}
			recList.add(rec);
		}
		return new AStructExpression(recList);
	}

	public void apply(TypeVisitorInterface visitor) {
		visitor.caseStructType(this);
	}

	public LinkedHashMap<String, TLAType> getTypeTable() {
		return this.types;
	}

}
