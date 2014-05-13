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
	private LinkedHashMap<String, TLAType> types;
	private boolean extensible;
	private boolean incompleteStruct;

	public StructType() {
		super(STRUCT);
		types = new LinkedHashMap<String, TLAType>();
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
		Iterator<Entry<String, TLAType>> iterator = set.iterator();

		while (iterator.hasNext()) {
			Entry<String, TLAType> entry = iterator.next();
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
		Iterator<TLAType> ts = types.values().iterator();
		while (ts.hasNext()) {
			TLAType bType = (TLAType) ts.next();
			if (bType.isUntyped())
				return true;
		}
		return false;
	}

	public boolean compare(TLAType o) {
		if (this.contains(o) || o.contains(this))
			return false;
		if (o.getKind() == UNTYPED)
			return true;

		if (o instanceof StructOrFunctionType) {
			return o.compare(this);
		}
		if (o instanceof StructType) {
			StructType s = (StructType) o;

			Iterator<String> thisKeys = types.keySet().iterator();
			while (thisKeys.hasNext()) {
				String fieldName = (String) thisKeys.next();
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
			StructType s = (StructType) o;
			boolean extendStruct = false;

			if (this.incompleteStruct && s.incompleteStruct) {
				extendStruct = false;
			} else if (this.incompleteStruct) {
				if (s.types.keySet().containsAll(this.types.keySet())) {
					extendStruct = false;
				} else {
					extendStruct = true;
				}
			} else if (s.incompleteStruct) {
				if (this.types.keySet().containsAll(s.types.keySet())) {
					extendStruct = false;
				} else {
					extendStruct = true;
				}
			} else {
				extendStruct = !s.types.keySet().equals(this.types.keySet());
			}
			this.extensible = this.extensible || s.extensible || extendStruct;

			Iterator<String> keys = s.types.keySet().iterator();
			while (keys.hasNext()) {
				String fieldName = (String) keys.next();
				TLAType sType = s.types.get(fieldName);
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
		Iterator<Entry<String, TLAType>> iterator = set.iterator();

		while (iterator.hasNext()) {
			Entry<String, TLAType> entry = iterator.next();
			String field = entry.getKey();
			TLAType type = entry.getValue().cloneTLAType();
			clone.add(field, type);
		}

		return clone;
	}

	public ArrayList<String> getFields() {
		ArrayList<String> fields = new ArrayList<String>();
		Iterator<String> keys = this.types.keySet().iterator();
		while (keys.hasNext()) {
			String fieldName = (String) keys.next();
			fields.add(fieldName);
		}
		return fields;
	}

	@Override
	public boolean contains(TLAType o) {
		Iterator<TLAType> ts = types.values().iterator();
		while (ts.hasNext()) {
			TLAType bType = (TLAType) ts.next();
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
			String fieldName = (String) keys.next();
			sb.append(fieldName).append(":").append(types.get(fieldName));
			if (keys.hasNext())
				sb.append(",");
		}
		sb.append(")");
		return sb.toString();
	}

	@Override
	public PExpression getBNode() {
		List<PRecEntry> recList = new ArrayList<PRecEntry>();
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
