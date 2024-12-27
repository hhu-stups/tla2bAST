package de.tla2b.config;

import de.tla2b.types.TLAType;
import tlc2.value.impl.Value;

public class ValueObj {
	private final Value value;
	private final TLAType type;

	public ValueObj(Value value, TLAType t) {
		this.value = value;
		this.type = t;
	}

	public Value getValue() {
		return value;
	}

	public TLAType getType() {
		return type;
	}
}
