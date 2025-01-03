package de.tla2b.config;

import de.tla2b.types.TLAType;
import tla2sany.semantic.AbortException;
import tla2sany.semantic.NumeralNode;
import tla2sany.st.TreeNode;
import tlc2.value.impl.Value;

public class TLCValueNode extends NumeralNode {

	private final Value value;
	private final TLAType type;

	public TLCValueNode(Value value, TLAType type, TreeNode stn) throws AbortException {
		super("1337", stn);
		this.value = value;
		this.type = type;
	}

	public String toString2() {
		return "\n*TLCValueNode: Value: '" + value.toString() + "'";
	}

	public TLAType getType() {
		return type;
	}

	public Value getValue() {
		return value;
	}
}
