package de.tla2b.analysis;

import de.tla2b.exceptions.NotImplementedException;
import tla2sany.semantic.OpApplNode;
import tla2sany.semantic.OpDefNode;
import tlc2.tool.BuiltInOPs;

public class RecursiveDefinition extends BuiltInOPs {

	private final OpDefNode def;
	private OpApplNode ifThenElse;

	public RecursiveDefinition(OpDefNode def) throws NotImplementedException {
		this.def = def;
		evalRecursiveDefinition();
	}

	private void evalRecursiveDefinition() throws NotImplementedException {
		if (def.getBody() instanceof OpApplNode) {
			OpApplNode o = (OpApplNode) def.getBody();
			if (getOpCode(o.getOperator().getName()) == OPCODE_ite) {// IF THEN ELSE
				ifThenElse = o;
				return;
			}
		}
		throw new NotImplementedException(
			"Only IF/THEN/ELSE or CASE constructs are supported at the body of a recursive function.");
	}

	public OpDefNode getOpDefNode() {
		return def;
	}

	public OpApplNode getIfThenElse() {
		return ifThenElse;
	}
}
