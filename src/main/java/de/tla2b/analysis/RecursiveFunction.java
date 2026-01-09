package de.tla2b.analysis;

import de.tla2b.exceptions.NotImplementedException;

import tla2sany.semantic.OpApplNode;
import tla2sany.semantic.OpDefNode;

public class RecursiveFunction {

	private final OpDefNode def;
	private final OpApplNode rfs;
	private OpApplNode ifThenElse;

	public RecursiveFunction(OpDefNode n, OpApplNode rfs)
		throws NotImplementedException {
		def = n;
		this.rfs = rfs;
		//evalDef();
	}


//	/**
//	 * @throws NotImplementedException
//	 * 
//	 */
//	private void evalDef() throws NotImplementedException {
//		ExprOrOpArgNode e = rfs.getArgs()[0];
//		//System.out.println(rfs.toString(5));
//		if (e instanceof OpApplNode) {
//			OpApplNode o = (OpApplNode) e;
//			switch (BuiltInOPs.getOpCode(o.getOperator().getName())) {
//			case ToolGlobals.OPCODE_ite: { // IF THEN ELSE
//				ifThenElse = o;
//				return;
//			}
//			}
//			throw new NotImplementedException(
//					"Only IF/THEN/ELSE or CASE constructs are supported at the body of a recursive function.");
//		} else {
//			throw new NotImplementedException(
//					"Only IF/THEN/ELSE or CASE constructs are supported at the body of a recursive function.");
//		}
//	}

	public OpDefNode getOpDefNode() {
		return def;
	}

	public OpApplNode getRF() {
		return rfs;
	}

	public OpApplNode getIfThenElse() {
		return ifThenElse;
	}
}
