package de.tla2b.translation;

import java.util.ArrayList;
import java.util.List;

import de.tla2b.analysis.AbstractASTVisitor;
import de.tla2b.analysis.BOperation;
import de.tla2b.analysis.SpecAnalyser;
import de.tla2b.global.BBuildIns;
import de.tla2b.global.BBuiltInOPs;
import de.tla2b.global.TranslationGlobals;
import de.tla2b.util.DebugUtils;

import tla2sany.semantic.*;

import tlc2.tool.BuiltInOPs;

import util.UniqueString;

public class OperationsFinder extends AbstractASTVisitor {
	private final SpecAnalyser specAnalyser;

	private String currentName;
	private List<OpApplNode> exists;
	// a list containing all existential quantifier which will be parameters in the resulting B Machine
	private final List<BOperation> bOperations;
	private final List<String> generatedOperations = new ArrayList<>();

	public OperationsFinder(SpecAnalyser specAnalyser) {
		this.specAnalyser = specAnalyser;
		this.bOperations = new ArrayList<>();
		if (specAnalyser.getNext() != null) {
			currentName = "Next";
			exists = new ArrayList<>();
			visitExprNode(specAnalyser.getNext());
		}
	}

	public void visitExprNode(ExprNode n) {
		switch (n.getKind()) {
			case OpApplKind: {
				visitOpApplNode((OpApplNode) n);
				return;
			}
			case NumeralKind:
			case DecimalKind:
				throw new RuntimeException(String.format("Expected an action (instead of a number).%n%s", n.getLocation().toString()));
			case StringKind:
				throw new RuntimeException(String.format("Expected an action (instead of a string).%n%s", n.getLocation().toString()));
			case SubstInKind:
			case AtNodeKind: // @
				throw new RuntimeException(String.format("Expected an action.%n%s", n.getLocation().toString()));
			case LetInKind: // we do not visit the local definitions
				visitExprNode(((LetInNode) n).getBody());
		}
	}

	public void visitUserDefinedNode(OpApplNode n) {
		OpDefNode def = (OpDefNode) n.getOperator();
		if (BBuiltInOPs.contains(def.getName())) {
			addOperation(def.getName().toString(), n, exists, specAnalyser);
			return;
		}

		for (int i = 0; i < def.getParams().length; i++) {
			def.getParams()[i].setToolObject(TranslationGlobals.SUBSTITUTE_PARAM, n.getArgs()[i]);
		}
		// TODO: remember params to omit unneeded in B operation
		currentName = def.getName().toString();
		visitExprNode(def.getBody());
	}

	@Override
	public void visitBuiltInNode(OpApplNode n) {
		UniqueString opname = n.getOperator().getName();
		int opcode = BuiltInOPs.getOpCode(opname);
		DebugUtils.printDebugMsg("OPCODE of " + opname + " = "+ opcode);
		switch (opcode) {
			case OPCODE_dl: // DisjList: split action further
				if (n.getArgs().length == 1) {
					visitExprOrOpArgNode(n.getArgs()[0]);
				} else {
					visitArgs(n);
				}
				return;

			case OPCODE_lor: // logical or: split action further
				visitArgs(n);
				return;

			case OPCODE_be: { // BoundedExists
				exists.add(n);
				visitExprOrOpArgNode(n.getArgs()[0]);
				return;
			}

			// all other action predicates:
			case OPCODE_unchanged: // UNCHANGED
			case OPCODE_eq: // =
			case OPCODE_noteq: // /=, #
			case OPCODE_neg: // Negation
			case OPCODE_lnot: // Negation
			case OPCODE_cl: // $ConjList
			case OPCODE_land: // \land
			case OPCODE_equiv: // \equiv
			case OPCODE_implies: // =>
			case OPCODE_bf: // \A x \in S : P
			case OPCODE_in: // \in
			case OPCODE_notin: // \notin
			case OPCODE_subseteq: // \subseteq - subset or equal
			case OPCODE_fa: // $FcnApply f[1] FIXME: how can FcnApply be an action?
			case OPCODE_ite: // IF THEN ELSE
			case OPCODE_case: // CASE p1 -> e1 [] p2 -> e2
			// TODO case OPCODE_aa: // <<A>>_e
			// TODO case OPCODE_sa: // [A]_e
				// no further decomposing: create a B operation
				addOperation(currentName, n, exists, specAnalyser);
				return;
		}

		if (opname == BBuildIns.OP_false || opname == BBuildIns.OP_true) {
			// FALSE: always disabled; TRUE: CHAOS
			addOperation(currentName, n, exists, specAnalyser);
			return;
		}
		throw new RuntimeException(String.format("Expected an action at '%s':%n%s", opname, n.getLocation()));
	}

	private void visitArgs(OpApplNode n) {
		String oldName = currentName;
		List<OpApplNode> oldExists = new ArrayList<>(exists);

		for (int i = 0; i < n.getArgs().length; i++) {
			exists = new ArrayList<>(oldExists);
			currentName = oldName + i;
			visitExprOrOpArgNode(n.getArgs()[i]);
		}
	}

	private void addOperation(String name, OpApplNode node, List<OpApplNode> exists, SpecAnalyser specAnalyser) {
		if (!generatedOperations.contains(name)) {
			bOperations.add(new BOperation(name, node, exists, specAnalyser));
			generatedOperations.add(name);
			return;
		}
		DebugUtils.printMsg("Duplicate operation not translated: " + name);
		// TODO: handle fixed parameters of an action definition, e.g. Act1(2) /\ Act1(2)
	}

	public List<BOperation> getBOperations() {
		return bOperations;
	}
}
