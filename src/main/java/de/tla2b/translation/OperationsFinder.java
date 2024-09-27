package de.tla2b.translation;

import de.tla2b.analysis.AbstractASTVisitor;
import de.tla2b.analysis.BOperation;
import de.tla2b.analysis.SpecAnalyser;
import de.tla2b.global.BBuildIns;
import de.tla2b.global.BBuiltInOPs;
import de.tla2b.global.TranslationGlobals;
import tla2sany.semantic.*;
import tlc2.tool.BuiltInOPs;
import tlc2.tool.ToolGlobals;
import util.UniqueString;

import java.util.ArrayList;

public class OperationsFinder extends AbstractASTVisitor implements
	ASTConstants, ToolGlobals, TranslationGlobals {
	private final SpecAnalyser specAnalyser;

	private String currentName;
	private ArrayList<OpApplNode> exists;
	// a list containing all existential quantifier which will be parameters in
	// the resulting B Maschine

	private final ArrayList<BOperation> bOperations;

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
			case DecimalKind: {
				throw new RuntimeException(String.format(
					"Expected an action (instead of a number).%n%s", n.getLocation().toString()));
			}
			case StringKind: {
				throw new RuntimeException(String.format(
					"Expected an action (instead of a string).%n%s", n.getLocation().toString()));
			}
			case SubstInKind: {
				throw new RuntimeException(String.format(
					"Expected an action.%n%s", n.getLocation().toString()));
			}
			case AtNodeKind: { // @
				throw new RuntimeException(String.format(
					"Expected an action.%n%s", n.getLocation().toString()));
			}
			case LetInKind: {
				// we do not visit the local definitions
				visitExprNode(((LetInNode) n).getBody());
			}
		}
	}

	public void visitUserDefinedNode(OpApplNode n) {
		OpDefNode def = (OpDefNode) n.getOperator();
		if (BBuiltInOPs.contains(def.getName())) {
			bOperations.add(new BOperation(def.getName().toString(), n, exists, specAnalyser));
			return;
		}

		for (int i = 0; i < def.getParams().length; i++) {
			FormalParamNode param = def.getParams()[i];
			param.setToolObject(SUBSTITUTE_PARAM, n.getArgs()[i]);
		}
		currentName = def.getName().toString();
		visitExprNode(def.getBody());
	}

	@Override
	public void visitBuiltInNode(OpApplNode n) {
		UniqueString opname = n.getOperator().getName();
		int opcode = BuiltInOPs.getOpCode(opname);
		switch (opcode) {
			case OPCODE_dl: // DisjList: split action further
			{
				if (n.getArgs().length == 1) {
					visitExprOrOpArgNode(n.getArgs()[0]);
				} else {
					String oldName = currentName;
					ArrayList<OpApplNode> oldExists = new ArrayList<>(exists);

					for (int i = 0; i < n.getArgs().length; i++) {
						exists = new ArrayList<>(oldExists);
						currentName = oldName + i;
						visitExprOrOpArgNode(n.getArgs()[i]);
					}
				}
				return;
			}
			case OPCODE_lor: { // logical or: split action further
				String oldName = currentName;
				ArrayList<OpApplNode> oldExists = new ArrayList<>(exists);

				for (int i = 0; i < n.getArgs().length; i++) {
					exists = new ArrayList<>(oldExists);
					currentName = oldName + i;
					visitExprOrOpArgNode(n.getArgs()[i]);
				}
				return;
			}
			case OPCODE_be: { // BoundedExists
				exists.add(n);
				visitExprOrOpArgNode(n.getArgs()[0]);
				return;
			}

			case OPCODE_unchanged:
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
			case OPCODE_fa: // $FcnApply f[1]
			case OPCODE_ite: // IF THEN ELSE
			case OPCODE_case: {
				// no further decomposing: create a B operation
				bOperations.add(new BOperation(currentName, n, exists, specAnalyser));
				return;
			}

		}
		//System.out.println("OPCODE of " + opname + " = "+ opcode);

		if (opname == BBuildIns.OP_false ||  // FALSE: always disabled
			opname == BBuildIns.OP_true) {  // TRUE: CHAOS
			bOperations.add(new BOperation(currentName, n, exists, specAnalyser));
			return;
		}
		throw new RuntimeException(String.format(
			"Expected an action at '%s' :%n%s", n.getOperator().getName(), n.getLocation().toString()));

	}

	public ArrayList<BOperation> getBOperations() {
		return bOperations;
	}

}
