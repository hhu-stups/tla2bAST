/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package de.tla2b.analysis;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.Hashtable;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map.Entry;
import java.util.Set;

import de.be4.classicalb.core.parser.node.AAnySubstitution;
import de.be4.classicalb.core.parser.node.AAssignSubstitution;
import de.be4.classicalb.core.parser.node.ABlockSubstitution;
import de.be4.classicalb.core.parser.node.AMemberPredicate;
import de.be4.classicalb.core.parser.node.AOperation;
import de.be4.classicalb.core.parser.node.ASelectSubstitution;
import de.be4.classicalb.core.parser.node.ASkipSubstitution;
import de.be4.classicalb.core.parser.node.PExpression;
import de.be4.classicalb.core.parser.node.PPredicate;
import de.tla2b.global.BBuiltInOPs;
import de.tla2b.global.TranslationGlobals;
import de.tla2b.types.TLAType;
import de.tla2bAst.BAstCreator;
import tla2sany.semantic.ASTConstants;
import tla2sany.semantic.ExprNode;
import tla2sany.semantic.ExprOrOpArgNode;
import tla2sany.semantic.FormalParamNode;
import tla2sany.semantic.LetInNode;
import tla2sany.semantic.OpApplNode;
import tla2sany.semantic.OpDeclNode;
import tla2sany.semantic.OpDefNode;
import tla2sany.semantic.SemanticNode;
import tla2sany.semantic.SubstInNode;
import tla2sany.semantic.SymbolNode;
import tlc2.tool.BuiltInOPs;
import tlc2.tool.ToolGlobals;

public class BOperation extends BuiltInOPs implements ASTConstants,
		ToolGlobals, TranslationGlobals {
	private final String name;
	private final ExprNode node;
	private final ArrayList<OpApplNode> existQuans;
	private ArrayList<String> opParams;
	private ArrayList<FormalParamNode> formalParams;
	private ArrayList<String> unchangedVariables;
	private final ArrayList<OpDeclNode> unchangedVariablesList;
	private final ArrayList<ExprOrOpArgNode> guards;
	private final ArrayList<ExprOrOpArgNode> beforeAfterPredicates;
	private LinkedHashMap<SymbolNode, ExprOrOpArgNode> assignments = new LinkedHashMap<SymbolNode, ExprOrOpArgNode>();
	private List<OpDeclNode> anyVariables;
	private final SpecAnalyser specAnalyser;

	public BOperation(String name, ExprNode n,
			ArrayList<OpApplNode> existQuans, SpecAnalyser specAnalyser) {
		this.name = name;
		this.node = n;
		this.existQuans = existQuans;
		this.specAnalyser = specAnalyser;
		this.unchangedVariablesList = new ArrayList<OpDeclNode>();
		this.guards = new ArrayList<ExprOrOpArgNode>();
		this.beforeAfterPredicates = new ArrayList<ExprOrOpArgNode>();
		anyVariables = new ArrayList<OpDeclNode>(Arrays.asList(specAnalyser
				.getModuleNode().getVariableDecls()));

		evalParams();
		findUnchangedVariables();
		separateGuardsAndBeforeAfterPredicates(node);
		findAssignments();
	}

	public AOperation getBOperation(BAstCreator bASTCreator) {
		AOperation operation = new AOperation();
		List<PExpression> paramList = new ArrayList<PExpression>();
		ArrayList<PPredicate> whereList = new ArrayList<PPredicate>();
		for (int j = 0; j < this.getFormalParams().size(); j++) {
			paramList.add(bASTCreator.createIdentifierNode(this
					.getFormalParams().get(j)));
		}
		for (int j = 0; j < this.getExistQuans().size(); j++) {
			OpApplNode o = this.getExistQuans().get(j);
			whereList.add(bASTCreator.visitBounded(o));
		}

		operation.setOpName(BAstCreator.createTIdentifierLiteral(name));
		operation.setParameters(paramList);
		operation.setReturnValues(new ArrayList<PExpression>());

		for (ExprOrOpArgNode g : guards) {
			whereList.add(bASTCreator.visitExprOrOpArgNodePredicate(g));
		}

		ArrayList<PExpression> left = new ArrayList<PExpression>();
		ArrayList<PExpression> right = new ArrayList<PExpression>();
		for (Entry<SymbolNode, ExprOrOpArgNode> entry : assignments.entrySet()) {
			left.add(bASTCreator.createIdentifierNode(entry.getKey()));
			right.add(bASTCreator.visitExprOrOpArgNodeExpression(entry
					.getValue()));
		}
		AAssignSubstitution assign = new AAssignSubstitution();

		if (anyVariables.size() > 0) { // ANY x_n WHERE P THEN A END
			AAnySubstitution any = new AAnySubstitution();
			any = new AAnySubstitution();
			List<PExpression> anyParams = new ArrayList<PExpression>();
			for (OpDeclNode var : anyVariables) {
				String varName = var.getName().toString();
				String nextName = varName + "_n";
				anyParams.add(BAstCreator.createIdentifierNode(nextName));

				AMemberPredicate member = new AMemberPredicate();
				member.setLeft(BAstCreator.createIdentifierNode(nextName));
				TLAType t = (TLAType) var.getToolObject(TYPE_ID);
				member.setRight(t.getBNode());
				whereList.add(member);
				left.add(bASTCreator.createIdentifierNode(var));
				right.add(BAstCreator.createIdentifierNode(nextName));
			}
			any.setIdentifiers(anyParams);
			whereList.addAll(createBeforeAfterPredicates(bASTCreator));
			any.setWhere(bASTCreator.createConjunction(whereList));
			any.setThen(assign);
			operation.setOperationBody(any);
		} else if (whereList.size() > 0) { // SELECT P THEN A END
			ASelectSubstitution select = new ASelectSubstitution();
			whereList.addAll(createBeforeAfterPredicates(bASTCreator));
			for (ExprOrOpArgNode e : beforeAfterPredicates) {
				whereList.add(bASTCreator.visitExprOrOpArgNodePredicate(e));
			}
			select.setCondition(bASTCreator.createConjunction(whereList));
			select.setThen(assign);
			operation.setOperationBody(select);
		} else { // BEGIN A END
			ABlockSubstitution block = new ABlockSubstitution(assign);
			operation.setOperationBody(block);
		}

		if (left.size() > 0) {
			assign.setLhsExpression(left);
			assign.setRhsExpressions(right);
		} else { // skip
			assign.replaceBy(new ASkipSubstitution());
		}

		return operation;
	}

	private ArrayList<PPredicate> createBeforeAfterPredicates(
			BAstCreator bAstCreator) {
		ArrayList<PPredicate> predicates = new ArrayList<PPredicate>();
		for (ExprOrOpArgNode e : beforeAfterPredicates) {
			PPredicate body = null;
			if (e instanceof OpApplNode) {
				OpApplNode opApplNode = (OpApplNode) e;
				if (opApplNode.getOperator().getKind() == UserDefinedOpKind
						&& !BBuiltInOPs.contains(opApplNode.getOperator()
								.getName())) {
					OpDefNode def = (OpDefNode) opApplNode.getOperator();
					FormalParamNode[] params = def.getParams();
					for (int j = 0; j < params.length; j++) {
						FormalParamNode param = params[j];
						param.setToolObject(SUBSTITUTE_PARAM,
								opApplNode.getArgs()[j]);
					}
					body = bAstCreator.visitExprNodePredicate(def.getBody());
				}
			}
			if (body == null) {
				body = bAstCreator.visitExprOrOpArgNodePredicate(e);
			}
			predicates.add(body);
		}
		return predicates;
	}

	private void findAssignments() {
		PrimedVariablesFinder primedVariablesFinder = new PrimedVariablesFinder(
				beforeAfterPredicates);
		for (ExprOrOpArgNode node : new ArrayList<ExprOrOpArgNode>(
				beforeAfterPredicates)) {
			if (node instanceof OpApplNode) {
				OpApplNode opApplNode = (OpApplNode) node;
				if (opApplNode.getOperator().getKind() == BuiltInKind) {
					switch (getOpCode(opApplNode.getOperator().getName())) {
					case OPCODE_eq: {
						ExprOrOpArgNode arg1 = opApplNode.getArgs()[0];
						try {
							OpApplNode arg11 = (OpApplNode) arg1;
							if (getOpCode(arg11.getOperator().getName()) == OPCODE_prime) {
								OpApplNode v = (OpApplNode) arg11.getArgs()[0];
								SymbolNode var = v.getOperator();
								if (!primedVariablesFinder
										.getTwiceUsedVariables().contains(var)) {
									// var is only used once in all before after
									// predicates
									assignments.put(v.getOperator(),
											opApplNode.getArgs()[1]);
									beforeAfterPredicates.remove(node);
								}

							}
						} catch (ClassCastException e) {

						}

					}
					default:
					}
				}
			}
		}
		anyVariables = new ArrayList<OpDeclNode>();
		for (OpDeclNode var : specAnalyser.getModuleNode().getVariableDecls()) {
			anyVariables.add(var);
		}

		// for (SymbolNode symbol : primedVariablesFinder.getAllVariables()) {
		// anyVariables.add((OpDeclNode) symbol);
		// }
		anyVariables.removeAll(assignments.keySet());
	}

	private void separateGuardsAndBeforeAfterPredicates(ExprOrOpArgNode node) {
		if (node instanceof OpApplNode) {
			OpApplNode opApplNode = (OpApplNode) node;
			if (opApplNode.getOperator().getKind() == BuiltInKind) {
				switch (getOpCode(opApplNode.getOperator().getName())) {
				case OPCODE_land: // \land
				{
					separateGuardsAndBeforeAfterPredicates(opApplNode.getArgs()[0]);
					separateGuardsAndBeforeAfterPredicates(opApplNode.getArgs()[1]);
					return;
				}
				case OPCODE_cl: // $ConjList
				{
					for (int i = 0; i < opApplNode.getArgs().length; i++) {
						separateGuardsAndBeforeAfterPredicates(opApplNode
								.getArgs()[i]);
					}
					return;
				}
				default: {
					if (opApplNode.level < 2) {
						guards.add(node);
						return;
					} else {
						beforeAfterPredicates.add(node);
						return;
					}
				}

				}
			}
		}
		if (node.level < 2) {
			guards.add(node);
			return;
		} else {
			beforeAfterPredicates.add(node);
			return;
		}
		//beforeAfterPredicates.add(node);
	}

	private void evalParams() {
		opParams = new ArrayList<String>();
		formalParams = new ArrayList<FormalParamNode>();
		for (int i = 0; i < existQuans.size(); i++) {
			OpApplNode n = existQuans.get(i);
			FormalParamNode[][] params = n.getBdedQuantSymbolLists();
			for (int k = 0; k < params.length; k++) {
				for (int j = 0; j < params[k].length; j++) {
					formalParams.add(params[k][j]);
					opParams.add(params[k][j].getName().toString());
				}
			}
		}
	}

	public SymbolNode getSymbolNode() {
		if (node instanceof OpApplNode) {
			OpApplNode n = ((OpApplNode) node);
			if (n.getOperator().getKind() == UserDefinedOpKind) {
				return ((OpApplNode) node).getOperator();
			}
		}
		return null;
	}

	public String getName() {
		return name;
	}

	public ExprNode getNode() {
		return node;
	}

	public ArrayList<OpApplNode> getExistQuans() {
		return new ArrayList<OpApplNode>(existQuans);
	}

	public ArrayList<String> getOpParams() {
		return opParams;
	}

	public ArrayList<FormalParamNode> getFormalParams() {
		return formalParams;
	}

	public ArrayList<String> getUnchangedVariables() {
		return unchangedVariables;
	}

	private void findUnchangedVariables() {
		unchangedVariables = new ArrayList<String>();
		findUnchangedVaribalesInSemanticNode(node);
	}

	/**
	 * @param node2
	 */
	private void findUnchangedVaribalesInSemanticNode(SemanticNode node) {
		switch (node.getKind()) {
		case OpApplKind: {
			findUnchangedVariablesInOpApplNode((OpApplNode) node);
			return;
		}
		case LetInKind: {
			LetInNode letNode = (LetInNode) node;
			findUnchangedVaribalesInSemanticNode(letNode.getBody());
			return;
		}

		case SubstInKind: {
			SubstInNode substInNode = (SubstInNode) node;
			findUnchangedVaribalesInSemanticNode(substInNode.getBody());
			return;
		}
		}
	}

	/**
	 * @param node2
	 */
	private void findUnchangedVariablesInOpApplNode(OpApplNode n) {

		int kind = n.getOperator().getKind();
		if (kind == UserDefinedOpKind
				&& !BBuiltInOPs.contains(n.getOperator().getName())) {
			OpDefNode def = (OpDefNode) n.getOperator();
			findUnchangedVaribalesInSemanticNode(def.getBody());
			return;
		} else if (kind == BuiltInKind) {
			int opcode = BuiltInOPs.getOpCode(n.getOperator().getName());
			switch (opcode) {
			case OPCODE_land: // \land
			case OPCODE_cl: { // $ConjList
				for (int i = 0; i < n.getArgs().length; i++) {
					findUnchangedVaribalesInSemanticNode(n.getArgs()[i]);
				}
				return;
			}
			case OPCODE_unchanged: {
				n.setToolObject(USED, false);
				OpApplNode k = (OpApplNode) n.getArgs()[0];
				if (k.getOperator().getKind() == VariableDeclKind) {
					unchangedVariablesList.add((OpDeclNode) k.getOperator());
					String name = k.getOperator().getName().toString();
					unchangedVariables.add(name);
				} else {
					// Tuple
					for (int i = 0; i < k.getArgs().length; i++) {
						OpApplNode var = (OpApplNode) k.getArgs()[i];
						unchangedVariablesList.add((OpDeclNode) var
								.getOperator());
						String name = var.getOperator().getName().toString();
						unchangedVariables.add(name);
					}
				}
			}

			}
		}
	}

}

class PrimedVariablesFinder extends AbstractASTVisitor {
	private final Set<SymbolNode> all;
	private final Set<SymbolNode> twiceUsedVariables;
	private final Hashtable<SemanticNode, Set<SymbolNode>> table;
	private Set<SymbolNode> currentSet;

	public PrimedVariablesFinder(ArrayList<ExprOrOpArgNode> list) {
		this.all = new HashSet<SymbolNode>();
		this.twiceUsedVariables = new HashSet<SymbolNode>();
		this.table = new Hashtable<SemanticNode, Set<SymbolNode>>();

		for (ExprOrOpArgNode exprOrOpArgNode : list) {
			findPrimedVariables(exprOrOpArgNode);
		}
	}

	public void findPrimedVariables(ExprOrOpArgNode n) {
		currentSet = new HashSet<SymbolNode>();
		this.visitExprOrOpArgNode(n);
		table.put(n, currentSet);
	}

	public void visitBuiltInNode(OpApplNode n) {
		switch (getOpCode(n.getOperator().getName())) {

		case OPCODE_prime: // prime
		{
			if (n.getArgs()[0] instanceof OpApplNode) {
				OpApplNode varNode = (OpApplNode) n.getArgs()[0];
				SymbolNode var = varNode.getOperator();

				currentSet.add(var);

				if (all.contains(var)) {
					twiceUsedVariables.add(var);
				} else {
					all.add(var);
				}
			}
		}

		default: {
			super.visitBuiltInNode(n);
		}

		}
	}

	public Set<SymbolNode> getTwiceUsedVariables() {
		return this.twiceUsedVariables;
	}

	public Set<SymbolNode> getAllVariables() {
		return this.all;
	}
}
