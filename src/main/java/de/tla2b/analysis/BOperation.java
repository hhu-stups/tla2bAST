package de.tla2b.analysis;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.be4.classicalb.core.parser.node.*;
import de.be4.classicalb.core.parser.util.ASTBuilder;
import de.tla2b.global.BBuiltInOPs;
import de.tla2b.global.TranslationGlobals;
import de.tla2bAst.BAstCreator;

import tla2sany.semantic.*;

import tlc2.tool.BuiltInOPs;

import static tla2sany.semantic.ASTConstants.*;
import static tlc2.tool.ToolGlobals.*;

public class BOperation {
	private final String name;
	private final OpApplNode node;
	private final List<OpApplNode> existQuans;
	private final List<FormalParamNode> formalParams = new ArrayList<>();
	private final List<OpDeclNode> unchangedVariables = new ArrayList<>();
	private final List<ExprOrOpArgNode> guards = new ArrayList<>();
	private final List<ExprOrOpArgNode> beforeAfterPredicates = new ArrayList<>();
	private final Map<OpDeclNode, ExprOrOpArgNode> assignments = new LinkedHashMap<>();
	private final List<OpDeclNode> anyVariables = new ArrayList<>();

	public BOperation(String name, OpApplNode n, List<OpApplNode> existQuans, SpecAnalyser specAnalyser) {
		this.name = name;
		this.node = n;
		this.existQuans = existQuans;
		OpDeclNode[] variableDecls = specAnalyser.getModuleNode().getVariableDecls();
		this.anyVariables.addAll(Arrays.asList(variableDecls));

		// eval params
		for (OpApplNode ex : existQuans) {
			for (FormalParamNode[] param : ex.getBdedQuantSymbolLists()) { // (bounded exists)
				formalParams.addAll(Arrays.asList(param));
			}
		}
		// DebugUtils.printDebugMsg("Constructing B Operation for TLA+ action: " + name);
		findUnchangedVariablesInSemanticNode(node);
		// System.out.println(" UNCHANGED = " + unchangedVariables.toString());
		separateGuardsAndBeforeAfterPredicates(node);
		findAssignments(variableDecls);
	}

	private static PSubstitution createAssignSubstitution(List<PExpression> lhsAssignment, List<PExpression> rhsAssignment) {
		if (lhsAssignment.isEmpty() && rhsAssignment.isEmpty()) {
			return new ASkipSubstitution();
		} else {
			if (lhsAssignment.size() != rhsAssignment.size()) {
				throw new IllegalArgumentException("Substitution LHS and RHS cannot have different number of elements: " + lhsAssignment.size() + " != " + rhsAssignment.size());
			}
			return new AAssignSubstitution(lhsAssignment, rhsAssignment);
		}
	}

	public AOperation getBOperation(BAstCreator bASTCreator) {
		bASTCreator.setUnchangedVariablesNames(this.getUnchangedVariables());

		List<PPredicate> whereList = new ArrayList<>();
		for (OpApplNode o : this.getExistQuans()) {
			whereList.add(bASTCreator.visitBoundsOfLocalVariables(o));
		}
		for (ExprOrOpArgNode g : guards) {
			whereList.add(bASTCreator.visitExprOrOpArgNodePredicate(g));
		}

		List<PExpression> lhsAssignment = new ArrayList<>();
		List<PExpression> rhsAssignment = new ArrayList<>();
		assignments.forEach((id, assignExpr) -> {
			lhsAssignment.add(bASTCreator.createIdentifierFromNode(id));
			rhsAssignment.add(bASTCreator.visitExprOrOpArgNodeExpression(assignExpr));
		});

		PSubstitution operationBody;
		if (!anyVariables.isEmpty()) { // ANY x_n WHERE P THEN A END
			List<PExpression> anyParams = new ArrayList<>();
			for (OpDeclNode var : anyVariables) {
				AIdentifierExpression nextName = ASTBuilder.createIdentifier(var.getName().toString() + "_n");
				anyParams.add(nextName);
				whereList.add(new AMemberPredicate(nextName.clone(), TypeChecker.getType(var).getBNode()));
				lhsAssignment.add(bASTCreator.createIdentifierFromNode(var));
				rhsAssignment.add(nextName.clone());
			}
			whereList.addAll(createBeforeAfterPredicates(bASTCreator));
			operationBody = new AAnySubstitution(anyParams, ASTBuilder.createConjunction(whereList), createAssignSubstitution(lhsAssignment, rhsAssignment));
		} else if (!whereList.isEmpty()) { // SELECT P THEN A END
			whereList.addAll(createBeforeAfterPredicates(bASTCreator));
			for (ExprOrOpArgNode e : beforeAfterPredicates) {
				whereList.add(bASTCreator.visitExprOrOpArgNodePredicate(e));
			}
			operationBody = new ASelectSubstitution(ASTBuilder.createConjunction(whereList), createAssignSubstitution(lhsAssignment, rhsAssignment), new ArrayList<>(), null);
		} else { // BEGIN A END
			operationBody = createAssignSubstitution(lhsAssignment, rhsAssignment);
		}

		return new AOperation(new LinkedList<>(),
				bASTCreator.createPositionedTIdentifierLiteral(name, getNode()),
				this.getFormalParams().stream().map(bASTCreator::createIdentifierFromNode).collect(Collectors.toList()),
				operationBody
		);
	}

	private List<PPredicate> createBeforeAfterPredicates(BAstCreator bAstCreator) {
		List<PPredicate> predicates = new ArrayList<>();
		for (ExprOrOpArgNode e : beforeAfterPredicates) {
			PPredicate body = null;
			if (e instanceof OpApplNode) {
				OpApplNode opApplNode = (OpApplNode) e;
				if (opApplNode.getOperator().getKind() == UserDefinedOpKind
						&& !BBuiltInOPs.contains(opApplNode.getOperator().getName())) {
					OpDefNode def = (OpDefNode) opApplNode.getOperator();
					FormalParamNode[] params = def.getParams();
					for (int j = 0; j < params.length; j++) {
						params[j].setToolObject(TranslationGlobals.SUBSTITUTE_PARAM, opApplNode.getArgs()[j]);
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

	private void findAssignments(OpDeclNode[] variableDecls) {
		PrimedVariablesFinder primedVariablesFinder = new PrimedVariablesFinder(beforeAfterPredicates);
		for (ExprOrOpArgNode node : new ArrayList<>(beforeAfterPredicates)) {
			if (node instanceof OpApplNode) {
				OpApplNode opApplNode = (OpApplNode) node;
				if (opApplNode.getOperator().getKind() == BuiltInKind
						&& BuiltInOPs.getOpCode(opApplNode.getOperator().getName()) == OPCODE_eq) {
					ExprOrOpArgNode arg1 = opApplNode.getArgs()[0]; // we have equality arg1 = RHS
					try {
						OpApplNode primeAppl = (OpApplNode) arg1;
						if (BuiltInOPs.getOpCode(primeAppl.getOperator().getName()) == OPCODE_prime) {
							OpDeclNode var = (OpDeclNode) ((OpApplNode) primeAppl.getArgs()[0]).getOperator(); // var is first arg of prime
							// we have equality var' = RHS
							if (!primedVariablesFinder.getTwiceUsedVariables().contains(var)) {
								// var' is only used once in all before after predicates
								// meaning we do not need it as parameter of the ANY
								// and can add an assignment var := RHS
								assignments.put(var, opApplNode.getArgs()[1]); // RHS of assignment
								beforeAfterPredicates.remove(node);
								// System.out.println("Detected assignment " + var.getName().toString() + "' = <RHS>");
							}
						}
					} catch (ClassCastException e) {
					}
				}
			}
		}
		anyVariables.clear();
		Collections.addAll(anyVariables, variableDecls);

		// for (SymbolNode symbol : primedVariablesFinder.getAllVariables()) {
		// anyVariables.add((OpDeclNode) symbol);
		// }
		anyVariables.removeAll(assignments.keySet());
		anyVariables.removeAll(unchangedVariables);
	}

	private void separateGuardsAndBeforeAfterPredicates(ExprOrOpArgNode node) {
		if (node instanceof OpApplNode) {
			OpApplNode opApplNode = (OpApplNode) node;
			if (opApplNode.getOperator().getKind() == BuiltInKind) {
				switch (BuiltInOPs.getOpCode(opApplNode.getOperator().getName())) {
					case OPCODE_land: // \land (getArgs has 2 args)
					case OPCODE_cl: // $ConjList
						Arrays.stream(opApplNode.getArgs()).forEach(this::separateGuardsAndBeforeAfterPredicates);
						return;
					default:
						(opApplNode.level < 2 ? guards : beforeAfterPredicates).add(node);
						// guards: should we check if nonLeibnizParams is empty?
						return;
				}
			}
		}
		(node.level < 2 ? guards : beforeAfterPredicates).add(node); // level = 2 means action predicate
	}

	private void findUnchangedVariablesInSemanticNode(SemanticNode node) {
		switch (node.getKind()) {
			case OpApplKind:
				findUnchangedVariablesInOpApplNode((OpApplNode) node);
				return;
			case LetInKind:
				findUnchangedVariablesInSemanticNode(((LetInNode) node).getBody());
				return;
			case SubstInKind:
				findUnchangedVariablesInSemanticNode(((SubstInNode) node).getBody());
		}
	}

	private void findUnchangedVariablesInOpApplNode(OpApplNode n) {
		int kind = n.getOperator().getKind();
		if (kind == UserDefinedOpKind && !BBuiltInOPs.contains(n.getOperator().getName())) {
			findUnchangedVariablesInSemanticNode(((OpDefNode) n.getOperator()).getBody());
		} else if (kind == BuiltInKind) {
			switch (BuiltInOPs.getOpCode(n.getOperator().getName())) {
				case OPCODE_land: // \land
				case OPCODE_cl: // $ConjList
					Arrays.stream(n.getArgs()).forEach(this::findUnchangedVariablesInSemanticNode);
					return;
				case OPCODE_unchanged: {
					// n.setToolObject(USED, false); FIXME: this tool object is never used?
					OpApplNode k = (OpApplNode) n.getArgs()[0];
					if (k.getOperator().getKind() == VariableDeclKind) {
						unchangedVariables.add((OpDeclNode) k.getOperator());
					} else {
						// Tuple
						for (int i = 0; i < k.getArgs().length; i++) {
							OpApplNode var = (OpApplNode) k.getArgs()[i];
							//findUnchangedVariablesInOpApplNode(var);
							// System.out.println("var.getOperator() = " + var.getOperator().getName() + " at " + var.getOperator() + " of class " + var.getOperator().getClass().getSimpleName());
							if (var.getOperator() instanceof OpDefNode) {
								// we have a definition
								OpDefNode def = (OpDefNode) var.getOperator();
								if (def.getParams().length > 0) {
									// TODO: we do not support definitions with arguments yet
									throw new RuntimeException("Declaration with parameters not supported for UNCHANGED: " + var.getOperator().getName() + " " + var.getLocation());
								}
								ExprNode body = def.getBody();
								// System.out.println("Body = " + body + " of class " + body.getClass().getSimpleName());
								if (body instanceof OpApplNode) {
									OpApplNode obody = (OpApplNode) body;
									// System.out.println("Operator = " + obody.getOperator()); // In module --TLA+ BUILTINS--
									findUnchangedVariablesInOpApplNode(obody);
								}
							} else if (!(var.getOperator() instanceof OpDeclNode)) {
								throw new RuntimeException("Cannot convert to list of UNCHANGED variables: " + var.getOperator().getName() + " " + var.getLocation());
							} else {
								unchangedVariables.add((OpDeclNode) var.getOperator());
							}
						}
					}
				}
			}
		}
	}

	public SymbolNode getSymbolNode() {
		if (node != null && node.getOperator().getKind() == UserDefinedOpKind) {
			return node.getOperator();
		}
		return null;
	}

	public String getName() {
		return name;
	}

	public ExprNode getNode() {
		return node;
	}

	public List<OpApplNode> getExistQuans() {
		return new ArrayList<>(existQuans);
	}

	public List<String> getOpParams() {
		return formalParams.stream().map(f -> f.getName().toString()).collect(Collectors.toList());
	}

	public List<FormalParamNode> getFormalParams() {
		return formalParams;
	}

	public List<String> getUnchangedVariables() {
		return unchangedVariables.stream().map(u -> u.getName().toString()).collect(Collectors.toList());
	}
}

class PrimedVariablesFinder extends AbstractASTVisitor {
	private final Set<SymbolNode> all;
	private final Set<SymbolNode> twiceUsedVariables;

	public PrimedVariablesFinder(List<ExprOrOpArgNode> list) {
		this.all = new HashSet<>();
		this.twiceUsedVariables = new HashSet<>();
		list.forEach(this::visitExprOrOpArgNode); // findPrimedVariables
	}

	public void visitBuiltInNode(OpApplNode n) {
		if (BuiltInOPs.getOpCode(n.getOperator().getName()) == OPCODE_prime && n.getArgs()[0] instanceof OpApplNode) {
			SymbolNode var = ((OpApplNode) n.getArgs()[0]).getOperator();
			if (!all.add(var)) {
				twiceUsedVariables.add(var);
			}
		}
		super.visitBuiltInNode(n);
	}

	public Set<SymbolNode> getTwiceUsedVariables() {
		return this.twiceUsedVariables;
	}

	public Set<SymbolNode> getAllVariables() {
		return this.all;
	}
}
