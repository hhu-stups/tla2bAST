package de.tla2b.analysis;

import de.be4.classicalb.core.parser.node.*;
import de.tla2b.global.BBuiltInOPs;
import de.tla2b.global.TranslationGlobals;
import de.tla2b.types.TLAType;
import de.tla2bAst.BAstCreator;
import tla2sany.semantic.*;
import tlc2.tool.BuiltInOPs;
import tlc2.tool.ToolGlobals;

import java.util.*;
import java.util.Map.Entry;
import java.util.stream.Collectors;

public class BOperation extends BuiltInOPs implements ASTConstants, ToolGlobals, TranslationGlobals {
	private final String name;
	private final OpApplNode node;
	private final List<OpApplNode> existQuans;
	private List<String> opParams;
	private List<FormalParamNode> formalParams;
	private List<String> unchangedVariables;
	private final List<OpDeclNode> unchangedVariablesList;
	private final List<ExprOrOpArgNode> guards;
	private final List<ExprOrOpArgNode> beforeAfterPredicates;
	private final LinkedHashMap<SymbolNode, ExprOrOpArgNode> assignments = new LinkedHashMap<>();
	private List<OpDeclNode> anyVariables;
	private final SpecAnalyser specAnalyser;

	public BOperation(String name, OpApplNode n, List<OpApplNode> existQuans, SpecAnalyser specAnalyser) {
		this.name = name;
		this.node = n;
		this.existQuans = existQuans;
		this.specAnalyser = specAnalyser;
		this.unchangedVariablesList = new ArrayList<>();
		this.guards = new ArrayList<>();
		this.beforeAfterPredicates = new ArrayList<>();
		anyVariables = new ArrayList<>(Arrays.asList(specAnalyser.getModuleNode().getVariableDecls()));

		evalParams();
		// System.out.println("Construction B Operation for TLA+ action: " + name);
		findUnchangedVariables();
		// System.out.println(" UNCHANGED = " + unchangedVariables.toString());
		separateGuardsAndBeforeAfterPredicates(node);
		findAssignments();
	}

	public AOperation getBOperation(BAstCreator bASTCreator) {
		bASTCreator.setUnchangedVariablesNames(unchangedVariables);
		List<PPredicate> whereList = new ArrayList<>();
		for (OpApplNode o : this.getExistQuans()) {
			whereList.add(bASTCreator.visitBoundsOfLocalVariables(o));
		}

		for (ExprOrOpArgNode g : guards) {
			whereList.add(bASTCreator.visitExprOrOpArgNodePredicate(g));
		}

		List<PExpression> leftSideOfAssigment = new ArrayList<>();
		List<PExpression> rightSideOfAssigment = new ArrayList<>();
		for (Entry<SymbolNode, ExprOrOpArgNode> entry : assignments.entrySet()) {
			leftSideOfAssigment.add(bASTCreator.createIdentifierNode(entry.getKey()));
			rightSideOfAssigment.add(bASTCreator.visitExprOrOpArgNodeExpression(entry.getValue()));
		}
		PSubstitution operationBody;
		AAssignSubstitution assign = new AAssignSubstitution();
		if (!anyVariables.isEmpty()) { // ANY x_n WHERE P THEN A END
			List<PExpression> anyParams = new ArrayList<>();
			for (OpDeclNode var : anyVariables) {
				String nextName = var.getName().toString() + "_n";
				anyParams.add(BAstCreator.createIdentifierNode(nextName));

				whereList.add(new AMemberPredicate(
						BAstCreator.createIdentifierNode(nextName),
						((TLAType) var.getToolObject(TYPE_ID)).getBNode()
				));
				leftSideOfAssigment.add(bASTCreator.createIdentifierNode(var));
				rightSideOfAssigment.add(BAstCreator.createIdentifierNode(nextName));
			}
			whereList.addAll(createBeforeAfterPredicates(bASTCreator));
			operationBody = new AAnySubstitution(anyParams, bASTCreator.createConjunction(whereList), assign);
		} else if (!whereList.isEmpty()) { // SELECT P THEN A END
			whereList.addAll(createBeforeAfterPredicates(bASTCreator));
			for (ExprOrOpArgNode e : beforeAfterPredicates) {
				whereList.add(bASTCreator.visitExprOrOpArgNodePredicate(e));
			}
			operationBody = new ASelectSubstitution(bASTCreator.createConjunction(whereList), assign, new ArrayList<>(), null);
		} else { // BEGIN A END
			operationBody = new ABlockSubstitution(assign);
		}

		if (!leftSideOfAssigment.isEmpty()) {
			assign.setLhsExpression(leftSideOfAssigment);
			assign.setRhsExpressions(rightSideOfAssigment);
		} else { // skip
			assign.replaceBy(new ASkipSubstitution());
		}

		return new AOperation(
				new ArrayList<>(),
				BAstCreator.createTIdentifierLiteral(name),
				this.getFormalParams().stream().map(bASTCreator::createIdentifierNode).collect(Collectors.toList()),
				operationBody
		);
	}

	private ArrayList<PPredicate> createBeforeAfterPredicates(BAstCreator bAstCreator) {
		ArrayList<PPredicate> predicates = new ArrayList<>();
		for (ExprOrOpArgNode e : beforeAfterPredicates) {
			PPredicate body = null;
			if (e instanceof OpApplNode) {
				OpApplNode opApplNode = (OpApplNode) e;
				if (opApplNode.getOperator().getKind() == UserDefinedOpKind
					&& !BBuiltInOPs.contains(opApplNode.getOperator().getName())) {
					OpDefNode def = (OpDefNode) opApplNode.getOperator();
					FormalParamNode[] params = def.getParams();
					for (int j = 0; j < params.length; j++) {
						FormalParamNode param = params[j];
						param.setToolObject(SUBSTITUTE_PARAM, opApplNode.getArgs()[j]);
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
		PrimedVariablesFinder primedVariablesFinder = new PrimedVariablesFinder(beforeAfterPredicates);
		for (ExprOrOpArgNode node : new ArrayList<>(beforeAfterPredicates)) {
			if (node instanceof OpApplNode) {
				OpApplNode opApplNode = (OpApplNode) node;
				if (opApplNode.getOperator().getKind() == BuiltInKind) {

					if (OPCODE_eq == getOpCode(opApplNode.getOperator().getName())) {
						ExprOrOpArgNode arg1 = opApplNode.getArgs()[0]; // we have equality arg1 = RHS
						try {
							OpApplNode arg11 = (OpApplNode) arg1;
							if (getOpCode(arg11.getOperator().getName()) == OPCODE_prime) {
								OpApplNode v = (OpApplNode) arg11.getArgs()[0];
								SymbolNode var = v.getOperator();
								// we have equality var' = RHS
								if (!primedVariablesFinder.getTwiceUsedVariables().contains(var)) {
									// var' is only used once in all before after predicates
									// meaning we do not need it as parameter of the ANY
									// and can add an assignment var := RHS
									assignments.put(v.getOperator(), opApplNode.getArgs()[1]); // RHS of assignment
									beforeAfterPredicates.remove(node);
									// System.out.println("Detected assignment " + var.getName().toString() + "' = <RHS>");
								}
							}
						} catch (ClassCastException e) {
						}
					}

				}
			}
		}
		anyVariables = new ArrayList<>();
		Collections.addAll(anyVariables, specAnalyser.getModuleNode().getVariableDecls());

		// for (SymbolNode symbol : primedVariablesFinder.getAllVariables()) {
		// anyVariables.add((OpDeclNode) symbol);
		// }
		anyVariables.removeAll(assignments.keySet());
		anyVariables.removeAll(unchangedVariablesList);
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
							guards.add(node); // should we be checking nonLeibnizParams is empty ?
						} else {
							beforeAfterPredicates.add(node);
						}
						return;
					}

				}
			}
		}
		if (node.level < 2) {
			guards.add(node);
		} else {
			beforeAfterPredicates.add(node);
		}
		// beforeAfterPredicates.add(node);
	}

	private void evalParams() {
		opParams = new ArrayList<>();
		formalParams = new ArrayList<>();
		for (OpApplNode n : existQuans) {
			FormalParamNode[][] params = n.getBdedQuantSymbolLists();
			for (FormalParamNode[] param : params) {
				for (FormalParamNode formalParamNode : param) {
					formalParams.add(formalParamNode);
					opParams.add(formalParamNode.getName().toString());
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
		return opParams;
	}

	public List<FormalParamNode> getFormalParams() {
		return formalParams;
	}

	public List<String> getUnchangedVariables() {
		return unchangedVariables;
	}

	private void findUnchangedVariables() {
		unchangedVariables = new ArrayList<>();
		findUnchangedVariablesInSemanticNode(node);
	}

	private void findUnchangedVariablesInSemanticNode(SemanticNode node) {
		switch (node.getKind()) {
			case OpApplKind: {
				findUnchangedVariablesInOpApplNode((OpApplNode) node);
				return;
			}
			case LetInKind: {
				LetInNode letNode = (LetInNode) node;
				findUnchangedVariablesInSemanticNode(letNode.getBody());
				return;
			}

			case SubstInKind: {
				SubstInNode substInNode = (SubstInNode) node;
				findUnchangedVariablesInSemanticNode(substInNode.getBody());
			}
		}
	}

	private void findUnchangedVariablesInOpApplNode(OpApplNode n) {

		int kind = n.getOperator().getKind();
		if (kind == UserDefinedOpKind && !BBuiltInOPs.contains(n.getOperator().getName())) {
			OpDefNode def = (OpDefNode) n.getOperator();
			findUnchangedVariablesInSemanticNode(def.getBody());
		} else if (kind == BuiltInKind) {
			int opcode = BuiltInOPs.getOpCode(n.getOperator().getName());
			switch (opcode) {
				case OPCODE_land: // \land
				case OPCODE_cl: { // $ConjList
					for (int i = 0; i < n.getArgs().length; i++) {
						findUnchangedVariablesInSemanticNode(n.getArgs()[i]);
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
							//findUnchangedVariablesInOpApplNode(var);
							// System.out.println("var.getOperator() = " + var.getOperator().getName() + " at " + var.getOperator() + " of class " + var.getOperator().getClass().getSimpleName());
							if (var.getOperator() instanceof OpDefNode) {
								// we have a definition
								OpDefNode def = (OpDefNode) var.getOperator();
								if (def.getParams().length > 0) {
									// we do not support definitions with arguments yet
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
								unchangedVariablesList.add((OpDeclNode) var.getOperator());
								String name = var.getOperator().getName().toString();
								unchangedVariables.add(name);
							}
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

	public PrimedVariablesFinder(List<ExprOrOpArgNode> list) {
		this.all = new HashSet<>();
		this.twiceUsedVariables = new HashSet<>();
		this.table = new Hashtable<>();

		for (ExprOrOpArgNode exprOrOpArgNode : list) {
			findPrimedVariables(exprOrOpArgNode);
		}
	}

	public void findPrimedVariables(ExprOrOpArgNode n) {
		currentSet = new HashSet<>();
		this.visitExprOrOpArgNode(n);
		table.put(n, currentSet);
	}

	public void visitBuiltInNode(OpApplNode n) {
		if (getOpCode(n.getOperator().getName()) == OPCODE_prime) { // prime
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
		super.visitBuiltInNode(n);
	}

	public Set<SymbolNode> getTwiceUsedVariables() {
		return this.twiceUsedVariables;
	}

	public Set<SymbolNode> getAllVariables() {
		return this.all;
	}
}
