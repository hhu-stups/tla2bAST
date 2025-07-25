package de.tla2bAst;

import de.be4.classicalb.core.parser.Definitions;
import de.be4.classicalb.core.parser.IDefinitions;
import de.be4.classicalb.core.parser.analysis.prolog.NodeFileNumbers;
import de.be4.classicalb.core.parser.node.*;
import de.be4.classicalb.core.parser.util.ASTBuilder;
import de.hhu.stups.sablecc.patch.PositionedNode;
import de.hhu.stups.sablecc.patch.SourcePosition;
import de.tla2b.analysis.*;
import de.tla2b.analysis.PredicateVsExpression.DefinitionType;
import de.tla2b.config.ConfigfileEvaluator;
import de.tla2b.config.TLCValueNode;
import de.tla2b.exceptions.NotImplementedException;
import de.tla2b.global.*;
import de.tla2b.translation.BMacroHandler;
import de.tla2b.translation.RecursiveFunctionHandler;
import de.tla2b.types.*;
import de.tla2b.util.DebugUtils;
import tla2sany.semantic.*;
import tla2sany.st.Location;
import tlc2.tool.BuiltInOPs;
import tlc2.value.ValueConstants;
import tlc2.value.impl.*;

import java.util.*;
import java.util.Map.Entry;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import static de.be4.classicalb.core.parser.util.ASTBuilder.*;
import static de.tla2b.analysis.TypeChecker.getType;

public class BAstCreator extends BuiltInOPs implements TranslationGlobals, BBuildIns, ValueConstants {

	private List<PMachineClause> machineClauseList;
	private ConfigfileEvaluator conEval;
	private final SpecAnalyser specAnalyser;
	private final PredicateVsExpression predicateVsExpression;
	private final BMacroHandler bMacroHandler;
	private final RecursiveFunctionHandler recursiveFunctionHandler;

	private List<OpDeclNode> bConstants;

	private final ModuleNode moduleNode;

	private final IDefinitions bDefinitions;

	private final Start start;
	private final Map<Node, TLAType> types = new HashMap<>();
	private final Set<PositionedNode> sourcePosition = new HashSet<>();
	private final NodeFileNumbers nodeFileNumbers = new NodeFileNumbers();
	private final List<String> filesOrderedById = new ArrayList<>();
	private List<String> toplevelUnchangedVariableNames = new ArrayList<>();

	/**
	 * Creates a B AST node for a TLA expression
	 */
	public BAstCreator(ModuleNode moduleNode, SpecAnalyser specAnalyser) {
		this.moduleNode = moduleNode;
		this.specAnalyser = specAnalyser;
		this.bDefinitions = new Definitions();
		this.bMacroHandler = new BMacroHandler();
		this.predicateVsExpression = new PredicateVsExpression(moduleNode);
		this.recursiveFunctionHandler = new RecursiveFunctionHandler(specAnalyser);

		ExprNode expr = moduleNode.getOpDefs()[moduleNode.getOpDefs().length - 1].getBody();
		if (expressionIsAPredicate(expr)) {
			start = new Start(new APredicateParseUnit(visitExprNodePredicate(expr)), new EOF());
		} else {
			start = new Start(new AExpressionParseUnit(visitExprNodeExpression(expr)), new EOF());
		}
	}

	private boolean expressionIsAPredicate(ExprNode expr) {
		if (expr.getKind() == OpApplKind) {
			OpApplNode opApplNode = (OpApplNode) expr;
			int kind = opApplNode.getOperator().getKind();
			if (kind == BuiltInKind) {
				int opcode = getOpCode(opApplNode.getOperator().getName());
				return OperatorTypes.tlaOperatorIsPredicate(opcode);
			} else if (kind == UserDefinedOpKind && BBuiltInOPs.contains(opApplNode.getOperator().getName())) {
				int opcode = BBuiltInOPs.getOpcode(opApplNode.getOperator().getName());
				return OperatorTypes.bbuiltInOperatorIsPredicate(opcode);
			}
		} else if (expr.getKind() == LetInKind) {
			LetInNode letInNode = (LetInNode) expr;
			return expressionIsAPredicate(letInNode.getBody());
		}
		return false;
	}

	public BAstCreator(ModuleNode moduleNode, ConfigfileEvaluator conEval, SpecAnalyser specAnalyser) {
		this.conEval = conEval;
		this.moduleNode = moduleNode;
		this.specAnalyser = specAnalyser;

		this.bDefinitions = UsedExternalFunctions.createDefinitions(specAnalyser);
		this.predicateVsExpression = new PredicateVsExpression(moduleNode);
		this.bMacroHandler = new BMacroHandler(specAnalyser, conEval);
		this.recursiveFunctionHandler = new RecursiveFunctionHandler(specAnalyser);

		if (conEval != null) {
			this.bConstants = conEval.getbConstantList();
		} else {
			this.bConstants = Arrays.asList(moduleNode.getConstantDecls());
		}

		machineClauseList = new ArrayList<>();

		createSetsClause();
		createDefinitionClause();
		createAbstractConstantsClause();
		createConstantsClause();
		createPropertyClause();
		createVariableClause();
		createInvariantClause();
		createInitClause();
		createOperationsClause();

		start = new Start(new AAbstractMachineParseUnit(new AMachineMachineVariant(),
				new AMachineHeader(createTIdentifierLiteral(getName(moduleNode)), new LinkedList<>()),
				machineClauseList), new EOF());
	}

	private void createSetsClause() {
		if (conEval == null || conEval.getEnumerationSet() == null || conEval.getEnumerationSet().isEmpty())
			return;

		List<EnumType> printed = new ArrayList<>();
		for (OpDeclNode con : moduleNode.getConstantDecls()) {
			TLAType type = getType(con);

			EnumType e = null;
			if (type instanceof SetType && ((SetType) type).getSubType() instanceof EnumType) {
				e = (EnumType) ((SetType) type).getSubType();
			} else if (type instanceof EnumType) {
				e = (EnumType) type;
			}

			if (e != null && !printed.contains(e)) {
				printed.add(e);
			}
		}

		List<PSet> sets = new ArrayList<>();
		for (int i = 0; i < printed.size(); i++) {
			EnumType enumType = printed.get(i);
			enumType.id = i + 1;
			List<PExpression> elements = enumType.getValues().stream()
					.map(ASTBuilder::createIdentifier)
					.collect(Collectors.toList());
			sets.add(new AEnumeratedSetSet(((AIdentifierExpression) enumType.getBNode()).getIdentifier(), elements));
		}

		machineClauseList.add(new ASetsMachineClause(sets));
	}

	private void createDefinitionClause() {
		List<OpDefNode> bDefs = new ArrayList<>();
		for (OpDefNode def : moduleNode.getOpDefs()) {
			if (specAnalyser.getBDefinitions().contains(def)) {
				if (conEval != null && conEval.getConstantOverrides().containsValue(def)) {
					DebugUtils.printVeryVerboseMsg("Not creating B DEFINITION (in Override Table) " + def.getName() + " " + def);
					continue;
				}
				if (def.getOriginallyDefinedInModuleNode().getName().toString().equals("MC")
						&& !specAnalyser.getUsedDefinitions().contains(def)) {
					// don't skip MC definitions if they are used
					// TODO: check if this is correct (see invariant check for MC below)
					DebugUtils.printDebugMsg("Skipping MC definition: " + def.getName());
					continue;
				}
				//debugUtils.printVeryVerboseMsg("Creating B DEFINITION " + def.getName() + " " + def);

				bDefs.add(def);
			} else {
				DebugUtils.printVeryVerboseMsg("Not creating unused B DEFINITION for " + def.getName() + " " + def);
			}
		}

		List<PDefinition> defs = bDefinitions.getDefinitionNames().stream()
				.map(bDefinitions::getDefinition).collect(Collectors.toList()); // add external functions
		for (OpDefNode opDefNode : bDefs) {
			List<PExpression> params = Arrays.stream(opDefNode.getParams())
				                           .map(this::createIdentifierFromNode)
				                           .collect(Collectors.toList());
			PDefinition definition;
			if (predicateVsExpression.getDefinitionType(opDefNode) == DefinitionType.PREDICATE) {
				PPredicate pred = null;
				// special predicate definitions

				if (pred == null) {
					pred = visitExprNodePredicate(opDefNode.getBody());
					if (!params.isEmpty()) {
						// wrap in let to force single evaluation of all params
						List<PExpression> paramsCopy = params;
						List<PExpression> defParams = Arrays.stream(opDefNode.getParams())
							                              .map(p -> createPositionedNode(createIdentifier("p__" + getName(p)), p))
							                              .collect(Collectors.toList());
						params = defParams;
						List<PPredicate> conjuncts = IntStream.range(0, paramsCopy.size())
							                             .mapToObj(i -> {
								                             PExpression param = paramsCopy.get(i);
								                             PExpression defParam = defParams.get(i);
								                             return new AEqualPredicate(param.clone(), defParam.clone());
							                             })
							                             .collect(Collectors.toList());
						pred = new ALetPredicatePredicate(paramsCopy, createConjunction(conjuncts), pred);
					}
					DebugUtils.printVeryVerboseMsg("Creating Predicate DEFINITION " + getName(opDefNode));
				} else {
					DebugUtils.printVeryVerboseMsg("Creating Predicate DEFINITION " + getName(opDefNode) + " (optimized)");
				}
				definition = new APredicateDefinitionDefinition(
					new TDefLiteralPredicate(getName(opDefNode)),
					params,
					pred
				);
			} else {
				PExpression expr = null;

				// special expression definitions
				if (opDefNode.isStandardModule()) {
					List<PExpression> paramAccess = Arrays.stream(opDefNode.getParams())
						                                .map(this::createIdentifierFromNodeWithoutPos)
						                                .collect(Collectors.toList());
					switch (getName(opDefNode)) {
						case ":>": {
							expr = createPositionedNode(createSetOfPExpression(createNestedCouple(Arrays.asList(paramAccess.get(0), paramAccess.get(1)))), opDefNode.getBody());
							break;
						}
						case "@@": {
							expr = createPositionedNode(new AOverwriteExpression(paramAccess.get(1), paramAccess.get(0)), opDefNode.getBody());
							break;
						}
					}
				}

				if (expr == null) {
					expr = visitExprNodeExpression(opDefNode.getBody());
					if (!params.isEmpty()) {
						// wrap in let to force single evaluation of all params
						List<PExpression> paramsCopy = params;
						List<PExpression> defParams = Arrays.stream(opDefNode.getParams())
							         .map(p -> createPositionedNode(createIdentifier("p__" + getName(p)), p))
							         .collect(Collectors.toList());
						params = defParams;
						List<PPredicate> conjuncts = IntStream.range(0, paramsCopy.size())
							                             .mapToObj(i -> {
								                             PExpression param = paramsCopy.get(i);
															 PExpression defParam = defParams.get(i);
								                             return new AEqualPredicate(param.clone(), defParam.clone());
							                             })
							                             .collect(Collectors.toList());
						expr = new ALetExpressionExpression(paramsCopy, createConjunction(conjuncts), expr);
					}
					DebugUtils.printVeryVerboseMsg("Creating Expression DEFINITION " + getName(opDefNode));
				} else {
					DebugUtils.printVeryVerboseMsg("Creating Expression DEFINITION " + getName(opDefNode) + " (optimized)");
				}
				definition = new AExpressionDefinitionDefinition(
					new TIdentifierLiteral(getName(opDefNode)),
					params,
					expr
				);
			}
			PDefinition def = createPositionedNode(definition, opDefNode);
			bDefinitions.addDefinition(def);
			defs.add(def);
		}

		if (!defs.isEmpty()) {
			machineClauseList.add(new ADefinitionsMachineClause(defs));
		}
	}

	private void createOperationsClause() {
		List<BOperation> bOperations = specAnalyser.getBOperations();
		if (bOperations == null || bOperations.isEmpty()) {
			return;
		}

		List<POperation> opList = new ArrayList<>();
		for (BOperation op : bOperations) {
			opList.add(createPositionedNode(op.getBOperation(this), op.getNode()));
		}

		machineClauseList.add(new AOperationsMachineClause(opList));
	}

	private void createInitClause() {
		OpDeclNode[] vars = moduleNode.getVariableDecls();
		if (vars.length == 0)
			return;
		List<PExpression> varList = Arrays.stream(vars).map(this::createIdentifierFromNode).collect(Collectors.toList());
		List<PPredicate> predList = specAnalyser.getInits().stream().map(this::visitExprNodePredicate).collect(Collectors.toList());
		if (predList.isEmpty()) {
			throw new IllegalStateException("Could not find a definition of Init.");
		}
		machineClauseList.add(new AInitialisationMachineClause(
				new ABecomesSuchSubstitution(varList,createConjunction(predList))
		));
	}

	private void createVariableClause() {
		List<OpDeclNode> bVariables = Arrays.asList(moduleNode.getVariableDecls());
		if (!bVariables.isEmpty()) {
			List<PExpression> list = new ArrayList<>();
			for (OpDeclNode opDeclNode : bVariables) {
				AIdentifierExpression id = createPositionedNode(createIdentifier(getName(opDeclNode)), opDeclNode);
				list.add(id);
				types.put(id, getType(opDeclNode));
			}
			machineClauseList.add(new AVariablesMachineClause(list));
		}
	}

	private void createAbstractConstantsClause() {
		List<PExpression> constantsList = new ArrayList<>();

		for (RecursiveDefinition recDef : specAnalyser.getRecursiveDefinitions()) {
			AIdentifierExpression id = createPositionedNode(createIdentifier(getName(recDef.getOpDefNode())),
				recDef.getOpDefNode());
			constantsList.add(id);
			types.put(id, getType(recDef.getOpDefNode()));
		}

		for (OpDefNode recFunc : specAnalyser.getRecursiveFunctions()) {
			AIdentifierExpression id = new AIdentifierExpression(createTIdentifierLiteral(getName(recFunc)));
			constantsList.add(id);
			types.put(id, getType(recFunc));
		}

		if (!constantsList.isEmpty()) {
			machineClauseList.add(new AAbstractConstantsMachineClause(constantsList));
		}
	}

	private void createConstantsClause() {
		List<OpDeclNode> bConstants = conEval != null ? conEval.getbConstantList() : Arrays.asList(moduleNode.getConstantDecls());

		List<PExpression> constantsList = new ArrayList<>();
		for (OpDeclNode opDeclNode : bConstants) {
			AIdentifierExpression id = createPositionedNode(createIdentifier(getName(opDeclNode)), opDeclNode);
			constantsList.add(id);
			types.put(id, getType(opDeclNode));
		}
		if (!constantsList.isEmpty()) {
			machineClauseList.add(new AConstantsMachineClause(constantsList));
		}
	}

	private void createPropertyClause() {
		List<PPredicate> propertiesList = new ArrayList<>();
		propertiesList.addAll(evalRecursiveDefinitions());
		propertiesList.addAll(evalRecursiveFunctions());
		for (OpDeclNode con : bConstants) {
			if (conEval != null && conEval.getConstantAssignments().containsKey(con) && bConstants.contains(con)) {
				TLCValueNode v = conEval.getConstantAssignments().get(con);
				TLAType t = v.getType();

				AEqualPredicate equal = new AEqualPredicate();
				equal.setLeft(createIdentifierFromNode(con));
				if (t instanceof SetType && ((SetType) t).getSubType() instanceof EnumType
						&& ((SetEnumValue) v.getValue()).elems.size() == ((EnumType) ((SetType) t).getSubType()).modelvalues.size()) {
					// isEnum = true
					equal.setRight(createIdentifier(((SetType) t).getSubType().toString()));
				} else {
					equal.setRight(createTLCValue(v.getValue()));
				}
				propertiesList.add(equal);
			} else {
				propertiesList.add(new AMemberPredicate(createIdentifierFromNode(con), getType(con).getBNode()));
			}
		}

		if (conEval != null) {
			for (Entry<OpDeclNode, OpDefNode> entry : conEval.getConstantOverrides().entrySet()) {
				OpDeclNode con = entry.getKey();
				OpDefNode def = entry.getValue(); // generated def
				try {
					OpApplNode opApplNode = (OpApplNode) def.getBody();
					if (opApplNode.getKind() == UserDefinedOpKind) {
						def = (OpDefNode) opApplNode.getOperator();
					}
				} catch (ClassCastException e) {
					// ignore
				}
				propertiesList.add(new AEqualPredicate(createIdentifierFromNode(con), visitExprNodeExpression(def.getBody())));
			}
		}

		AssumeNode[] assumes = moduleNode.getAssumptions();
		List<PPredicate> assertionList = new ArrayList<>();
		for (AssumeNode assumeNode : assumes) {
			ThmOrAssumpDefNode def = assumeNode.getDef();
			if (def != null) {
				assertionList.add(new ALabelPredicate(
						new TPragmaIdOrString(def.getName().toString()),
						createPositionedNode(visitAssumeNode(assumeNode), assumeNode)));
			} else {
				propertiesList.add(visitAssumeNode(assumeNode));
			}
		}
		if (!propertiesList.isEmpty()) {
			machineClauseList.add(new APropertiesMachineClause(createConjunction(propertiesList)));
		}
		if (!assertionList.isEmpty()) {
			machineClauseList.add(new AAssertionsMachineClause(assertionList));
		}
	}

	private List<PPredicate> evalRecursiveFunctions() {
		List<PPredicate> propertiesList = new ArrayList<>();
		for (OpDefNode def : specAnalyser.getRecursiveFunctions()) {
			propertiesList.add(new AEqualPredicate(createIdentifierFromNode(def),
					visitExprNodeExpression(def.getBody())));
		}
		return propertiesList;
	}

	private List<PPredicate> evalRecursiveDefinitions() {
		// TODO: review this method
		List<PPredicate> propertiesList = new ArrayList<>();

		for (RecursiveDefinition recDef : specAnalyser.getRecursiveDefinitions()) {
			OpDefNode def = recDef.getOpDefNode();
			// TLAType t = getType(def);
			// OpApplNode ifThenElse = recDef.getIfThenElse();
			List<PExpression> paramList1 = new ArrayList<>();
			List<PPredicate> typeList = new ArrayList<>();
			// ArrayList<PExpression> paramList2 = new ArrayList<PExpression>();
			for (FormalParamNode p : def.getParams()) {
				paramList1.add(createIdentifierFromNode(p));
				// paramList2.add(createIdentifierFromNode(p.getName().toString()));
				typeList.add(new AEqualPredicate(createIdentifierFromNode(p), getType(p).getBNode()));
			}
			ALambdaExpression lambda1 = new ALambdaExpression(
					paramList1,
					createConjunction(typeList),
					visitExprNodeExpression(def.getBody())
			);
			// lambda1.setPredicate(visitExprOrOpArgNodePredicate(ifThenElse.getArgs()[0]));
			// lambda1.setExpression(visitExprOrOpArgNodeExpression(ifThenElse.getArgs()[1]));

			// ALambdaExpression lambda2 = new ALambdaExpression();
			// lambda2.setIdentifiers(paramList2);
			// ANegationPredicate not = new
			// ANegationPredicate(visitExprOrOpArgNodePredicate(ifThenElse.getArgs()[0]));
			// lambda2.setPredicate(not);
			// lambda2.setExpression(visitExprOrOpArgNodeExpression(ifThenElse.getArgs()[2]));
			// AUnionExpression union = new AUnionExpression(lambda1, lambda2);

			propertiesList.add(new AEqualPredicate(createIdentifierFromNode(def), lambda1));
		}

		return propertiesList;
	}

	private PExpression createTLCValue(Value tlcValue) {
		switch (tlcValue.getKind()) {
			case INTVALUE:
				return createIntegerExpression(tlcValue.toString());
			case REALVALUE:
				return createRealExpression(tlcValue.toString());
			case SETENUMVALUE:
				return new ASetExtensionExpression(Arrays.stream(((SetEnumValue) tlcValue).elems.toArray())
						.map(this::createTLCValue).collect(Collectors.toList()));
			case MODELVALUE:
				return createIdentifier(tlcValue.toString());
			case STRINGVALUE:
				return createStringExpression(((StringValue) tlcValue).getVal().toString());
			default:
				throw new NotImplementedException("TLC value in configuration file: " + tlcValue.getClass());
		}
	}

	private void createInvariantClause() {
		List<PPredicate> predList = new ArrayList<>();
		for (OpDeclNode var : moduleNode.getVariableDecls()) {
			predList.add(new AMemberPredicate(createIdentifierFromNode(var), getType(var).getBNode()));
		}

		for (OpDefNode def : specAnalyser.getInvariants()) {
			if (def.getOriginallyDefinedInModuleNode().getName().toString().equals("MC")) {
				predList.add(visitExprNodePredicate(def.getBody()));
			} else {
				if (predicateVsExpression.getDefinitionType(def) == DefinitionType.PREDICATE) {
					predList.add(new ADefinitionPredicate(new TDefLiteralPredicate(getName(def)), new LinkedList<>()));
				} else {
					ADefinitionExpression defExpr = new ADefinitionExpression(new TIdentifierLiteral(getName(def)), new LinkedList<>());
					predList.add(new AEqualPredicate(defExpr, new ABooleanTrueExpression()));
				}
			}
		}

		if (!predList.isEmpty()) {
			machineClauseList.add(new AInvariantMachineClause(createConjunction(predList)));
		}
	}

	private PPredicate visitAssumeNode(AssumeNode assumeNode) {
		return visitExprNodePredicate(assumeNode.getAssume());
	}

	public PPredicate visitExprNodePredicate(ExprNode exprNode) {
		switch (exprNode.getKind()) {
			case OpApplKind:
				return visitOpApplNodePredicate((OpApplNode) exprNode);
			case LetInKind:
				return visitExprNodePredicate(((LetInNode) exprNode).getBody());
			case NumeralKind:
			case DecimalKind:
				throw new RuntimeException("Expected a predicate " + exprNode);
			default:
				throw new NotImplementedException(exprNode.getClass().toString());
		}
	}

	private PExpression visitExprNodeExpression(ExprNode exprNode) {
		switch (exprNode.getKind()) {
			case OpApplKind:
				return visitOpApplNodeExpression((OpApplNode) exprNode);
			case NumeralKind: {
				NumeralNode node = (NumeralNode) exprNode;
				String number = String.valueOf(node.useVal() ? node.val() : node.bigVal());
				return createPositionedNode(createIntegerExpression(number), exprNode);
			}
			case DecimalKind: {
				DecimalNode node = (DecimalNode) exprNode;
				String number = String.valueOf(node.bigVal() == null ? node.mantissa() * Math.pow(10,node.exponent()) : node.bigVal());
				// the image of BigDecimal should always be with .0, because the node would not have been of DecimalKind otherwise
				return createPositionedNode(createRealExpression(number), exprNode);
			}
			case StringKind: {
				StringNode s = (StringNode) exprNode;
				return createPositionedNode(createStringExpression(s.getRep().toString()), exprNode);
			}
			case AtNodeKind: { // @
				AtNode at = (AtNode) exprNode;
				// PExpression base = visitExprNodeExpression(at.getAtBase());
				return evalAtNode(
						new LinkedList<>(Arrays.asList(at.getAtModifier().getArgs())), // seq
						getType(at.getExceptRef()),
						((PExpression) at.getExceptComponentRef().getToolObject(EXCEPT_BASE)).clone()
				);
			}
			case LetInKind:
				return visitExprNodeExpression(((LetInNode) exprNode).getBody());
			default:
				throw new NotImplementedException(exprNode.getClass().toString());
		}
	}

	private PExpression evalAtNode(LinkedList<ExprOrOpArgNode> list, TLAType type, PExpression base) {
		if (list.isEmpty()) {
			return base;
		}
		if (type instanceof FunctionType) {
			return evalAtNode(list, ((FunctionType) type).getRange(),
					new AFunctionExpression(base, Collections.singletonList(visitExprOrOpArgNodeExpression(list.poll()))));
		} else {
			StringNode stringNode = (StringNode) list.poll();
			// TODO rename field name
			String fieldName = stringNode.getRep().toString();
			return evalAtNode(list, ((StructType) type).getType(fieldName),
					new ARecordFieldExpression(base, new TIdentifierLiteral(fieldName)));
		}
	}

	private PPredicate visitOpApplNodePredicate(OpApplNode opApplNode) {
		switch (opApplNode.getOperator().getKind()) {
			case VariableDeclKind:
			case ConstantDeclKind:
			case FormalParamKind:
				return createPositionedNode(new AEqualPredicate(
							createIdentifierFromNode(opApplNode.getOperator()),
							new ABooleanTrueExpression()),
						opApplNode);
			case BuiltInKind:
				return visitBuiltInKindPredicate(opApplNode);
			case UserDefinedOpKind:
				return visitUserdefinedOpPredicate(opApplNode);
			default:
				throw new NotImplementedException(opApplNode.getClass().toString());
		}
	}

	private PExpression visitOpApplNodeExpression(OpApplNode n) {
		switch (n.getOperator().getKind()) {
			case ConstantDeclKind:
			case VariableDeclKind:
				return createIdentifierFromNode(n.getOperator());
			case FormalParamKind: {
				FormalParamNode param = (FormalParamNode) n.getOperator();
				ExprOrOpArgNode e = (ExprOrOpArgNode) param.getToolObject(SUBSTITUTE_PARAM);
				if (e != null) {
					return visitExprOrOpArgNodeExpression(e);
				}

				if (recursiveFunctionHandler.isRecursiveFunction(param)) {
					List<SymbolNode> list = recursiveFunctionHandler.getAdditionalParams(param);
					if (!list.isEmpty()) {
						List<PExpression> params = new ArrayList<>();
						for (SymbolNode symbolNode : list) {
							params.add(createIdentifierFromNode(symbolNode));
						}
						return new AFunctionExpression(createIdentifierFromNode(param), params);
					}
				}
				FormalParamNode[] tuple = (FormalParamNode[]) param.getToolObject(TUPLE);
				if (tuple != null) {
					if (tuple.length == 1) {
						return new AFunctionExpression(
								createIdentifierFromNode(n.getOperator()),
								Collections.singletonList(createIntegerExpression("1"))
						);
					} else {
						StringBuilder sb = new StringBuilder();
						List<TLAType> typeList = new ArrayList<>();
						int number = -1;
						for (int j = 0; j < tuple.length; j++) {
							FormalParamNode p = tuple[j];
							sb.append(p.getName());
							typeList.add(getType(p));
							if (p == param) {
								number = j + 1;
							}
						}
						return createProjectionFunction(createIdentifier(sb.toString()), number, new TupleType(typeList));
					}
				}
				return createIdentifierFromNode(n.getOperator());
			}
			case BuiltInKind:
				return visitBuiltInKindExpression(n);
			case UserDefinedOpKind:
				return visitUserdefinedOpExpression(n);
			default:
				throw new NotImplementedException(n.getOperator().getName().toString());
		}
	}

	private PPredicate visitUserdefinedOpPredicate(OpApplNode n) {
		OpDefNode def = (OpDefNode) n.getOperator();
		// Operator is a B built-in operator
		if (BBuiltInOPs.isBBuiltInOp(def)) {
			return visitBBuiltInsPredicate(n);
		}
		if (specAnalyser.getRecursiveFunctions().contains(def)) {
			return new AEqualPredicate(createIdentifierFromNode(def), new ABooleanTrueExpression());
		}
		if (Arrays.asList(moduleNode.getOpDefs()).contains(def)) {
			if (predicateVsExpression.getDefinitionType(def) == DefinitionType.EXPRESSION) {
				return new AEqualPredicate(
						new ADefinitionExpression(new TIdentifierLiteral(getName(def)), visitArgs(n)),
						new ABooleanTrueExpression()
				);
			} else {
				return new ADefinitionPredicate(new TDefLiteralPredicate(getName(def)), visitArgs(n));
			}
		} else {
			FormalParamNode[] params = def.getParams();
			for (int i = 0; i < params.length; i++) {
				FormalParamNode param = params[i];
				param.setToolObject(SUBSTITUTE_PARAM, n.getArgs()[i]);
			}
			return visitExprNodePredicate(def.getBody());
		}
	}

	private String getName(SymbolNode def) {
		return def.getName().toString();
	}

	private PExpression visitUserdefinedOpExpression(OpApplNode n) {
		OpDefNode def = (OpDefNode) n.getOperator();
		// Operator is a B built-in operator
		if (BBuiltInOPs.isBBuiltInOp(def)) {
			return visitBBuiltInsExpression(n);
		}

		if (specAnalyser.getRecursiveFunctions().contains(def)) {
			List<SymbolNode> params = recursiveFunctionHandler.getAdditionalParams(def);
			if (params.isEmpty()) {
				return createIdentifierFromNode(def);
			} else {
				return new AFunctionExpression(
						createIdentifierFromNode(def),
						params.stream().map(this::createIdentifierFromNode).collect(Collectors.toList())
				);
			}
		}

		if (Arrays.asList(moduleNode.getOpDefs()).contains(def)) {
			List<PExpression> params = visitArgs(n);

			if (conEval != null && conEval.getConstantOverrides().containsValue(def)) {
				// used constants name instead of the definition overriding the constant
				String name = conEval.getConstantOverrides().entrySet().stream()
						.filter(entry -> entry.getValue().equals(def))
						.map(entry -> getName(entry.getKey()))
						.findFirst()
						.orElse(null);
				if (params.isEmpty()) {
					return createIdentifier(name);
				} else {
					return new AFunctionExpression(createIdentifier(name), params);
				}
			} else {
				if (predicateVsExpression.getDefinitionType(def) == DefinitionType.PREDICATE) {
					return new AConvertBoolExpression(
							new ADefinitionPredicate(new TDefLiteralPredicate(getName(n.getOperator())), params));
				} else {
					return new ADefinitionExpression(new TIdentifierLiteral(getName(n.getOperator())), params);
				}
			}
		} else {
			FormalParamNode[] params = def.getParams();
			for (int i = 0; i < params.length; i++) {
				FormalParamNode param = params[i];
				param.setToolObject(SUBSTITUTE_PARAM, n.getArgs()[i]);
			}
			return visitExprNodeExpression(def.getBody());
		}
	}

	private PPredicate visitBBuiltInsPredicate(OpApplNode opApplNode) {
		PPredicate returnNode;
		switch (BBuiltInOPs.getOpcode(opApplNode.getOperator().getName())) {
			case B_OPCODE_lt: // <
				returnNode = new ALessPredicate(visitExprOrOpArgNodeExpression(opApplNode.getArgs()[0]),
					visitExprOrOpArgNodeExpression(opApplNode.getArgs()[1]));
				break;

			case B_OPCODE_gt: // >
				returnNode = new AGreaterPredicate(visitExprOrOpArgNodeExpression(opApplNode.getArgs()[0]),
					visitExprOrOpArgNodeExpression(opApplNode.getArgs()[1]));
				break;

			case B_OPCODE_leq: // <=
				returnNode = new ALessEqualPredicate(visitExprOrOpArgNodeExpression(opApplNode.getArgs()[0]),
					visitExprOrOpArgNodeExpression(opApplNode.getArgs()[1]));
				break;

			case B_OPCODE_geq: // >=
				returnNode = new AGreaterEqualPredicate(visitExprOrOpArgNodeExpression(opApplNode.getArgs()[0]),
					visitExprOrOpArgNodeExpression(opApplNode.getArgs()[1]));
				break;

			case B_OPCODE_finite: // IsFiniteSet({1,2,3})
				returnNode = new AMemberPredicate(visitExprOrOpArgNodeExpression(opApplNode.getArgs()[0]),
						new AFinSubsetExpression(visitExprOrOpArgNodeExpression(opApplNode.getArgs()[0])));
				break;

			case B_OPCODE_true: // TRUE
				// TODO: we could use ATruth-/AFalsityPredicate
				returnNode = new AEqualPredicate(new ABooleanTrueExpression(), new ABooleanTrueExpression());
				break;

			case B_OPCODE_false: // FALSE
				returnNode = new AEqualPredicate(new ABooleanFalseExpression(), new ABooleanTrueExpression());
				break;

			case B_OPCODE_assert: {
				String stringMsg = opApplNode.getArgs()[1] instanceof StringNode
						? ((StringNode) opApplNode.getArgs()[1]).getRep().toString()
						: "Error";
				returnNode = new ADefinitionPredicate(
						new TDefLiteralPredicate(ASSERT_TRUE),
						Arrays.asList( // params
								visitExprOrOpArgNodeExpression(opApplNode.getArgs()[0]),
								createStringExpression(stringMsg)
						)
				);
				break;
			}

			default:
				throw new RuntimeException("Unexpected operator: " + opApplNode.getOperator().getName().toString() + "\n"
						+ opApplNode.stn.getLocation());
		}
		return createPositionedNode(returnNode, opApplNode);
	}

	private PExpression visitBBuiltInsExpression(OpApplNode opApplNode) {
		PExpression returnNode;
		switch (BBuiltInOPs.getOpcode(opApplNode.getOperator().getName())) {
			// use visitBBuiltInsPredicate for inner part of AConvertBoolExpression where possible
			case B_OPCODE_lt: // <
			case B_OPCODE_gt: // >
			case B_OPCODE_leq: // <=
			case B_OPCODE_geq: // >=
			case B_OPCODE_assert:
			case B_OPCODE_finite: // IsFiniteSet({1,2,3})
				returnNode = new AConvertBoolExpression(visitBBuiltInsPredicate(opApplNode));
				break;

			case B_OPCODE_bool: // BOOLEAN
				returnNode = new ABoolSetExpression();
				break;
			case B_OPCODE_true: // TRUE
				returnNode = new ABooleanTrueExpression();
				break;
			case B_OPCODE_false: // FALSE
				returnNode = new ABooleanFalseExpression();
				break;

			/*
			 * Standard Module Naturals
			 */
			case B_OPCODE_nat: // Nat
				returnNode = new ANaturalSetExpression();
				break;

			case B_OPCODE_plus: // +
				returnNode = new AAddExpression(visitExprOrOpArgNodeExpression(opApplNode.getArgs()[0]),
						visitExprOrOpArgNodeExpression(opApplNode.getArgs()[1]));
				break;

			case B_OPCODE_minus: // -
				returnNode = new AMinusOrSetSubtractExpression(visitExprOrOpArgNodeExpression(opApplNode.getArgs()[0]),
						visitExprOrOpArgNodeExpression(opApplNode.getArgs()[1]));
				break;

			case B_OPCODE_times: // *
				returnNode = new AMultOrCartExpression(visitExprOrOpArgNodeExpression(opApplNode.getArgs()[0]),
						visitExprOrOpArgNodeExpression(opApplNode.getArgs()[1]));
				break;

			case B_OPCODE_exp: // x^y
				returnNode = new APowerOfExpression(visitExprOrOpArgNodeExpression(opApplNode.getArgs()[0]),
						visitExprOrOpArgNodeExpression(opApplNode.getArgs()[1]));
				break;

			case B_OPCODE_mod: { // modulo a % b = a - b* (a/b)
				PExpression a = visitExprOrOpArgNodeExpression(opApplNode.getArgs()[0]);
				PExpression b = visitExprOrOpArgNodeExpression(opApplNode.getArgs()[1]);

				returnNode = new AMinusOrSetSubtractExpression(
						a.clone(),
						new AMultOrCartExpression(b.clone(), new AFlooredDivExpression(a, b))
				);
				break;
			}

			case B_OPCODE_div: // \div
				returnNode = new AFlooredDivExpression(
						visitExprOrOpArgNodeExpression(opApplNode.getArgs()[0]),
						visitExprOrOpArgNodeExpression(opApplNode.getArgs()[1]));
				break;

			case B_OPCODE_realdiv: // /
				returnNode = new ADivExpression(
						visitExprOrOpArgNodeExpression(opApplNode.getArgs()[0]),
						visitExprOrOpArgNodeExpression(opApplNode.getArgs()[1]));
				break;

			case B_OPCODE_dotdot: // ..
				returnNode = new AIntervalExpression(visitExprOrOpArgNodeExpression(opApplNode.getArgs()[0]),
						visitExprOrOpArgNodeExpression(opApplNode.getArgs()[1]));
				break;

			case B_OPCODE_int: // Int
				returnNode = new AIntegerSetExpression();
				break;

			case B_OPCODE_real: // Real
				returnNode = new ARealSetExpression();
				break;

			case B_OPCODE_uminus: // -x
				returnNode = new AUnaryMinusExpression(visitExprOrOpArgNodeExpression(opApplNode.getArgs()[0]));
				break;

			case B_OPCODE_card: // Cardinality
				returnNode = new ACardExpression(visitExprOrOpArgNodeExpression(opApplNode.getArgs()[0]));
				break;

			case B_OPCODE_string: // STRING
				returnNode = new AStringSetExpression();
				break;

			/*
			 * Standard Module Sequences
			 */
			case B_OPCODE_seq: // Seq(S) - set of sequences
				returnNode = new ASeqExpression(visitExprOrOpArgNodeExpression(opApplNode.getArgs()[0]));
				break;

			case B_OPCODE_len: // length of the sequence
				returnNode = new ASizeExpression(visitExprOrOpArgNodeExpression(opApplNode.getArgs()[0]));
				break;

			case B_OPCODE_conc: // s \o s2 - concatenation of s and s2
				returnNode = new AConcatExpression(visitExprOrOpArgNodeExpression(opApplNode.getArgs()[0]),
						visitExprOrOpArgNodeExpression(opApplNode.getArgs()[1]));
				break;

			case B_OPCODE_append: // Append(s,x)
				returnNode = new AInsertTailExpression(visitExprOrOpArgNodeExpression(opApplNode.getArgs()[0]),
						visitExprOrOpArgNodeExpression(opApplNode.getArgs()[1]));
				break;

			case B_OPCODE_head: // Head(s)
				returnNode = new AFirstExpression(visitExprOrOpArgNodeExpression(opApplNode.getArgs()[0]));
				break;

			case B_OPCODE_tail: // Tail(s)
				returnNode = new ATailExpression(visitExprOrOpArgNodeExpression(opApplNode.getArgs()[0]));
				break;

			case B_OPCODE_subseq: { // SubSeq(s,a,b)
				// new translation: (s /|\ b) \|/ a-1 (this saves us a new identifier name)
				returnNode = new ARestrictTailExpression(
						new ARestrictFrontExpression(
								visitExprOrOpArgNodeExpression(opApplNode.getArgs()[0]), // s
								visitExprOrOpArgNodeExpression(opApplNode.getArgs()[2]) // b
						),
						new AMinusOrSetSubtractExpression(
								visitExprOrOpArgNodeExpression(opApplNode.getArgs()[1]), // a
								createIntegerExpression("1")
						)
				);
				break;
				// previous translation: %t_.(t_ : 1..(b-a+1)| s(t_+a-1))
					/*PExpression a = visitExprOrOpArgNodeExpression(opApplNode.getArgs()[1]);
					PExpression b = visitExprOrOpArgNodeExpression(opApplNode.getArgs()[2]);

					returnNode = new ALambdaExpression( // %t_.(t_ : 1..(b-a+1)| s(t_+a-1))
							createIdentifierList("t_"),
							new AMemberPredicate( // t_ : 1..(b-a+1)
									createIdentifierNode("t_"),
									new AIntervalExpression(
											createIntegerExpression("1"),
											new AAddExpression(
													new AMinusOrSetSubtractExpression(b, a),
													createIntegerExpression("1")
											)
									)
							),
							new AFunctionExpression( // s(t_+a-1)
									visitExprOrOpArgNodeExpression(opApplNode.getArgs()[0]), // s
									Collections.singletonList(
											new AMinusOrSetSubtractExpression(
													new AAddExpression(createIdentifierNode("t_"), a.clone()),
													createIntegerExpression("1")
											)
									)
							)
					);*/
			}

			case B_OPCODE_setsum: {
				AIdentifierExpression variable = createIdentifier("t_"); // TODO unused identifier name
				returnNode = new AGeneralSumExpression(
						Collections.singletonList(variable.clone()),
						new AMemberPredicate(
								variable.clone(),
								visitExprOrOpArgNodeExpression(opApplNode.getArgs()[0])
						),
						variable.clone()
				);
				break;
			}

			case B_OPCODE_setprod: {
				AIdentifierExpression variable = createIdentifier("t_"); // TODO unused identifier name
				returnNode = new AGeneralProductExpression(
						Collections.singletonList(variable.clone()),
						new AMemberPredicate(
								variable.clone(),
								visitExprOrOpArgNodeExpression(opApplNode.getArgs()[0])
						),
						variable.clone()
				);
				break;
			}

			default:
				throw new RuntimeException("Unexpected operator: " + opApplNode.getOperator().getName().toString() + "\n"
						+ opApplNode.stn.getLocation());
		}
		return createPositionedNode(returnNode, opApplNode);
	}

	private PPredicate visitBuiltInKindPredicate(OpApplNode n) {
		PPredicate returnNode;
		switch (getOpCode(n.getOperator().getName())) {
			// use visitBuiltInKindExpression for left side of AEqualPredicate where possible
			case OPCODE_case:
			case OPCODE_prime: // x' ~> x_n
			case OPCODE_bc: // CHOOSE x \in S: P
			case OPCODE_uc: // CHOOSE x : P
				returnNode = new AEqualPredicate(visitBuiltInKindExpression(n), new ABooleanTrueExpression());
				break;

			case OPCODE_land: // \land
				returnNode = new AConjunctPredicate(
						visitExprOrOpArgNodePredicate(n.getArgs()[0]),
						visitExprOrOpArgNodePredicate(n.getArgs()[1])
				);
				break;

			case OPCODE_cl: // $ConjList
				returnNode = createConjunction(Arrays.stream(n.getArgs())
						.map(this::visitExprOrOpArgNodePredicate).collect(Collectors.toList()));
				break;

			case OPCODE_lor: // \/
				returnNode = new ADisjunctPredicate(
						visitExprOrOpArgNodePredicate(n.getArgs()[0]),
						visitExprOrOpArgNodePredicate(n.getArgs()[1])
				);
				break;

			case OPCODE_dl: // $DisjList
				returnNode = createDisjunction(Arrays.stream(n.getArgs())
						.map(this::visitExprOrOpArgNodePredicate).collect(Collectors.toList()));
				break;

			case OPCODE_neg: // \neg
			case OPCODE_lnot: // ~ / \lnot
				returnNode = new ANegationPredicate(visitExprOrOpArgNodePredicate(n.getArgs()[0]));
				break;

			case OPCODE_equiv: // \equiv
				returnNode = new AEquivalencePredicate(
						visitExprOrOpArgNodePredicate(n.getArgs()[0]),
						visitExprOrOpArgNodePredicate(n.getArgs()[1])
				);
				break;

			case OPCODE_implies: // =>
				returnNode = new AImplicationPredicate(
						visitExprOrOpArgNodePredicate(n.getArgs()[0]),
						visitExprOrOpArgNodePredicate(n.getArgs()[1])
				);
				break;

			case OPCODE_be: { // \E x \in S : P
				returnNode = new AExistsPredicate(createListOfParameters(n.getBdedQuantSymbolLists()),
						new AConjunctPredicate(
								visitBoundsOfLocalVariables(n),
								visitExprOrOpArgNodePredicate(n.getArgs()[0])
				));
				break;
			}

			case OPCODE_bf: { // \A x \in S : P
				returnNode = new AForallPredicate(createListOfParameters(n.getBdedQuantSymbolLists()),
						new AImplicationPredicate(
								visitBoundsOfLocalVariables(n),
								visitExprOrOpArgNodePredicate(n.getArgs()[0])
				));
				break;
			}

			case OPCODE_eq: // =
				returnNode = new AEqualPredicate(
						visitExprOrOpArgNodeExpression(n.getArgs()[0]),
						visitExprOrOpArgNodeExpression(n.getArgs()[1])
				);
				break;

			case OPCODE_noteq: // /=
				returnNode = new ANotEqualPredicate(
						visitExprOrOpArgNodeExpression(n.getArgs()[0]),
						visitExprOrOpArgNodeExpression(n.getArgs()[1])
				);
				break;

			case OPCODE_in: // \in
				returnNode = new AMemberPredicate(
						visitExprOrOpArgNodeExpression(n.getArgs()[0]),
						visitExprOrOpArgNodeExpression(n.getArgs()[1])
				);
				break;

			case OPCODE_notin: // \notin
				returnNode = new ANotMemberPredicate(
						visitExprOrOpArgNodeExpression(n.getArgs()[0]),
						visitExprOrOpArgNodeExpression(n.getArgs()[1])
				);
				break;

			case OPCODE_subseteq: // \subseteq {1,2} <: {1,2,3}
				returnNode = new ASubsetPredicate(
						visitExprOrOpArgNodeExpression(n.getArgs()[0]),
						visitExprOrOpArgNodeExpression(n.getArgs()[1])
				);
				break;

			case OPCODE_fa: { // f[1]
				// TODO: difference predicate/expression?
				List<PExpression> paramList = new ArrayList<>();
				ExprOrOpArgNode dom = n.getArgs()[1];
				if (dom instanceof OpApplNode && ((OpApplNode) dom).getOperator().getName().toString().equals("$Tuple")) {
					paramList.addAll(visitArgs((OpApplNode) dom));
				} else {
					paramList.add(visitExprOrOpArgNodeExpression(dom));
				}
				returnNode = new AEqualPredicate(new AFunctionExpression(
						visitExprOrOpArgNodeExpression(n.getArgs()[0]),
						paramList
				), new ABooleanTrueExpression());
				break;
			}

			case OPCODE_rs: { // $RcdSelect r.c
				// TODO: difference predicate/expression?
				returnNode = new AEqualPredicate(new ARecordFieldExpression(
						visitExprOrOpArgNodeExpression(n.getArgs()[0]),
						new TIdentifierLiteral(((StringNode) n.getArgs()[1]).getRep().toString())
				), new ABooleanTrueExpression());
				break;
			}

			case OPCODE_unchanged: {
				OpApplNode node = (OpApplNode) n.getArgs()[0];
				// System.out.println(" Translating UNCHANGED : " + node.toString());
				// System.out.println(" Top-level unchanged for this operation: " + this.toplevelUnchangedVariableNames);
				if (node.getOperator().getKind() == VariableDeclKind) {
					return createUnchangedPrimeEquality(node);
				} else if (node.getOperator().getKind() == UserDefinedOpKind) {
					node = (OpApplNode) ((OpDefNode) node.getOperator()).getBody();
				}

				returnNode = createConjunction(Arrays.stream(node.getArgs())
						.map(arg -> createUnchangedPrimeEquality((OpApplNode) arg))
						.collect(Collectors.toList()));
				break;
			}

			case OPCODE_ite: // IF THEN ELSE
				// AIfPredicatePredicate is rewritten by the parser => failing tests
				AImplicationPredicate impl1 = new AImplicationPredicate(
						visitExprOrOpArgNodePredicate(n.getArgs()[0]), // IF
						visitExprOrOpArgNodePredicate(n.getArgs()[1]) // THEN
				);
				AImplicationPredicate impl2 = new AImplicationPredicate(
						new ANegationPredicate(visitExprOrOpArgNodePredicate(n.getArgs()[0])), // not IF
						visitExprOrOpArgNodePredicate(n.getArgs()[2]) // ELSE
				);
				returnNode = new AConjunctPredicate(impl1, impl2);
				break;

			case 0:
				return visitBBuiltInsPredicate(n);
			default:
				throw new NotImplementedException(n.getOperator().getName().toString());
		}
		return createPositionedNode(returnNode, n);
	}

	private PExpression visitBuiltInKindExpression(OpApplNode n) {
		switch (getOpCode(n.getOperator().getName())) {
			// use visitBuiltInKindPredicate for inner part of AConvertBoolExpression where possible
			case OPCODE_land: // \land
			case OPCODE_equiv: // \equiv
			case OPCODE_implies: // =>
			case OPCODE_cl: // $ConjList
			case OPCODE_dl: // $DisjList
			case OPCODE_lor: // \/
			case OPCODE_neg: // \neg
			case OPCODE_lnot: // ~ / \lnot
			case OPCODE_in: // \in
			case OPCODE_notin: // \notin
			case OPCODE_eq: // =
			case OPCODE_noteq: // /=
			case OPCODE_subseteq: // \subseteq {1,2} <: {1,2,3}
			case OPCODE_bf: // \A x \in S : P
			case OPCODE_be: // \E x \in S : P
				return new AConvertBoolExpression(visitBuiltInKindPredicate(n));

			/*
			 * Set Operators
			 */
			case OPCODE_se: // SetEnumeration {..}
				if (n.getArgs().length == 0) {
					return new AEmptySetExpression();
				} else {
					return new ASetExtensionExpression(visitArgs(n));
				}

			case OPCODE_setdiff: // set difference
				return new AMinusOrSetSubtractExpression(
						visitExprOrOpArgNodeExpression(n.getArgs()[0]),
						visitExprOrOpArgNodeExpression(n.getArgs()[1])
				);

			case OPCODE_cup: // set union
				return new AUnionExpression(
						visitExprOrOpArgNodeExpression(n.getArgs()[0]),
						visitExprOrOpArgNodeExpression(n.getArgs()[1])
				);

			case OPCODE_cap: // set intersection
				return new AIntersectionExpression(
						visitExprOrOpArgNodeExpression(n.getArgs()[0]),
						visitExprOrOpArgNodeExpression(n.getArgs()[1])
				);

			case OPCODE_subset: // SUBSET
				return new APowSubsetExpression(visitExprOrOpArgNodeExpression(n.getArgs()[0]));

			case OPCODE_union: // Union - Union{{1},{2}}
				return new AGeneralUnionExpression(visitExprOrOpArgNodeExpression(n.getArgs()[0]));

			case OPCODE_sso: // $SubsetOf Represents {x \in S : P}
				return new AComprehensionSetExpression(
						createListOfParameters(n.getBdedQuantSymbolLists()), // params
						new AConjunctPredicate(
								visitBoundsOfFunctionsVariables(n),
								visitExprOrOpArgNodePredicate(n.getArgs()[0])
						)
				);

			case OPCODE_soa: { // $SetOfAll Represents {e : p1 \in S, p2,p3 \in S2}
				// UNION(p1,p2,p3).(P | {e})
				return new AQuantifiedUnionExpression(
						createListOfParameters(n.getBdedQuantSymbolLists()),
						createConjunction(Collections.singletonList(visitBoundsOfLocalVariables(n))),
						new ASetExtensionExpression(
								Collections.singletonList(visitExprOrOpArgNodeExpression(n.getArgs()[0])))
				);
				// currently not used:
				/* final String nameOfTempVariable = "t_";

				AEqualPredicate equals = new AEqualPredicate(
					createIdentifierNode(nameOfTempVariable),
					visitExprOrOpArgNodeExpression(n.getArgs()[0])
				);
				// predList.add(equals);
				AExistsPredicate exist = new AExistsPredicate(
					idList,
					createConjunction(predList)
				);

				AComprehensionSetExpression compre = new AComprehensionSetExpression();
				List<PExpression> tList = new ArrayList<>();
				tList.add(createIdentifierNode(nameOfTempVariable));
				compre.setIdentifiers(tList);
				compre.setPredicates(exist);*/
			}

			case OPCODE_nrfs:
			case OPCODE_fc: // Represents [x \in S |-> e].
			case OPCODE_rfs: {
				// TODO: review
				FormalParamNode[][] params = n.getBdedQuantSymbolLists();
				List<PExpression> idList = createListOfParameters(params);
				boolean[] isTuple = n.isBdedQuantATuple();
				List<PExpression> idList2 = new ArrayList<>();
				for (int i = 0; i < params.length; i++) {
					if (isTuple[i] && i > 0) { // concatenate identifiers
						idList2.add(createIdentifier(Arrays.stream(params[i])
								.map(p -> p.getName().toString())
								.collect(Collectors.joining())));
					} else {
						Arrays.stream(params[i])
								.map(p -> createIdentifier(p.getName().toString()))
								.forEach(idList2::add);
					}
				}

				ALambdaExpression lambda = new ALambdaExpression(idList2, visitBoundsOfFunctionsVariables(n),
						visitExprOrOpArgNodeExpression(n.getArgs()[0]));

				if (recursiveFunctionHandler.isRecursiveFunction(n)) {
					List<SymbolNode> externParams = recursiveFunctionHandler.getAdditionalParams(n);
					if (!externParams.isEmpty()) {
						List<PExpression> shiftedParams = new ArrayList<>();
						List<PPredicate> predList2 = new ArrayList<>();
						for (SymbolNode p : externParams) {
							shiftedParams.add(createIdentifierFromNode(p));
							predList2.add(new AMemberPredicate(createIdentifierFromNode(p), getType(p).getBNode()));
						}
						return new ALambdaExpression(shiftedParams, createConjunction(predList2), lambda);
					}
				}
				return lambda;
			}

			case OPCODE_fa: { // f[1]
				TLAType t = getType(n.getArgs()[0]);
				if (t instanceof TupleType && ((TupleType) t).getTypes().size() > 1) {
					NumeralNode num = (NumeralNode) n.getArgs()[1];
					int field = num.val();
					PExpression pair = visitExprOrOpArgNodeExpression(n.getArgs()[0]);
					return createProjectionFunction(pair, field, t);
				} else {
					AFunctionExpression func = new AFunctionExpression();
					func.setIdentifier(visitExprOrOpArgNodeExpression(n.getArgs()[0]));
					List<PExpression> paramList = new ArrayList<>();

					ExprOrOpArgNode dom = n.getArgs()[1];
					if (dom instanceof OpApplNode
						&& ((OpApplNode) dom).getOperator().getName().toString().equals("$Tuple")) {
						OpApplNode domOpAppl = (OpApplNode) dom;
						if (domOpAppl.getArgs().length == 1) {
							List<PExpression> list = new ArrayList<>();
							list.add(visitExprOrOpArgNodeExpression(domOpAppl.getArgs()[0]));
							ASequenceExtensionExpression seq = new ASequenceExtensionExpression(list);
							paramList.add(seq);
						} else {
							for (int i = 0; i < domOpAppl.getArgs().length; i++) {
								paramList.add(visitExprOrOpArgNodeExpression(domOpAppl.getArgs()[i]));
							}
						}

					} else {
						paramList.add(visitExprOrOpArgNodeExpression(dom));
					}
					func.setParameters(paramList);
					return func;
				}
			}

			case OPCODE_domain:
				return new ADomainExpression(visitExprOrOpArgNodeExpression(n.getArgs()[0]));

			case OPCODE_sof: // [ A -> B]
				return new ATotalFunctionExpression(
						visitExprOrOpArgNodeExpression(n.getArgs()[0]),
						visitExprOrOpArgNodeExpression(n.getArgs()[1])
				);

			case OPCODE_tup: { // $Tuple
				List<PExpression> args = visitArgs(n);
				if (getType(n) instanceof TupleType) {
					return new ACoupleExpression(args);
				} else {
					if (args.isEmpty()) {
						return new AEmptySequenceExpression();
					} else {
						return new ASequenceExtensionExpression(args);
					}
				}
			}

			case OPCODE_cp: { // $CartesianProd A \X B \X C
				PExpression first = visitExprOrOpArgNodeExpression(n.getArgs()[0]);
				for (int i = 1; i < n.getArgs().length; i++) {
					PExpression second = visitExprOrOpArgNodeExpression(n.getArgs()[i]);
					first = new AMultOrCartExpression(first, second);
				}
				return first;
			}

			case OPCODE_sor: { // $SetOfRcds [L1 : e1, L2 : e2]
				SetType pow = (SetType) getType(n);
				StructType struct = (StructType) pow.getSubType();
				Map<String, PExpression> pairMap = new HashMap<>();
				for (ExprOrOpArgNode arg : n.getArgs()) {
					OpApplNode pair = (OpApplNode) arg;
					pairMap.put(((StringNode) pair.getArgs()[0]).getRep().toString(),
							visitExprOrOpArgNodeExpression(pair.getArgs()[1]));
				}
				List<PRecEntry> recList = new ArrayList<>();
				for (String fieldName : struct.getFields()) {
					PExpression value = pairMap.containsKey(fieldName)
							? pairMap.get(fieldName)
							: struct.getType(fieldName).getBNode();
					if (struct.isExtensible()) {
						value = new APowSubsetExpression(new AMultOrCartExpression(new ABoolSetExpression(), value));
					}
					recList.add(new ARecEntry(new TIdentifierLiteral(fieldName), value));
				}
				return new AStructExpression(recList);
			}

			case OPCODE_rc: { // [h_1 |-> 1, h_2 |-> 2]
				StructType struct = (StructType) getType(n);
				Map<String, PExpression> pairMap = new HashMap<>();
				for (ExprOrOpArgNode arg : n.getArgs()) {
					OpApplNode pair = (OpApplNode) arg;
					pairMap.put(((StringNode) pair.getArgs()[0]).getRep().toString(),
							visitExprOrOpArgNodeExpression(pair.getArgs()[1]));
				}
				List<PRecEntry> recList = new ArrayList<>();
				for (String fieldName : struct.getFields()) {
					PExpression value;
					if (pairMap.containsKey(fieldName)) {
						value = pairMap.get(fieldName);
						if (struct.isExtensible()) {
							value = new ASetExtensionExpression(Collections.singletonList(
									new ACoupleExpression(Arrays.asList(new ABooleanTrueExpression(), value))));
						}
					} else if (struct.isExtensible()) {
						value = new AEmptySetExpression();
					} else { // this struct is extensible ; TODO: is this correct? by the ifs it is NOT extensible
						throw new NotImplementedException("Missing case handling extensible structs.");
					}
					recList.add(new ARecEntry(new TIdentifierLiteral(fieldName), value));
				}
				return new ARecExpression(recList);
			}

			case OPCODE_rs: { // $RcdSelect r.c
				StructType struct = (StructType) getType(n.getArgs()[0]);
				if (struct.isExtensible()) {
					return new AFunctionExpression(new ARecordFieldExpression(
							visitExprOrOpArgNodeExpression(n.getArgs()[0]),
							new TIdentifierLiteral(((StringNode) n.getArgs()[1]).getRep().toString())
					), Collections.singletonList(new ABooleanTrueExpression()));
				} else {
					return new ARecordFieldExpression(
							visitExprOrOpArgNodeExpression(n.getArgs()[0]),
							new TIdentifierLiteral(((StringNode) n.getArgs()[1]).getRep().toString())
					);
				}
			}

			case OPCODE_prime: // prime
				return createIdentifier(getName(((OpApplNode) n.getArgs()[0]).getOperator()) + "_n");

			case OPCODE_ite: { // IF THEN ELSE
				return new AIfThenElseExpression(
						visitExprOrOpArgNodePredicate(n.getArgs()[0]),
						visitExprOrOpArgNodeExpression(n.getArgs()[1]),
						new LinkedList<>(),
						visitExprOrOpArgNodeExpression(n.getArgs()[2])
				);

				// ALambdaExpression lambda1 = new ALambdaExpression();
				// lambda1.setIdentifiers(createIdentifierList("t_"));
				// AEqualPredicate eq1 = new AEqualPredicate(
				// createIdentifierNode("t_"), new AIntegerExpression(
				// new TIntegerLiteral("0")));
				// AConjunctPredicate c1 = new AConjunctPredicate();
				// c1.setLeft(eq1);
				// c1.setRight(visitExprOrOpArgNodePredicate(n.getArgs()[0]));
				// lambda1.setPredicate(c1);
				// lambda1.setExpression(visitExprOrOpArgNodeExpression(n.getArgs()[1]));
				//
				// ALambdaExpression lambda2 = new ALambdaExpression();
				// lambda2.setIdentifiers(createIdentifierList("t_"));
				// AEqualPredicate eq2 = new AEqualPredicate(
				// createIdentifierNode("t_"), new AIntegerExpression(
				// new TIntegerLiteral("0")));
				// AConjunctPredicate c2 = new AConjunctPredicate();
				// c2.setLeft(eq2);
				// ANegationPredicate not = new ANegationPredicate(
				// visitExprOrOpArgNodePredicate(n.getArgs()[0]));
				// c2.setRight(not);
				// lambda2.setPredicate(c2);
				// lambda2.setExpression(visitExprOrOpArgNodeExpression(n.getArgs()[2]));
				//
				// AUnionExpression union = new AUnionExpression(lambda1, lambda2);
				// AFunctionExpression funCall = new AFunctionExpression();
				// funCall.setIdentifier(union);
				// List<PExpression> list = new ArrayList<PExpression>();
				// list.add(new AIntegerExpression(new TIntegerLiteral("0")));
				// funCall.setParameters(list);
				// return funCall;
			}

			case OPCODE_case:
				return createCaseNode(n);

			case OPCODE_exc: { // $Except
				PExpression res = visitExprOrOpArgNodeExpression(n.getArgs()[0]);
				for (int i = 1; i < n.getArgs().length; i++) {
					OpApplNode pair = (OpApplNode) n.getArgs()[i];
					OpApplNode first = (OpApplNode) pair.getArgs()[0]; // seq
					pair.setToolObject(EXCEPT_BASE, res.clone());
					res = evalExceptValue(res.clone(), new LinkedList<>(Arrays.asList(first.getArgs())),
							getType(n), pair.getArgs()[1]);
				}
				return res;
			}

			case OPCODE_seq: // !
				return visitExprOrOpArgNodeExpression(n.getArgs()[0]);

			case OPCODE_uc: // CHOOSE x : P
				return createUnboundedChoose(n);
			case OPCODE_bc: // CHOOSE x \in S: P
				return createBoundedChoose(n);

			case 0:
				return visitBBuiltInsExpression(n);
			default:
				throw new NotImplementedException("Operator: " + n.getOperator().getName() + " not supported.");
		}
	}

	private PExpression evalExceptValue(PExpression prefix, LinkedList<ExprOrOpArgNode> seqList, TLAType tlaType, ExprOrOpArgNode val) {
		ExprOrOpArgNode head = seqList.poll();
		if (head == null) {
			return visitExprOrOpArgNodeExpression(val);
		}

		if (tlaType instanceof StructType) {
			StructType structType = (StructType) tlaType;

			List<PRecEntry> list = new ArrayList<>();
			for (String fieldName : structType.getFields()) {
				ARecordFieldExpression select = new ARecordFieldExpression(prefix.clone(), new TIdentifierLiteral(fieldName));
				list.add(new ARecEntry(
						new TIdentifierLiteral(fieldName),
						fieldName.equals(((StringNode) head).getRep().toString()) // field
								? evalExceptValue(select, seqList, structType.getType(fieldName), val)
								: select
				));
			}
			return new ARecExpression(list);
		} else {
			AFunctionExpression funcCall = new AFunctionExpression(prefix,
					Collections.singletonList(visitExprOrOpArgNodeExpression(head)));
			List<PExpression> coupleList = Arrays.asList(visitExprOrOpArgNodeExpression(head),
					evalExceptValue(funcCall, seqList, ((FunctionType) tlaType).getRange(), val));
			return new AOverwriteExpression(
					prefix.clone(),
					new ASetExtensionExpression(Collections.singletonList(new ACoupleExpression(coupleList)))
			);
		}
	}

	private PExpression createProjectionFunction(PExpression pair, int field, TLAType t) {
		TupleType tuple = (TupleType) t;
		boolean untyped = tuple.isUntyped();
		int size = tuple.getTypes().size();
		if (size <= 1) {
			throw new IllegalArgumentException("tuples must have at least two elements");
		}
		if (field < 1 || field > size) {
			throw new IllegalArgumentException("tuple index out of bounds");
		}

		AFunctionExpression returnFunc = new AFunctionExpression();
		int index;
		if (field == 1) {
			index = 2;
			returnFunc.setIdentifier(untyped ? new AEventBFirstProjectionV2Expression() : new AFirstProjectionExpression(
					tuple.getTypes().get(0).getBNode(),
					tuple.getTypes().get(1).getBNode()
			));
		} else {
			index = field;
			returnFunc.setIdentifier(untyped ? new AEventBSecondProjectionV2Expression() : new ASecondProjectionExpression(
					createNestedMultOrCard(tuple.getTypes().subList(0, field-1).stream().map(TLAType::getBNode).collect(Collectors.toList())),
					tuple.getTypes().get(field-1).getBNode()
			));
		}
		AFunctionExpression func = returnFunc;
		for (int i = index; i < size; i++) {
			AFunctionExpression newfunc = new AFunctionExpression();
			newfunc.setIdentifier(untyped ? new AEventBFirstProjectionV2Expression() : new AFirstProjectionExpression(
					createNestedMultOrCard(tuple.getTypes().subList(0, i).stream().map(TLAType::getBNode).collect(Collectors.toList())), // type list
					tuple.getTypes().get(i).getBNode()
			));
			func.setParameters(Collections.singletonList(newfunc));
			func = newfunc;
		}
		func.setParameters(Collections.singletonList(pair));
		return returnFunc;
	}

	private PExpression createUnboundedChoose(OpApplNode n) {
		return callExternalFunction(ASTBuilder.CHOOSE,
				new AComprehensionSetExpression(
						Arrays.stream(n.getUnbdedQuantSymbols()).map(this::createIdentifierFromNode).collect(Collectors.toList()),
						visitExprOrOpArgNodePredicate(n.getArgs()[0])
				)
		);
	}

	private PExpression createBoundedChoose(OpApplNode n) {
		return callExternalFunction(ASTBuilder.CHOOSE,
				new AComprehensionSetExpression(
						createListOfParameters(n.getBdedQuantSymbolLists()), // [0]
						new AConjunctPredicate(
								visitBoundsOfLocalVariables(n),
								visitExprOrOpArgNodePredicate(n.getArgs()[0])
						)
				)
		);
	}

	private PExpression createCaseNode(OpApplNode n) {
		List<PPredicate> conditions = new ArrayList<>();
		List<PPredicate> disjunctionList = new ArrayList<>();
		for (int i = 0; i < n.getArgs().length; i++) {
			OpApplNode pair = (OpApplNode) n.getArgs()[i];

			AConjunctPredicate conj = new AConjunctPredicate();
			if (pair.getArgs()[0] == null) {
				conj.setLeft(new ANegationPredicate(createDisjunction(conditions)));
			} else {
				conditions.add(visitExprOrOpArgNodePredicate(pair.getArgs()[0]));
				conj.setLeft(visitExprOrOpArgNodePredicate(pair.getArgs()[0]));
			}
			conj.setRight(new AEqualPredicate(
					createIdentifier("t_"),
					visitExprOrOpArgNodeExpression(pair.getArgs()[1])
			));
			disjunctionList.add(conj);
		}
		return new ADefinitionExpression(
				new TIdentifierLiteral("CHOOSE"),
				Collections.singletonList(new AComprehensionSetExpression(
						createIdentifierList("t_"),
						createDisjunction(disjunctionList)
				))
		);
	}

	// create an equality predicate var_n = var if required
	private AEqualPredicate createUnchangedPrimeEquality(OpApplNode var) {
		if (!this.toplevelUnchangedVariableNames.contains(getName(var.getOperator()))) {
			return new AEqualPredicate(
					createIdentifier(getName(var.getOperator()) + "_n"),
					createIdentifierFromNode(var.getOperator())
			);
		}
		// the variable is marked UNCHANGED in a top-level UNCHANGED predicate
		// Hence it will not be added to the ANY variables and we do not need it
		return new AEqualPredicate(new ABooleanTrueExpression(), new ABooleanTrueExpression());
	}

	public PPredicate visitBoundsOfLocalVariables(OpApplNode n) {
		FormalParamNode[][] params = n.getBdedQuantSymbolLists();
		ExprNode[] in = n.getBdedQuantBounds();
		boolean[] isTuple = n.isBdedQuantATuple();

		List<PPredicate> predList = new ArrayList<>();
		for (int i = 0; i < params.length; i++) {
			List<PExpression> paramNodes = Arrays.stream(params[i])
					.map(this::createIdentifierFromNode).collect(Collectors.toList());
			if (isTuple[i]) {
				PExpression lhs;
				if (params[i].length == 1) { // one-tuple is translated as a sequence
					lhs = new ASequenceExtensionExpression(paramNodes); // is just params[i][0]
				} else {
					lhs = new ACoupleExpression(paramNodes);
				}
				predList.add(new AMemberPredicate(lhs, visitExprNodeExpression(in[i])));
			} else {
				for (PExpression paramNode : paramNodes) {
					predList.add(new AMemberPredicate(paramNode, visitExprNodeExpression(in[i])));
				}
			}
		}
		return createPositionedNode(createConjunction(predList), n);
	}

	public PPredicate visitBoundsOfFunctionsVariables(OpApplNode n) {
		FormalParamNode[][] params = n.getBdedQuantSymbolLists();
		ExprNode[] in = n.getBdedQuantBounds();
		boolean[] isTuple = n.isBdedQuantATuple();

		List<PPredicate> predList = new ArrayList<>();
		for (int i = 0; i < params.length; i++) {
			List<PExpression> paramNodes = Arrays.stream(params[i])
					.map(this::createIdentifierFromNode).collect(Collectors.toList());
			if (isTuple[i]) {
				if (params[i].length == 1) { // one-tuple is handled as a sequence
					FormalParamNode param = params[i][0];
					param.setToolObject(TUPLE, params[i]);
					predList.add(new AMemberPredicate(createIdentifierFromNode(param), visitExprNodeExpression(in[i])));
				} else if (i == 0) { // do not use prj1 & prj2 if it is the first tuple TODO: why?
					predList.add(new AMemberPredicate(new ACoupleExpression(paramNodes), visitExprNodeExpression(in[i])));
				} else { // '<<b,c>> \in {2} \X {3}' is translated to 'bc : {2} * {3}'
					StringBuilder sb = new StringBuilder();
					for (FormalParamNode param : params[i]) {
						param.setToolObject(TUPLE, params[i]);
						sb.append(param.getName().toString());
					}
					predList.add(new AMemberPredicate(createIdentifier(sb.toString()), visitExprNodeExpression(in[i])));
				}
			} else {
				for (PExpression paramNode : paramNodes) {
					predList.add(new AMemberPredicate(paramNode, visitExprNodeExpression(in[i])));
				}
			}
		}
		return createConjunction(predList);
	}

	public PPredicate visitExprOrOpArgNodePredicate(ExprOrOpArgNode n) {
		if (n instanceof ExprNode) {
			return visitExprNodePredicate((ExprNode) n);
		} else {
			throw new RuntimeException("OpArgNode not implemented yet");
		}
	}

	public PExpression visitExprOrOpArgNodeExpression(ExprOrOpArgNode n) {
		if (n instanceof ExprNode) {
			return visitExprNodeExpression((ExprNode) n);
		} else {
			throw new RuntimeException("OpArgNode not implemented yet");
		}
	}

	private List<PExpression> visitArgs(OpApplNode n) {
		return Arrays.stream(n.getArgs())
				.map(this::visitExprOrOpArgNodeExpression)
				.collect(Collectors.toList());
	}

	// HELPER METHODS

	public AIdentifierExpression createIdentifierFromNodeWithoutPos(SymbolNode symbolNode) {
		if (bMacroHandler.containsSymbolNode(symbolNode)) {
			return createIdentifier(bMacroHandler.getNewName(symbolNode));
		} else {
			return createIdentifier(symbolNode.getName().toString());
		}
	}

	public AIdentifierExpression createIdentifierFromNode(SymbolNode symbolNode) {
		return createPositionedNode(createIdentifierFromNodeWithoutPos(symbolNode), symbolNode);
	}

	private List<PExpression> createListOfParameters(FormalParamNode[][] params) {
		List<PExpression> list = new ArrayList<>();
		for (FormalParamNode[] formalParamNodes : params) {
			for (FormalParamNode param : formalParamNodes) {
				list.add(createIdentifierFromNode(param));
			}
		}
		return list;
	}

	public static List<TIdentifierLiteral> createTIdentifierLiteral(String name) {
		return Collections.singletonList(new TIdentifierLiteral(name));
	}

	public List<TIdentifierLiteral> createPositionedTIdentifierLiteral(String name, SemanticNode node) {
		return Collections.singletonList(createPositionedNode(new TIdentifierLiteral(name), node));
	}

	private <T extends PositionedNode> T createPositionedNode(T positionedNode, SemanticNode semanticNode) {
		Location location = semanticNode.getTreeNode().getLocation();
		positionedNode.setStartPos(new SourcePosition(location.beginLine(), location.beginColumn()));
		positionedNode.setEndPos(new SourcePosition(location.endLine(), location.endColumn()));
		sourcePosition.add(positionedNode);
		String source = semanticNode.getLocation().source();
		int id = filesOrderedById.indexOf(source);
		if (id == -1) {
			id = filesOrderedById.size();
			filesOrderedById.add(source);
		}
		nodeFileNumbers.assignIdentifiers(id+1, (Node) positionedNode);
		return positionedNode;
	}

	public Start getStartNode() {
		return start;
	}

	public IDefinitions getBDefinitions() {
		// used for the recursive machine loader
		return bDefinitions;
	}

	public Map<Node, TLAType> getTypes() {
		return this.types;
	}

	public Set<PositionedNode> getSourcePositions() {
		return this.sourcePosition;
	}

	public NodeFileNumbers getNodeFileNumbers() {
		return nodeFileNumbers;
	}

	public List<String> getFilesOrderedById() {
		return filesOrderedById;
	}

	public List<String> getUnchangedVariablesNames() {
		return toplevelUnchangedVariableNames;
	}

	public void setUnchangedVariablesNames(List<String> unchangedVariablesNames) {
		this.toplevelUnchangedVariableNames = unchangedVariablesNames;
	}

}
