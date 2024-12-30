package de.tla2bAst;

import de.be4.classicalb.core.parser.Definitions;
import de.be4.classicalb.core.parser.analysis.prolog.NodeFileNumbers;
import de.be4.classicalb.core.parser.node.*;
import de.hhu.stups.sablecc.patch.PositionedNode;
import de.hhu.stups.sablecc.patch.SourcePosition;
import de.tla2b.analysis.*;
import de.tla2b.analysis.PredicateVsExpression.DefinitionType;
import de.tla2b.analysis.UsedExternalFunctions.EXTERNAL_FUNCTIONS;
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

public class BAstCreator extends BuiltInOPs implements TranslationGlobals, BBuildIns, ValueConstants {

	private List<PMachineClause> machineClauseList;
	private ConfigfileEvaluator conEval;
	private final SpecAnalyser specAnalyser;
	private final PredicateVsExpression predicateVsExpression;
	private final BMacroHandler bMacroHandler;
	private final RecursiveFunctionHandler recursiveFunctionHandler;

	private List<OpDeclNode> bConstants;

	private final ModuleNode moduleNode;
	private UsedExternalFunctions usedExternalFunctions;

	private final Definitions bDefinitions = new Definitions();

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

		this.usedExternalFunctions = new UsedExternalFunctions(moduleNode, specAnalyser);
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
		OpDeclNode[] cons = moduleNode.getConstantDecls();
		for (OpDeclNode con : cons) {
			TLAType type = (TLAType) con.getToolObject(TYPE_ID);

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
					.map(BAstCreator::createIdentifierNode)
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

		Set<EXTERNAL_FUNCTIONS> set = usedExternalFunctions.getUsedExternalFunctions();
		List<PDefinition> defs = new ArrayList<>(createDefinitionsForExternalFunctions(set));

		for (OpDefNode opDefNode : bDefs) {
			List<PExpression> params = Arrays.stream(opDefNode.getParams())
					.map(this::createIdentifierNode).collect(Collectors.toList());
			// TLAType type = (TLAType) opDefNode.getToolObject(TYPE_ID);
			// if (opDefNode.level == 2 || type instanceof BoolType) {
			PDefinition definition;
			if (predicateVsExpression.getDefinitionType(opDefNode) == DefinitionType.PREDICATE) {
				definition = new APredicateDefinitionDefinition(
						new TDefLiteralPredicate(getName(opDefNode)),
						params,
						visitExprNodePredicate(opDefNode.getBody())
				);
				DebugUtils.printVeryVerboseMsg("Creating Predicate DEFINITION " + getName(opDefNode));
			} else {
				definition = new AExpressionDefinitionDefinition(
						new TIdentifierLiteral(getName(opDefNode)),
						params,
						visitExprNodeExpression(opDefNode.getBody())
				);
				DebugUtils.printVeryVerboseMsg("Creating Expression DEFINITION " + getName(opDefNode));
			}
			defs.add(createPositionedNode(definition, opDefNode));
		}

		if (!defs.isEmpty()) {
			machineClauseList.add(new ADefinitionsMachineClause(defs));

			for (PDefinition def : defs) {
				if (def instanceof AExpressionDefinitionDefinition) {
					bDefinitions.addDefinition((AExpressionDefinitionDefinition) def, Definitions.Type.Expression);
				} else if (def instanceof APredicateDefinitionDefinition) {
					bDefinitions.addDefinition((APredicateDefinitionDefinition) def, Definitions.Type.Predicate);
				} else {
					bDefinitions.addDefinition((ASubstitutionDefinitionDefinition) def, Definitions.Type.Substitution);
				}
			}
		}
	}

	private List<PDefinition> createDefinitionsForExternalFunctions(Set<EXTERNAL_FUNCTIONS> set) {
		List<PDefinition> list = new ArrayList<>();
		if (set.contains(UsedExternalFunctions.EXTERNAL_FUNCTIONS.CHOOSE)) {
			list.add(new AExpressionDefinitionDefinition(
					new TIdentifierLiteral("CHOOSE"),
					createIdentifierList("X"),
					new AStringExpression(new TStringLiteral("a member of X"))
			));
			list.add(new AExpressionDefinitionDefinition(
					new TIdentifierLiteral("EXTERNAL_FUNCTION_CHOOSE"),
					createIdentifierList("T"),
					new ATotalFunctionExpression(
							new APowSubsetExpression(createIdentifierNode("T")),
							createIdentifierNode("T")
					)
			));
		}
		if (set.contains(UsedExternalFunctions.EXTERNAL_FUNCTIONS.ASSERT)) {
			list.add(new APredicateDefinitionDefinition(
					new TDefLiteralPredicate("ASSERT_TRUE"),
					Arrays.asList(createIdentifierNode("P"), createIdentifierNode("Msg")),
					new ATruthPredicate()
			));
			list.add(new AExpressionDefinitionDefinition(
					new TIdentifierLiteral("EXTERNAL_PREDICATE_ASSERT_TRUE"),
					new ArrayList<>(),
					new AMultOrCartExpression(new ABoolSetExpression(), new AStringSetExpression())
			));
		}
		return list;
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
		List<PExpression> varList = Arrays.stream(vars).map(this::createIdentifierNode).collect(Collectors.toList());
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
				AIdentifierExpression id = createPositionedNode(createIdentifierNode(getName(opDeclNode)), opDeclNode);
				list.add(id);
				types.put(id, (TLAType) opDeclNode.getToolObject(TYPE_ID));
			}
			machineClauseList.add(new AVariablesMachineClause(list));
		}
	}

	private void createAbstractConstantsClause() {
		List<PExpression> constantsList = new ArrayList<>();

		for (RecursiveDefinition recDef : specAnalyser.getRecursiveDefinitions()) {
			AIdentifierExpression id = createPositionedNode(createIdentifierNode(getName(recDef.getOpDefNode())),
				recDef.getOpDefNode());
			constantsList.add(id);
			types.put(id, (TLAType) recDef.getOpDefNode().getToolObject(TYPE_ID));
		}

		for (OpDefNode recFunc : specAnalyser.getRecursiveFunctions()) {
			AIdentifierExpression id = new AIdentifierExpression(createTIdentifierLiteral(getName(recFunc)));
			constantsList.add(id);
			types.put(id, (TLAType) recFunc.getToolObject(TYPE_ID));
		}

		if (!constantsList.isEmpty()) {
			machineClauseList.add(new AAbstractConstantsMachineClause(constantsList));
		}
	}

	private void createConstantsClause() {
		List<OpDeclNode> bConstants = conEval != null ? conEval.getbConstantList() : Arrays.asList(moduleNode.getConstantDecls());

		List<PExpression> constantsList = new ArrayList<>();
		for (OpDeclNode opDeclNode : bConstants) {
			AIdentifierExpression id = createPositionedNode(createIdentifierNode(getName(opDeclNode)), opDeclNode);
			constantsList.add(id);
			types.put(id, (TLAType) opDeclNode.getToolObject(TYPE_ID));
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
				equal.setLeft(createIdentifierNode(con));
				if (t instanceof SetType && ((SetType) t).getSubType() instanceof EnumType
						&& ((SetEnumValue) v.getValue()).elems.size() == ((EnumType) ((SetType) t).getSubType()).modelvalues.size()) {
					// isEnum = true
					equal.setRight(createIdentifierNode(((SetType) t).getSubType().toString()));
				} else {
					equal.setRight(createTLCValue(v.getValue()));
				}
				propertiesList.add(equal);
			} else {
				TLAType t = (TLAType) con.getToolObject(TYPE_ID);
				propertiesList.add(new AMemberPredicate(createIdentifierNode(con), t.getBNode()));
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
				propertiesList.add(new AEqualPredicate(createIdentifierNode(con), visitExprNodeExpression(def.getBody())));
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
			propertiesList.add(new AEqualPredicate(createIdentifierNode(def),
					visitExprNodeExpression(def.getBody())));
		}
		return propertiesList;
	}

	private List<PPredicate> evalRecursiveDefinitions() {
		// TODO: review this method
		List<PPredicate> propertiesList = new ArrayList<>();

		for (RecursiveDefinition recDef : specAnalyser.getRecursiveDefinitions()) {
			OpDefNode def = recDef.getOpDefNode();
			// TLAType t = (TLAType) def.getToolObject(TYPE_ID);
			// OpApplNode ifThenElse = recDef.getIfThenElse();
			FormalParamNode[] params = def.getParams();
			ArrayList<PExpression> paramList1 = new ArrayList<>();
			ArrayList<PPredicate> typeList = new ArrayList<>();
			// ArrayList<PExpression> paramList2 = new ArrayList<PExpression>();
			for (FormalParamNode p : params) {
				paramList1.add(createIdentifierNode(p));
				// paramList2.add(createIdentifierNode(p.getName().toString()));
				TLAType paramType = (TLAType) p.getToolObject(TYPE_ID);
				AEqualPredicate equal = new AEqualPredicate(createIdentifierNode(p), paramType.getBNode());
				typeList.add(equal);
			}
			ALambdaExpression lambda1 = new ALambdaExpression();
			lambda1.setIdentifiers(paramList1);
			lambda1.setPredicate(createConjunction(typeList));
			lambda1.setExpression(visitExprNodeExpression(def.getBody()));
			// lambda1.setPredicate(visitExprOrOpArgNodePredicate(ifThenElse.getArgs()[0]));
			// lambda1.setExpression(visitExprOrOpArgNodeExpression(ifThenElse.getArgs()[1]));

			// ALambdaExpression lambda2 = new ALambdaExpression();
			// lambda2.setIdentifiers(paramList2);
			// ANegationPredicate not = new
			// ANegationPredicate(visitExprOrOpArgNodePredicate(ifThenElse.getArgs()[0]));
			// lambda2.setPredicate(not);
			// lambda2.setExpression(visitExprOrOpArgNodeExpression(ifThenElse.getArgs()[2]));
			// AUnionExpression union = new AUnionExpression(lambda1, lambda2);

			AEqualPredicate equals = new AEqualPredicate(createIdentifierNode(def), lambda1);
			propertiesList.add(equals);
		}

		return propertiesList;
	}

	private PExpression createTLCValue(Value tlcValue) {
		switch (tlcValue.getKind()) {
			case INTVALUE:
				return new AIntegerExpression(new TIntegerLiteral(tlcValue.toString()));
			case REALVALUE:
				return new ARealExpression(new TRealLiteral(tlcValue.toString()));
			case SETENUMVALUE:
				return new ASetExtensionExpression(Arrays.stream(((SetEnumValue) tlcValue).elems.toArray())
						.map(this::createTLCValue).collect(Collectors.toList()));
			case MODELVALUE:
				return createIdentifierNode(tlcValue.toString());
			case STRINGVALUE:
				return new AStringExpression(new TStringLiteral(((StringValue) tlcValue).getVal().toString()));
			default:
				throw new NotImplementedException("TLC value in configuration file: " + tlcValue.getClass());
		}
	}

	private void createInvariantClause() {
		OpDeclNode[] vars = moduleNode.getVariableDecls();

		List<PPredicate> predList = new ArrayList<>();
		for (OpDeclNode var : vars) {
			TLAType varType = (TLAType) var.getToolObject(TYPE_ID);
			predList.add(new AMemberPredicate(createIdentifierNode(var), varType.getBNode()));
		}

		for (OpDefNode def : specAnalyser.getInvariants()) {
			if (def.getOriginallyDefinedInModuleNode().getName().toString().equals("MC")) {
				predList.add(visitExprNodePredicate(def.getBody()));
			} else {
				if (predicateVsExpression.getDefinitionType(def) == DefinitionType.PREDICATE) {
					ADefinitionPredicate defPred = new ADefinitionPredicate();
					defPred.setDefLiteral(new TDefLiteralPredicate(getName(def)));
					predList.add(defPred);
				} else {
					ADefinitionExpression defExpr = new ADefinitionExpression();
					defExpr.setDefLiteral(new TIdentifierLiteral(getName(def)));
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
				// TODO: description
				throw new RuntimeException();
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
				return createPositionedNode(new AIntegerExpression(new TIntegerLiteral(number)), exprNode);
			}
			case DecimalKind: {
				DecimalNode node = (DecimalNode) exprNode;
				String number = String.valueOf(node.bigVal() == null ? node.mantissa() * Math.pow(10,node.exponent()) : node.bigVal());
				// the image of BigDecimal should always be with .0, because the node would not have been of DecimalKind otherwise
				return createPositionedNode(new ARealExpression(new TRealLiteral(number)), exprNode);
			}
			case StringKind: {
				StringNode s = (StringNode) exprNode;
				return createPositionedNode(new AStringExpression(new TStringLiteral(s.getRep().toString())), exprNode);
			}
			case AtNodeKind: { // @
				AtNode at = (AtNode) exprNode;
				// PExpression base = visitExprNodeExpression(at.getAtBase());
				return evalAtNode(
						new LinkedList<>(Arrays.asList(at.getAtModifier().getArgs())), // seq
						(TLAType) at.getExceptRef().getToolObject(TYPE_ID),
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
				return createPositionedNode(
					new AEqualPredicate(createIdentifierNode(opApplNode.getOperator()), new ABooleanTrueExpression()),
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
				return createIdentifierNode(n.getOperator());
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
							params.add(createIdentifierNode(symbolNode));
						}
						return new AFunctionExpression(createIdentifierNode(param), params);
					}
				}
				FormalParamNode[] tuple = (FormalParamNode[]) param.getToolObject(TUPLE);
				if (tuple != null) {
					if (tuple.length == 1) {
						List<PExpression> paramList = new ArrayList<>();
						paramList.add(new AIntegerExpression(new TIntegerLiteral("1")));
						return new AFunctionExpression(createIdentifierNode(n.getOperator()), paramList);
					} else {
						StringBuilder sb = new StringBuilder();
						List<TLAType> typeList = new ArrayList<>();
						int number = -1;
						for (int j = 0; j < tuple.length; j++) {
							FormalParamNode p = tuple[j];
							sb.append(p.getName().toString());
							TLAType type = (TLAType) p.getToolObject(TYPE_ID);
							typeList.add(type);
							if (p == param) {
								number = j + 1;
							}
						}
						return createProjectionFunction(createIdentifierNode(sb.toString()), number, new TupleType(typeList));
					}
				}
				return createIdentifierNode(n.getOperator());
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
		if (BBuiltInOPs.contains(def.getName()) // Operator is a B built-in operator
				&& STANDARD_MODULES.contains(def.getSource().getOriginallyDefinedInModuleNode().getName().toString())) {
			return visitBBuiltInsPredicate(n);
		}
		if (specAnalyser.getRecursiveFunctions().contains(def)) {
			return new AEqualPredicate(createIdentifierNode(def), new ABooleanTrueExpression());
		}
		if (Arrays.asList(moduleNode.getOpDefs()).contains(def)) {
			List<PExpression> params = new ArrayList<>();
			for (int i = 0; i < n.getArgs().length; i++) {
				params.add(visitExprOrOpArgNodeExpression(n.getArgs()[i]));
			}
			if (predicateVsExpression.getDefinitionType(def) == DefinitionType.EXPRESSION) {
				ADefinitionExpression defCall = new ADefinitionExpression();
				defCall.setDefLiteral(new TIdentifierLiteral(getName(def)));
				defCall.setParameters(params);
				return new AEqualPredicate(defCall, new ABooleanTrueExpression());
			} else {
				ADefinitionPredicate defCall = new ADefinitionPredicate();
				defCall.setDefLiteral(new TDefLiteralPredicate(getName(def)));
				defCall.setParameters(params);
				return defCall;
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
		if (BBuiltInOPs.contains(def.getName())
			&& STANDARD_MODULES.contains(def.getSource().getOriginallyDefinedInModuleNode().getName().toString())) {
			return visitBBuiltInsExpression(n);
		}

		if (specAnalyser.getRecursiveFunctions().contains(def)) {
			ArrayList<SymbolNode> list = recursiveFunctionHandler.getAdditionalParams(def);
			if (!list.isEmpty()) {
				AFunctionExpression call = new AFunctionExpression();
				call.setIdentifier(createIdentifierNode(def));
				ArrayList<PExpression> params = new ArrayList<>();
				for (SymbolNode symbolNode : list) {
					params.add(createIdentifierNode(symbolNode));
				}
				call.setParameters(params);
				return call;
			} else {
				return createIdentifierNode(def);
			}
		}

		if (Arrays.asList(moduleNode.getOpDefs()).contains(def)) {
			List<PExpression> params = new ArrayList<>();
			for (int i = 0; i < n.getArgs().length; i++) {
				params.add(visitExprOrOpArgNodeExpression(n.getArgs()[i]));
			}

			if (conEval != null && conEval.getConstantOverrides().containsValue(def)) {
				// used constants name instead of the definition overriding the
				// constant
				Iterator<Entry<OpDeclNode, OpDefNode>> iter = conEval.getConstantOverrides().entrySet().iterator();
				String name = null;
				while (iter.hasNext()) {
					Entry<OpDeclNode, OpDefNode> entry = iter.next();
					if (entry.getValue().equals(def)) {
						name = getName(entry.getKey());
					}
				}
				if (params.isEmpty()) {
					return createIdentifierNode(name);
				} else {
					AFunctionExpression funcCall = new AFunctionExpression();
					funcCall.setIdentifier(createIdentifierNode(name));
					funcCall.setParameters(params);
					return funcCall;
				}
			} else {
				if (predicateVsExpression.getDefinitionType(def) == DefinitionType.PREDICATE) {
					ADefinitionPredicate defPred = new ADefinitionPredicate();
					defPred.setDefLiteral(new TDefLiteralPredicate(getName(n.getOperator())));
					defPred.setParameters(params);
					return new AConvertBoolExpression(defPred);
				} else {
					ADefinitionExpression defExpr = new ADefinitionExpression();
					defExpr.setDefLiteral(new TIdentifierLiteral(getName(n.getOperator())));
					defExpr.setParameters(params);
					return defExpr;
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
		PPredicate returnNode = null;
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
			{
				AMemberPredicate member = new AMemberPredicate();
				member.setLeft(visitExprOrOpArgNodeExpression(opApplNode.getArgs()[0]));
				member.setRight(new AFinSubsetExpression(visitExprOrOpArgNodeExpression(opApplNode.getArgs()[0])));
				returnNode = member;
				break;
			}
			case B_OPCODE_true: // TRUE
				returnNode = new AEqualPredicate(new ABooleanTrueExpression(), new ABooleanTrueExpression());
				break;

			case B_OPCODE_false: // FALSE
				returnNode = new AEqualPredicate(new ABooleanFalseExpression(), new ABooleanTrueExpression());
				break;

			case B_OPCODE_assert: {
				ADefinitionPredicate pred = new ADefinitionPredicate();
				pred.setDefLiteral(new TDefLiteralPredicate("ASSERT_TRUE"));
				ArrayList<PExpression> list = new ArrayList<>();
				list.add(visitExprOrOpArgNodeExpression(opApplNode.getArgs()[0]));
				if (opApplNode.getArgs()[1] instanceof StringNode) {
					StringNode stringNode = (StringNode) opApplNode.getArgs()[1];
					list.add(new AStringExpression(new TStringLiteral(stringNode.getRep().toString())));
				} else {
					list.add(new AStringExpression(new TStringLiteral("Error")));
				}
				pred.setParameters(list);
				returnNode = pred;
				break;
			}
		}
		if (returnNode != null) {
			return createPositionedNode(returnNode, opApplNode);
		} else {
			throw new RuntimeException("Unexpected operator: " + opApplNode.getOperator().getName().toString() + "\n"
				+ opApplNode.stn.getLocation());
		}
	}

	private PExpression visitBBuiltInsExpression(OpApplNode opApplNode) {
		PExpression returnNode = null;
		switch (BBuiltInOPs.getOpcode(opApplNode.getOperator().getName())) {
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

			case B_OPCODE_lt: // <
				returnNode = new AConvertBoolExpression(
					new ALessPredicate(visitExprOrOpArgNodeExpression(opApplNode.getArgs()[0]),
						visitExprOrOpArgNodeExpression(opApplNode.getArgs()[1])));
				break;

			case B_OPCODE_gt: // >
				returnNode = new AConvertBoolExpression(
					new AGreaterPredicate(visitExprOrOpArgNodeExpression(opApplNode.getArgs()[0]),
						visitExprOrOpArgNodeExpression(opApplNode.getArgs()[1])));
				break;
			case B_OPCODE_leq: // <=
				returnNode = new AConvertBoolExpression(
					new ALessEqualPredicate(visitExprOrOpArgNodeExpression(opApplNode.getArgs()[0]),
						visitExprOrOpArgNodeExpression(opApplNode.getArgs()[1])));
				break;

			case B_OPCODE_geq: // >=
				returnNode = new AConvertBoolExpression(
					new AGreaterEqualPredicate(visitExprOrOpArgNodeExpression(opApplNode.getArgs()[0]),
						visitExprOrOpArgNodeExpression(opApplNode.getArgs()[1])));
				break;

			case B_OPCODE_mod: // modulo a % b = a - b* (a/b)
			{
				PExpression a = visitExprOrOpArgNodeExpression(opApplNode.getArgs()[0]);
				PExpression b = visitExprOrOpArgNodeExpression(opApplNode.getArgs()[1]);
				PExpression a2 = visitExprOrOpArgNodeExpression(opApplNode.getArgs()[0]);
				PExpression b2 = visitExprOrOpArgNodeExpression(opApplNode.getArgs()[1]);

				AFlooredDivExpression div = new AFlooredDivExpression(a, b);
				AMultOrCartExpression mult = new AMultOrCartExpression(b2, div);
				returnNode = new AMinusOrSetSubtractExpression(a2, mult);
				break;
			}

			case B_OPCODE_div: // \div
				AFlooredDivExpression aFlooredDivExpression = new AFlooredDivExpression(
					visitExprOrOpArgNodeExpression(opApplNode.getArgs()[0]),
					visitExprOrOpArgNodeExpression(opApplNode.getArgs()[1]));
				returnNode = createPositionedNode(aFlooredDivExpression, opApplNode);;
				break;

			case B_OPCODE_realdiv: // /
				ADivExpression aDivExpression = new ADivExpression(
					visitExprOrOpArgNodeExpression(opApplNode.getArgs()[0]),
					visitExprOrOpArgNodeExpression(opApplNode.getArgs()[1]));
				returnNode = createPositionedNode(aDivExpression, opApplNode);
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

			case B_OPCODE_finite: // IsFiniteSet({1,2,3})
			{
				AMemberPredicate member = new AMemberPredicate();
				member.setLeft(visitExprOrOpArgNodeExpression(opApplNode.getArgs()[0]));
				member.setRight(new AFinSubsetExpression(visitExprOrOpArgNodeExpression(opApplNode.getArgs()[0])));
				returnNode = new AConvertBoolExpression(member);
				break;
			}

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
				// %p.(p : 1..(b-a+1)| s(p+a-1))
				ALambdaExpression lambda = new ALambdaExpression();
				lambda.setIdentifiers(createIdentifierList("t_"));
				AMemberPredicate member = new AMemberPredicate();
				member.setLeft(createIdentifierNode("t_"));
				AIntervalExpression interval = new AIntervalExpression();
				interval.setLeftBorder(new AIntegerExpression(new TIntegerLiteral("1")));
				AMinusOrSetSubtractExpression minus = new AMinusOrSetSubtractExpression();
				minus.setLeft(visitExprOrOpArgNodeExpression(opApplNode.getArgs()[2]));
				minus.setRight(visitExprOrOpArgNodeExpression(opApplNode.getArgs()[1]));
				AAddExpression add = new AAddExpression();
				add.setLeft(minus);
				add.setRight(new AIntegerExpression(new TIntegerLiteral("1")));
				interval.setRightBorder(add);
				member.setRight(interval);
				lambda.setPredicate(member);
				AAddExpression add2 = new AAddExpression();
				add2.setLeft(createIdentifierNode("t_"));
				add2.setRight(visitExprOrOpArgNodeExpression(opApplNode.getArgs()[1]));
				AMinusOrSetSubtractExpression minus2 = new AMinusOrSetSubtractExpression();
				minus2.setLeft(add2);
				minus2.setRight(new AIntegerExpression(new TIntegerLiteral("1")));
				ArrayList<PExpression> params = new ArrayList<>();
				params.add(minus2);
				AFunctionExpression func = new AFunctionExpression();
				func.setIdentifier(visitExprOrOpArgNodeExpression(opApplNode.getArgs()[0]));
				func.setParameters(params);
				lambda.setExpression(func);
				returnNode = lambda;
				break;
			}

			case B_OPCODE_assert: {
				ADefinitionPredicate pred = new ADefinitionPredicate();
				pred.setDefLiteral(new TDefLiteralPredicate("ASSERT_TRUE"));
				ArrayList<PExpression> list = new ArrayList<>();
				list.add(visitExprOrOpArgNodeExpression(opApplNode.getArgs()[0]));
				list.add(new AStringExpression(new TStringLiteral("Error")));
				pred.setParameters(list);
				returnNode = new AConvertBoolExpression(pred);
				break;
			}

			case B_OPCODE_setsum: {
				AGeneralSumExpression sum = new AGeneralSumExpression();
				String variableName = "t_"; // TODO unused identifier name
				sum.setIdentifiers(Collections.singletonList(createIdentifierNode(variableName)));
				AMemberPredicate memberPredicate = new AMemberPredicate();
				memberPredicate.setLeft(createIdentifierNode(variableName));
				memberPredicate.setRight(visitExprOrOpArgNodeExpression(opApplNode.getArgs()[0]));
				sum.setPredicates(memberPredicate);
				sum.setExpression(createIdentifierNode(variableName));
				returnNode = sum;
				break;
			}
		}
		if (returnNode != null) {
			return createPositionedNode(returnNode, opApplNode);
		} else {
			throw new RuntimeException("Unexpected operator: " + opApplNode.getOperator().getName().toString() + "\n"
				+ opApplNode.stn.getLocation());
		}

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

	private PExpression visitBuiltInKindExpression(OpApplNode n) {
		switch (getOpCode(n.getOperator().getName())) {

			case OPCODE_land: // \land
				return new AConvertBoolExpression(new AConjunctPredicate(
						visitExprOrOpArgNodePredicate(n.getArgs()[0]),
						visitExprOrOpArgNodePredicate(n.getArgs()[1])
				));

			case OPCODE_equiv: // \equiv
				return new AConvertBoolExpression(new AEquivalencePredicate(
						visitExprOrOpArgNodePredicate(n.getArgs()[0]),
						visitExprOrOpArgNodePredicate(n.getArgs()[1])
				));

			case OPCODE_implies: // =>
				new AConvertBoolExpression(new AImplicationPredicate(
						visitExprOrOpArgNodePredicate(n.getArgs()[0]),
						visitExprOrOpArgNodePredicate(n.getArgs()[1])
				));

			case OPCODE_cl: // $ConjList
				return new AConvertBoolExpression(createConjunction(Arrays.stream(n.getArgs())
						.map(this::visitExprOrOpArgNodePredicate)
						.collect(Collectors.toList())
				));

			case OPCODE_dl: // $DisjList
				return new AConvertBoolExpression(createDisjunction(Arrays.stream(n.getArgs())
						.map(this::visitExprOrOpArgNodePredicate)
						.collect(Collectors.toList())));

			case OPCODE_lor: // \/
				return new AConvertBoolExpression(new ADisjunctPredicate(
						visitExprOrOpArgNodePredicate(n.getArgs()[0]),
						visitExprOrOpArgNodePredicate(n.getArgs()[1])
				));

			case OPCODE_lnot: // \lnot
				return new AConvertBoolExpression(new ANegationPredicate(visitExprOrOpArgNodePredicate(n.getArgs()[0])));

			case OPCODE_in: // \in
				return new AConvertBoolExpression(new AMemberPredicate(
						visitExprOrOpArgNodeExpression(n.getArgs()[0]),
						visitExprOrOpArgNodeExpression(n.getArgs()[1])
				));

			case OPCODE_notin: // \notin
				return new AConvertBoolExpression(new ANotMemberPredicate(
						visitExprOrOpArgNodeExpression(n.getArgs()[0]),
						visitExprOrOpArgNodeExpression(n.getArgs()[1])
				));

			case OPCODE_eq: // =
				return new AConvertBoolExpression(new AEqualPredicate(
						visitExprOrOpArgNodeExpression(n.getArgs()[0]),
						visitExprOrOpArgNodeExpression(n.getArgs()[1])
				));

			case OPCODE_noteq: // /=
				return new AConvertBoolExpression(new ANotEqualPredicate(
						visitExprOrOpArgNodeExpression(n.getArgs()[0]),
						visitExprOrOpArgNodeExpression(n.getArgs()[1])
				));

			/*
			 * Set Operators
			 */

			case OPCODE_se: // SetEnumeration {..}
				if (n.getArgs().length == 0) {
					return new AEmptySetExpression();
				} else {
					return new ASetExtensionExpression(Arrays.stream(n.getArgs())
							.map(this::visitExprOrOpArgNodeExpression)
							.collect(Collectors.toList()));
				}

			case 0: {
				return visitBBuiltInsExpression(n);
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
			{
				APowSubsetExpression pow = new APowSubsetExpression();
				pow.setExpression(visitExprOrOpArgNodeExpression(n.getArgs()[0]));
				return pow;
			}

			case OPCODE_union: // Union - Union{{1},{2}}
			{
				AGeneralUnionExpression union = new AGeneralUnionExpression();
				union.setExpression(visitExprOrOpArgNodeExpression(n.getArgs()[0]));
				return union;
			}

			case OPCODE_subseteq: // \subseteq {1,2} <: {1,2,3}
			{
				ASubsetPredicate subset = new ASubsetPredicate();
				subset.setLeft(visitExprOrOpArgNodeExpression(n.getArgs()[0]));
				subset.setRight(visitExprOrOpArgNodeExpression(n.getArgs()[1]));
				return new AConvertBoolExpression(subset);
			}

			case OPCODE_sso: { // $SubsetOf Represents {x \in S : P}
				FormalParamNode[][] params = n.getBdedQuantSymbolLists();
				List<PExpression> list = new ArrayList<>();
				for (int i = 0; i < params[0].length; i++) {
					FormalParamNode p = params[0][i];
					list.add(createIdentifierNode(p));
				}
				return new AComprehensionSetExpression(
					list,
					new AConjunctPredicate(
						visitBoundsOfFunctionsVariables(n),
						visitExprOrOpArgNodePredicate(n.getArgs()[0])
					)
				);
			}

			case OPCODE_soa: { // $SetOfAll Represents {e : p1 \in S, p2,p3 \in S2}
				FormalParamNode[][] params = n.getBdedQuantSymbolLists();
				List<PExpression> idList = createListOfIdentifier(params);
				List<PPredicate> predList = new ArrayList<>();
				predList.add(visitBoundsOfLocalVariables(n));

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

				// UNION(p1,p2,p3).(P | {e})
				return new AQuantifiedUnionExpression(
					idList,
					createConjunction(predList),
					new ASetExtensionExpression(
						Collections.singletonList(visitExprOrOpArgNodeExpression(n.getArgs()[0])))
				);
			}

			case OPCODE_nrfs:
			case OPCODE_fc: // Represents [x \in S |-> e].
			case OPCODE_rfs: {
				FormalParamNode[][] params = n.getBdedQuantSymbolLists();
				List<PExpression> idList = new ArrayList<>();
				for (FormalParamNode[] param : params) {
					for (FormalParamNode p : param) {
						idList.add(createIdentifierNode(p));
					}
				}
				boolean[] isTuple = n.isBdedQuantATuple();
				ALambdaExpression lambda = new ALambdaExpression();
				List<PExpression> idList2 = new ArrayList<>();
				for (int i = 0; i < params.length; i++) {
					if (isTuple[i] && i > 0) {
						StringBuilder sb = new StringBuilder();
						for (int j = 0; j < params[i].length; j++) {
							FormalParamNode p = params[i][j];
							sb.append(p.getName().toString());

						}
						idList2.add(createIdentifierNode(sb.toString()));
					} else {
						for (int j = 0; j < params[i].length; j++) {
							FormalParamNode p = params[i][j];
							idList2.add(createIdentifierNode(p.getName().toString()));
						}
					}
				}

				lambda.setIdentifiers(idList2);
				lambda.setPredicate(visitBoundsOfFunctionsVariables(n));
				lambda.setExpression(visitExprOrOpArgNodeExpression(n.getArgs()[0]));

				if (recursiveFunctionHandler.isRecursiveFunction(n)) {

					ArrayList<SymbolNode> externParams = recursiveFunctionHandler.getAdditionalParams(n);
					if (!externParams.isEmpty()) {
						ALambdaExpression lambda2 = new ALambdaExpression();
						ArrayList<PExpression> shiftedParams = new ArrayList<>();
						List<PPredicate> predList2 = new ArrayList<>();
						for (SymbolNode p : externParams) {
							shiftedParams.add(createIdentifierNode(p));

							AMemberPredicate member = new AMemberPredicate();
							member.setLeft(createIdentifierNode(p));
							TLAType t = (TLAType) p.getToolObject(TYPE_ID);
							member.setRight(t.getBNode());
							predList2.add(member);
						}
						lambda2.setIdentifiers(shiftedParams);
						lambda2.setPredicate(createConjunction(predList2));
						lambda2.setExpression(lambda);
						return lambda2;
					}
				}
				return lambda;
			}

			case OPCODE_fa: { // f[1]
				TLAType t = (TLAType) n.getArgs()[0].getToolObject(TYPE_ID);
				if (t instanceof TupleType) {
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
				return new ATotalFunctionExpression(visitExprOrOpArgNodeExpression(n.getArgs()[0]),
					visitExprOrOpArgNodeExpression(n.getArgs()[1]));

			case OPCODE_tup: { // $Tuple
				List<PExpression> list = new ArrayList<>();
				for (int i = 0; i < n.getArgs().length; i++) {
					list.add(visitExprOrOpArgNodeExpression(n.getArgs()[i]));
				}
				TLAType t = (TLAType) n.getToolObject(TYPE_ID);
				if (t instanceof TupleType) {
					return new ACoupleExpression(list);
				} else {
					if (list.isEmpty()) {
						return new AEmptySequenceExpression();
					} else {
						return new ASequenceExtensionExpression(list);
					}
				}
			}

			case OPCODE_cp: // $CartesianProd A \X B \X C
			{
				PExpression first = visitExprOrOpArgNodeExpression(n.getArgs()[0]);
				for (int i = 1; i < n.getArgs().length; i++) {
					PExpression second = visitExprOrOpArgNodeExpression(n.getArgs()[i]);
					first = new AMultOrCartExpression(first, second);
				}
				return first;
			}

			case OPCODE_sor: { // $SetOfRcds [L1 : e1, L2 : e2]
				SetType pow = (SetType) n.getToolObject(TYPE_ID);
				StructType struct = (StructType) pow.getSubType();
				ExprOrOpArgNode[] args = n.getArgs();
				Hashtable<String, PExpression> pairTable = new Hashtable<>();
				for (ExprOrOpArgNode arg : args) {
					OpApplNode pair = (OpApplNode) arg;
					StringNode stringNode = (StringNode) pair.getArgs()[0];
					pairTable.put(stringNode.getRep().toString(), visitExprOrOpArgNodeExpression(pair.getArgs()[1]));
				}
				List<PRecEntry> recList = new ArrayList<>();
				if (struct.isExtensible()) {
					for (int i = 0; i < struct.getFields().size(); i++) {
						String fieldName = struct.getFields().get(i); // name
						ARecEntry rec = new ARecEntry();
						rec.setIdentifier(new TIdentifierLiteral(fieldName));
						AMultOrCartExpression cart = new AMultOrCartExpression();
						cart.setLeft(new ABoolSetExpression());
						if (pairTable.containsKey(fieldName)) {
							cart.setRight(pairTable.get(fieldName));
						} else {
							cart.setRight(struct.getType(fieldName).getBNode());
						}
						rec.setValue(new APowSubsetExpression(cart));
						recList.add(rec);
					}
				} else {
					for (int i = 0; i < struct.getFields().size(); i++) {
						String fieldName = struct.getFields().get(i);
						ARecEntry rec = new ARecEntry();
						rec.setIdentifier(new TIdentifierLiteral(fieldName));
						if (pairTable.containsKey(fieldName)) {
							rec.setValue(pairTable.get(fieldName));
						} else {
							rec.setValue(struct.getType(fieldName).getBNode());
						}
						recList.add(rec);
					}

				}
				return new AStructExpression(recList);
			}

			case OPCODE_rc: { // [h_1 |-> 1, h_2 |-> 2]
				StructType struct = (StructType) n.getToolObject(TYPE_ID);
				if (struct.isExtensible()) {
					Map<String, PExpression> pairTable = new HashMap<>();
					ExprOrOpArgNode[] args = n.getArgs();
					for (ExprOrOpArgNode arg : args) {
						OpApplNode pair = (OpApplNode) arg;
						StringNode stringNode = (StringNode) pair.getArgs()[0];
						pairTable.put(stringNode.getRep().toString(), visitExprOrOpArgNodeExpression(pair.getArgs()[1]));
					}
					List<PRecEntry> recList = new ArrayList<>();
					for (String fieldName : struct.getFields()) {
						ARecEntry rec = new ARecEntry();
						rec.setIdentifier(new TIdentifierLiteral(fieldName));
						if (pairTable.containsKey(fieldName)) {
							ACoupleExpression couple = new ACoupleExpression(Arrays.asList(
									new ABooleanTrueExpression(), pairTable.get(fieldName)));
							rec.setValue(new ASetExtensionExpression(Collections.singletonList(couple)));
						} else {
							AEmptySetExpression emptySet = new AEmptySetExpression();
							rec.setValue(emptySet);
						}
						recList.add(rec);
					}
					return new ARecExpression(recList);

				} else {
					Hashtable<String, PExpression> pairTable = new Hashtable<>();
					ExprOrOpArgNode[] args = n.getArgs();
					for (ExprOrOpArgNode arg : args) {
						OpApplNode pair = (OpApplNode) arg;
						StringNode stringNode = (StringNode) pair.getArgs()[0];
						pairTable.put(stringNode.getRep().toString(), visitExprOrOpArgNodeExpression(pair.getArgs()[1]));
					}
					List<PRecEntry> recList = new ArrayList<>();
					for (String fieldName : struct.getFields()) {
						ARecEntry rec = new ARecEntry();
						rec.setIdentifier(new TIdentifierLiteral(fieldName));
						if (pairTable.containsKey(fieldName)) {
							rec.setValue(pairTable.get(fieldName));
						} else {
							// this struct is extensible
							throw new NotImplementedException("Missing case handling extensible structs.");
						}
						recList.add(rec);
					}
					return new ARecExpression(recList);
				}

			}

			case OPCODE_rs: { // $RcdSelect r.c
				StructType struct = (StructType) n.getArgs()[0].getToolObject(TYPE_ID);
				if (struct.isExtensible()) {
					ARecordFieldExpression rcdSelect = new ARecordFieldExpression();
					rcdSelect.setRecord(visitExprOrOpArgNodeExpression(n.getArgs()[0]));
					StringNode stringNode = (StringNode) n.getArgs()[1];
					rcdSelect.setIdentifier(new TIdentifierLiteral(stringNode.getRep().toString()));
					AFunctionExpression funcCall = new AFunctionExpression();
					funcCall.setIdentifier(rcdSelect);
					funcCall.setParameters(Collections.singletonList(new ABooleanTrueExpression()));
					return funcCall;
				} else {
					ARecordFieldExpression rcdSelect = new ARecordFieldExpression();
					rcdSelect.setRecord(visitExprOrOpArgNodeExpression(n.getArgs()[0]));
					StringNode stringNode = (StringNode) n.getArgs()[1];
					rcdSelect.setIdentifier(new TIdentifierLiteral(stringNode.getRep().toString()));
					return rcdSelect;
				}
			}

			case OPCODE_prime: // prime
			{
				OpApplNode node = (OpApplNode) n.getArgs()[0];
				return createIdentifierNode(node.getOperator().getName().toString() + "_n");
			}

			case OPCODE_ite: { // IF THEN ELSE
				return new AIfThenElseExpression(
						visitExprOrOpArgNodePredicate(n.getArgs()[0]),
						visitExprOrOpArgNodeExpression(n.getArgs()[1]),
						new ArrayList<>(),
						visitExprOrOpArgNodeExpression(n.getArgs()[2]));

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

			case OPCODE_case: {
				return createCaseNode(n);
			}

			case OPCODE_exc: // $Except
			{
				TLAType type = (TLAType) n.getToolObject(TYPE_ID);

				if (type.getKind() == IType.STRUCT) {
					StructType structType = (StructType) type;
					PExpression res = visitExprOrOpArgNodeExpression(n.getArgs()[0]);
					for (int i = 1; i < n.getArgs().length; i++) {
						OpApplNode pair = (OpApplNode) n.getArgs()[i];
						ExprOrOpArgNode first = pair.getArgs()[0];
						ExprOrOpArgNode val = pair.getArgs()[1];
						OpApplNode seq = (OpApplNode) first;

						LinkedList<ExprOrOpArgNode> seqList = new LinkedList<>();
						Collections.addAll(seqList, seq.getArgs());

						pair.setToolObject(EXCEPT_BASE, res.clone());
						res = evalExceptValue(res.clone(), seqList, structType, val);
					}
					return res;

				} else {
					FunctionType func = (FunctionType) type;

					PExpression res = visitExprOrOpArgNodeExpression(n.getArgs()[0]);
					for (int i = 1; i < n.getArgs().length; i++) {
						OpApplNode pair = (OpApplNode) n.getArgs()[i];

						ExprOrOpArgNode first = pair.getArgs()[0];
						ExprOrOpArgNode val = pair.getArgs()[1];
						OpApplNode seq = (OpApplNode) first;

						LinkedList<ExprOrOpArgNode> seqList = new LinkedList<>();
						Collections.addAll(seqList, seq.getArgs());

						pair.setToolObject(EXCEPT_BASE, res.clone());
						res = evalExceptValue(res.clone(), seqList, func, val);
					}
					return res;
				}
			}

			case OPCODE_seq: { // !
				return visitExprOrOpArgNodeExpression(n.getArgs()[0]);
			}

			case OPCODE_uc: { // CHOOSE x : P
				return createUnboundedChoose(n);
			}

			case OPCODE_bc: { // CHOOSE x \in S: P
				return createBoundedChoose(n);
			}

			case OPCODE_bf: { // \A x \in S : P
				FormalParamNode[][] params = n.getBdedQuantSymbolLists();
				List<PExpression> list = new ArrayList<>();
				for (FormalParamNode[] param : params) {
					for (FormalParamNode formalParamNode : param) {
						list.add(createIdentifierNode(formalParamNode));
					}
				}
				return new AConvertBoolExpression(
						new AForallPredicate(
								list,
								new AImplicationPredicate(
									visitBoundsOfLocalVariables(n),
									visitExprOrOpArgNodePredicate(n.getArgs()[0])
								)
						)
				);
			}

			case OPCODE_be: { // \E x \in S : P
				FormalParamNode[][] params = n.getBdedQuantSymbolLists();
				List<PExpression> list = new ArrayList<>();
				for (FormalParamNode[] param : params) {
					for (FormalParamNode formalParamNode : param) {
						list.add(createIdentifierNode(formalParamNode));
					}
				}
				return new AConvertBoolExpression(
						new AExistsPredicate(
								list,
								new AConjunctPredicate(
										visitBoundsOfLocalVariables(n),
										visitExprOrOpArgNodePredicate(n.getArgs()[0])
								)
						)
				);
			}

		}

		throw new NotImplementedException("Missing support for operator: " + n.getOperator().getName());
	}

	private List<PExpression> createListOfIdentifier(FormalParamNode[][] params) {
		List<PExpression> list = new ArrayList<>();
		for (FormalParamNode[] formalParamNodes : params) {
			for (FormalParamNode param : formalParamNodes) {
				list.add(createIdentifierNode(param));
			}
		}
		return list;
	}

	private PExpression evalExceptValue(PExpression prefix, LinkedList<ExprOrOpArgNode> seqList, TLAType tlaType, ExprOrOpArgNode val) {
		ExprOrOpArgNode head = seqList.poll();
		if (head == null) {
			return visitExprOrOpArgNodeExpression(val);
		}

		if (tlaType instanceof StructType) {
			StructType structType = (StructType) tlaType;
			String field = ((StringNode) head).getRep().toString();

			List<PRecEntry> list = new ArrayList<>();
			for (int i = 0; i < structType.getFields().size(); i++) {
				ARecEntry entry = new ARecEntry();
				String fieldName = structType.getFields().get(i);
				entry.setIdentifier(new TIdentifierLiteral(fieldName));

				PExpression value;
				ARecordFieldExpression select = new ARecordFieldExpression();
				select.setRecord(prefix.clone());
				select.setIdentifier(new TIdentifierLiteral(fieldName));
				if (fieldName.equals(field)) {
					value = evalExceptValue(select, seqList, structType.getType(fieldName), val);
				} else {
					value = select;
				}
				entry.setValue(value);
				list.add(entry);

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

		AFunctionExpression returnFunc = new AFunctionExpression();
		int index;
		if (field == 1) {
			index = 2;
			returnFunc.setIdentifier(new AFirstProjectionExpression(
					tuple.getTypes().get(0).getBNode(),
					tuple.getTypes().get(1).getBNode()
			));
		} else {
			index = field;
			List<TLAType> typeList = new ArrayList<>();
			for (int i = 0; i < field - 1; i++) {
				typeList.add(tuple.getTypes().get(i));
			}
			// we could use AEventBSecondProjectionV2Expression here (which would be much easier),
			// but this is only supported by ProB (?)
			returnFunc.setIdentifier(new ASecondProjectionExpression(
					createNestedCouple(typeList),
					tuple.getTypes().get(field - 1).getBNode()
			));
		}
		AFunctionExpression func = returnFunc;
		for (int i = index; i < tuple.getTypes().size(); i++) {
			AFunctionExpression newfunc = new AFunctionExpression();
			List<TLAType> typeList = new ArrayList<>();
			for (int j = 0; j < i; j++) {
				typeList.add(tuple.getTypes().get(j));
			}
			newfunc.setIdentifier(new AFirstProjectionExpression(
					createNestedCouple(typeList),
					tuple.getTypes().get(i).getBNode()
			));

			func.setParameters(Collections.singletonList(newfunc));
			func = newfunc;
		}
		func.setParameters(Collections.singletonList(pair));
		return returnFunc;
	}

	public static PExpression createNestedCouple(List<TLAType> typeList) {
		if (typeList.size() == 1) {
			return typeList.get(0).getBNode();
		}
		List<PExpression> list = new ArrayList<>();
		for (TLAType t : typeList) {
			list.add(t.getBNode());
		}
		AMultOrCartExpression card = new AMultOrCartExpression();
		card.setLeft(list.get(0));
		for (int i = 1; i < list.size(); i++) {
			if (i < list.size() - 1) {
				AMultOrCartExpression old = card;
				old.setRight(list.get(i));
				card = new AMultOrCartExpression();
				card.setLeft(old);
			} else {
				card.setRight(list.get(i));
			}
		}
		return card;
	}

	private PExpression createUnboundedChoose(OpApplNode n) {
		return new ADefinitionExpression(
				new TIdentifierLiteral("CHOOSE"),
				Collections.singletonList(new AComprehensionSetExpression(
						Arrays.stream(n.getUnbdedQuantSymbols()).map(this::createIdentifierNode).collect(Collectors.toList()),
						visitExprOrOpArgNodePredicate(n.getArgs()[0])
				))
		);
	}

	private PExpression createBoundedChoose(OpApplNode n) {
		return new ADefinitionExpression(
				new TIdentifierLiteral("CHOOSE"),
				Collections.singletonList(new AComprehensionSetExpression(
						Arrays.stream(n.getBdedQuantSymbolLists()[0]).map(this::createIdentifierNode).collect(Collectors.toList()),
						new AConjunctPredicate(
								visitBoundsOfLocalVariables(n),
								visitExprOrOpArgNodePredicate(n.getArgs()[0])
						)
				))
		);
	}

	private PExpression createCaseNode(OpApplNode n) {
		List<PPredicate> conditions = new ArrayList<>();
		List<PPredicate> disjunctionList = new ArrayList<>();
		for (int i = 0; i < n.getArgs().length; i++) {
			OpApplNode pair = (OpApplNode) n.getArgs()[i];

			AConjunctPredicate conj = new AConjunctPredicate();
			if (pair.getArgs()[0] == null) {
				ANegationPredicate neg = new ANegationPredicate();
				neg.setPredicate(createDisjunction(conditions));
				conj.setLeft(neg);
			} else {
				conditions.add(visitExprOrOpArgNodePredicate(pair.getArgs()[0]));
				conj.setLeft(visitExprOrOpArgNodePredicate(pair.getArgs()[0]));
			}
			AEqualPredicate equals = new AEqualPredicate();
			equals.setLeft(createIdentifierNode("t_"));
			equals.setRight(visitExprOrOpArgNodeExpression(pair.getArgs()[1]));
			conj.setRight(equals);
			disjunctionList.add(conj);
		}
		AComprehensionSetExpression comprehension = new AComprehensionSetExpression();
		comprehension.setIdentifiers(createIdentifierList("t_"));
		comprehension.setPredicates(createDisjunction(disjunctionList));
		ADefinitionExpression defCall = new ADefinitionExpression();
		defCall.setDefLiteral(new TIdentifierLiteral("CHOOSE"));
		List<PExpression> params = new ArrayList<>();
		params.add(comprehension);
		defCall.setParameters(params);
		return defCall;
	}

	private List<PExpression> createIdentifierList(String name) {
		ArrayList<PExpression> list = new ArrayList<>();
		list.add(createIdentifierNode(name));
		return list;
	}

	private PPredicate visitBuiltInKindPredicate(OpApplNode n) {
		PPredicate returnNode;
		switch (getOpCode(n.getOperator().getName())) {
			case OPCODE_land: // \land
			{
				AConjunctPredicate conjunction = new AConjunctPredicate();
				conjunction.setLeft(visitExprOrOpArgNodePredicate(n.getArgs()[0]));
				conjunction.setRight(visitExprOrOpArgNodePredicate(n.getArgs()[1]));
				returnNode = conjunction;
				break;
			}
			case OPCODE_cl: // $ConjList
			{
				List<PPredicate> list = new ArrayList<>();
				for (int i = 0; i < n.getArgs().length; i++) {
					list.add(visitExprOrOpArgNodePredicate(n.getArgs()[i]));
				}
				returnNode = createConjunction(list);
				break;
			}
			case OPCODE_lor: // \/
			{
				ADisjunctPredicate disjunction = new ADisjunctPredicate();
				disjunction.setLeft(visitExprOrOpArgNodePredicate(n.getArgs()[0]));
				disjunction.setRight(visitExprOrOpArgNodePredicate(n.getArgs()[1]));
				returnNode = disjunction;
				break;
			}
			case OPCODE_dl: // $DisjList
			{
				List<PPredicate> list = new ArrayList<>();
				for (int i = 0; i < n.getArgs().length; i++) {
					list.add(visitExprOrOpArgNodePredicate(n.getArgs()[i]));
				}
				returnNode = createDisjunction(list);
				break;
			}
			case OPCODE_lnot: // \lnot
				returnNode = new ANegationPredicate(visitExprOrOpArgNodePredicate(n.getArgs()[0]));
				break;
			case OPCODE_equiv: // \equiv
				returnNode = new AEquivalencePredicate(visitExprOrOpArgNodePredicate(n.getArgs()[0]),
					visitExprOrOpArgNodePredicate(n.getArgs()[1]));
				break;

			case OPCODE_implies: // =>
				returnNode = new AImplicationPredicate(visitExprOrOpArgNodePredicate(n.getArgs()[0]),
					visitExprOrOpArgNodePredicate(n.getArgs()[1]));
				break;

			case OPCODE_be: { // \E x \in S : P
				FormalParamNode[][] params = n.getBdedQuantSymbolLists();
				ArrayList<PExpression> list = new ArrayList<>();
				for (FormalParamNode[] param : params) {
					for (FormalParamNode formalParamNode : param) {
						list.add(createIdentifierNode(formalParamNode));
					}
				}
				AConjunctPredicate conjunction = new AConjunctPredicate();
				conjunction.setLeft(visitBoundsOfLocalVariables(n));
				conjunction.setRight(visitExprOrOpArgNodePredicate(n.getArgs()[0]));
				returnNode = new AExistsPredicate(list, conjunction);
				break;
			}

			case OPCODE_bf: { // \A x \in S : P
				FormalParamNode[][] params = n.getBdedQuantSymbolLists();
				ArrayList<PExpression> list = new ArrayList<>();
				for (FormalParamNode[] param : params) {
					for (FormalParamNode formalParamNode : param) {
						list.add(createIdentifierNode(formalParamNode));
					}
				}
				AImplicationPredicate implication = new AImplicationPredicate();
				implication.setLeft(visitBoundsOfLocalVariables(n));
				implication.setRight(visitExprOrOpArgNodePredicate(n.getArgs()[0]));
				returnNode = new AForallPredicate(list, implication);
				break;
			}

			case OPCODE_eq: { // =
				AEqualPredicate equal = new AEqualPredicate();
				equal.setLeft(visitExprOrOpArgNodeExpression(n.getArgs()[0]));
				equal.setRight(visitExprOrOpArgNodeExpression(n.getArgs()[1]));
				returnNode = equal;
				break;
			}
			case OPCODE_noteq: // /=
			{
				ANotEqualPredicate notEqual = new ANotEqualPredicate();
				notEqual.setLeft(visitExprOrOpArgNodeExpression(n.getArgs()[0]));
				notEqual.setRight(visitExprOrOpArgNodeExpression(n.getArgs()[1]));
				returnNode = notEqual;
				break;
			}
			case OPCODE_in: // \in
			{
				AMemberPredicate memberPredicate = new AMemberPredicate();
				memberPredicate.setLeft(visitExprOrOpArgNodeExpression(n.getArgs()[0]));
				memberPredicate.setRight(visitExprOrOpArgNodeExpression(n.getArgs()[1]));
				returnNode = memberPredicate;
				break;
			}

			case OPCODE_notin: // \notin
			{
				ANotMemberPredicate notMemberPredicate = new ANotMemberPredicate();
				notMemberPredicate.setLeft(visitExprOrOpArgNodeExpression(n.getArgs()[0]));
				notMemberPredicate.setRight(visitExprOrOpArgNodeExpression(n.getArgs()[1]));
				returnNode = notMemberPredicate;
				break;
			}

			case OPCODE_subseteq: // \subseteq {1,2} <: {1,2,3}
			{
				ASubsetPredicate subset = new ASubsetPredicate();
				subset.setLeft(visitExprOrOpArgNodeExpression(n.getArgs()[0]));
				subset.setRight(visitExprOrOpArgNodeExpression(n.getArgs()[1]));
				returnNode = subset;
				break;
			}

			case OPCODE_fa: { // f[1]
				AFunctionExpression func = new AFunctionExpression();
				func.setIdentifier(visitExprOrOpArgNodeExpression(n.getArgs()[0]));
				List<PExpression> paramList = new ArrayList<>();

				ExprOrOpArgNode dom = n.getArgs()[1];
				if (dom instanceof OpApplNode && ((OpApplNode) dom).getOperator().getName().toString().equals("$Tuple")) {
					OpApplNode domOpAppl = (OpApplNode) dom;
					for (int i = 0; i < domOpAppl.getArgs().length; i++) {
						paramList.add(visitExprOrOpArgNodeExpression(domOpAppl.getArgs()[i]));
					}
				} else {
					paramList.add(visitExprOrOpArgNodeExpression(dom));
				}
				func.setParameters(paramList);
				returnNode = new AEqualPredicate(func, new ABooleanTrueExpression());
				break;
			}

			case OPCODE_rs: { // $RcdSelect r.c
				ARecordFieldExpression rcdSelect = new ARecordFieldExpression();
				rcdSelect.setRecord(visitExprOrOpArgNodeExpression(n.getArgs()[0]));
				StringNode stringNode = (StringNode) n.getArgs()[1];
				rcdSelect.setIdentifier(new TIdentifierLiteral(stringNode.getRep().toString()));
				returnNode = new AEqualPredicate(rcdSelect, new ABooleanTrueExpression());
				break;
			}

			case OPCODE_case: {
				returnNode = new AEqualPredicate(createCaseNode(n), new ABooleanTrueExpression());
				break;
			}
			case OPCODE_prime: // prime
			{
				OpApplNode node = (OpApplNode) n.getArgs()[0];
				returnNode = new AEqualPredicate(createIdentifierNode(getName(node.getOperator()) + "_n"),
					new ABooleanTrueExpression());
				break;
			}
			case OPCODE_unchanged: {
				OpApplNode node = (OpApplNode) n.getArgs()[0];
				// System.out.println(" Translating UNCHANGED : " + node.toString());
				// System.out.println(" Top-level unchanged for this operation: " + this.toplevelUnchangedVariableNames);
				if (node.getOperator().getKind() == VariableDeclKind) {
					return CreateUnchangedPrimeEquality(node);

				} else if (node.getOperator().getKind() == UserDefinedOpKind) {
					OpDefNode operator = (OpDefNode) node.getOperator();
					ExprNode e = operator.getBody();
					node = (OpApplNode) e;
				}

				ArrayList<PPredicate> list = new ArrayList<>();
				for (int i = 0; i < node.getArgs().length; i++) {
					OpApplNode var = (OpApplNode) node.getArgs()[i];
					list.add(CreateUnchangedPrimeEquality(var));
				}
				returnNode = createConjunction(list);
				// returnNode = new AEqualPredicate(new ABooleanTrueExpression(),
				// new ABooleanTrueExpression());
				break;
			}
			case OPCODE_uc: { // CHOOSE x : P
				returnNode = new AEqualPredicate(createUnboundedChoose(n), new ABooleanTrueExpression());
				break;
			}
			case OPCODE_bc: { // CHOOSE x \in S: P
				returnNode = new AEqualPredicate(createBoundedChoose(n), new ABooleanTrueExpression());
				break;
			}
			case OPCODE_ite: // IF THEN ELSE
			{
				AImplicationPredicate impl1 = new AImplicationPredicate();
				impl1.setLeft(visitExprOrOpArgNodePredicate(n.getArgs()[0]));
				impl1.setRight(visitExprOrOpArgNodePredicate(n.getArgs()[1]));

				AImplicationPredicate impl2 = new AImplicationPredicate();
				ANegationPredicate neg = new ANegationPredicate(visitExprOrOpArgNodePredicate(n.getArgs()[0]));
				impl2.setLeft(neg);
				impl2.setRight(visitExprOrOpArgNodePredicate(n.getArgs()[2]));
				returnNode = new AConjunctPredicate(impl1, impl2);
				break;
			}
			case 0:
				return visitBBuiltInsPredicate(n);
			default:
				throw new NotImplementedException(n.getOperator().getName().toString());
		}
		return createPositionedNode(returnNode, n);
	}

	// create an equality predicate var_n = var if required
	private AEqualPredicate CreateUnchangedPrimeEquality(OpApplNode var) {
		if (!this.toplevelUnchangedVariableNames.contains(getName(var.getOperator()))) {
			AEqualPredicate equal = new AEqualPredicate();
			equal.setLeft(createIdentifierNode(getName(var.getOperator()) + "_n"));
			equal.setRight(createIdentifierNode(var.getOperator()));
			return equal;
		} else {
			// the variable is marked UNCHANGED in a top-level UNCHANGED predicate
			// Hence it will not be added to the ANY variables and we do not need it
			return new AEqualPredicate(new ABooleanTrueExpression(), new ABooleanTrueExpression());
		}

	}

	public PPredicate visitBoundsOfLocalVariables(OpApplNode n) {
		FormalParamNode[][] params = n.getBdedQuantSymbolLists();
		ExprNode[] in = n.getBdedQuantBounds();
		boolean[] isTuple = n.isBdedQuantATuple();

		List<PPredicate> predList = new ArrayList<>();
		for (int i = 0; i < params.length; i++) {
			if (isTuple[i]) {
				if (params[i].length == 1) {
					// one-tuple is handled is translated as a sequence
					FormalParamNode param = params[i][0];
					predList.add(new AMemberPredicate(
							new ASequenceExtensionExpression(Collections.singletonList(createIdentifierNode(param))),
							visitExprNodeExpression(in[i]))
					);

				} else {
					ArrayList<PExpression> list = new ArrayList<>();
					for (int j = 0; j < params[i].length; j++) {
						list.add(createIdentifierNode(params[i][j]));
					}
					predList.add(new AMemberPredicate(
							new ACoupleExpression(list),
							visitExprNodeExpression(in[i])
					));
				}
			} else {
				for (int j = 0; j < params[i].length; j++) {
					predList.add(new AMemberPredicate(
							createIdentifierNode(params[i][j]),
							visitExprNodeExpression(in[i])
					));
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
			if (isTuple[i]) {
				if (params[i].length == 1) { // one-tuple is handled as a
					// sequence
					FormalParamNode param = params[i][0];
					param.setToolObject(TUPLE, params[i]);
					predList.add(new AMemberPredicate(createIdentifierNode(param), visitExprNodeExpression(in[i])));
				} else if (i == 0) {
					List<PExpression> list = new ArrayList<>();
					for (int j = 0; j < params[i].length; j++) {
						list.add(createIdentifierNode(params[i][j]));
					}
					predList.add(new AMemberPredicate(new ACoupleExpression(list), visitExprNodeExpression(in[i])));
				} else {
					ArrayList<PExpression> list = new ArrayList<>();
					StringBuilder sb = new StringBuilder();
					for (int j = 0; j < params[i].length; j++) {
						FormalParamNode param = params[i][j];
						if (i > 0) { // do not use prj1 & prj2 if it is the
							// first tuple
							param.setToolObject(TUPLE, params[i]);
						}
						sb.append(param.getName().toString());
						list.add(createIdentifierNode(param));
					}
					predList.add(new AMemberPredicate(createIdentifierNode(sb.toString()), visitExprNodeExpression(in[i])));
				}
			} else {
				for (int j = 0; j < params[i].length; j++) {
					predList.add(new AMemberPredicate(createIdentifierNode(params[i][j]), visitExprNodeExpression(in[i])));
				}
			}
		}
		return createConjunction(predList);
	}

	public PPredicate visitExprOrOpArgNodePredicate(ExprOrOpArgNode n) {
		if (n instanceof ExprNode) {
			return visitExprNodePredicate((ExprNode) n);
		} else {
			throw new RuntimeException("OpArgNode not implemented jet");
		}
	}

	public PExpression visitExprOrOpArgNodeExpression(ExprOrOpArgNode n) {
		if (n instanceof ExprNode) {
			return visitExprNodeExpression((ExprNode) n);
		} else {
			throw new RuntimeException("OpArgNode not implemented jet");
		}
	}

	// HELPER METHODS

	public AIdentifierExpression createIdentifierNode(SymbolNode symbolNode) {
		if (bMacroHandler.containsSymbolNode(symbolNode)) {
			return createPositionedNode(createIdentifierNode(bMacroHandler.getNewName(symbolNode)), symbolNode);
		} else {
			return createPositionedNode(createIdentifierNode(symbolNode.getName().toString()), symbolNode);
		}
	}

	public static AIdentifierExpression createIdentifierNode(String name) {
		return new AIdentifierExpression(createTIdentifierLiteral(name));
	}

	public PPredicate createConjunction(List<PPredicate> list) {
		if (list.size() == 1)
			return list.get(0);
		AConjunctPredicate conj = new AConjunctPredicate();
		conj.setLeft(list.get(0));
		for (int i = 1; i < list.size(); i++) {
			if (i < list.size() - 1) {
				AConjunctPredicate old = conj;
				old.setRight(list.get(i));
				conj = new AConjunctPredicate();
				conj.setLeft(old);
			} else {
				conj.setRight(list.get(i));
			}
		}
		return conj;
	}

	private PPredicate createDisjunction(List<PPredicate> list) {
		if (list.size() == 1)
			return list.get(0);
		ADisjunctPredicate disjunction = new ADisjunctPredicate();
		disjunction.setLeft(list.get(0));
		for (int i = 1; i < list.size(); i++) {
			if (i < list.size() - 1) {
				disjunction.setRight(list.get(i));
				disjunction = new ADisjunctPredicate(disjunction, null);
			} else {
				disjunction.setRight(list.get(i));
			}
		}
		return disjunction;
	}

	public static List<TIdentifierLiteral> createTIdentifierLiteral(String name) {
		return Collections.singletonList(new TIdentifierLiteral(name));
	}

	public List<TIdentifierLiteral> createPositionedTIdentifierLiteral(String name, SemanticNode node) {
		return Collections.singletonList(createPositionedNode(new TIdentifierLiteral(name), node));
	}

	public Start getStartNode() {
		return start;
	}

	public Definitions getBDefinitions() {
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
