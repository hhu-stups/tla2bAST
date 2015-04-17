package de.tla2bAst;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Hashtable;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map.Entry;
import java.util.Set;

import tla2sany.semantic.ASTConstants;
import tla2sany.semantic.AssumeNode;
import tla2sany.semantic.AtNode;
import tla2sany.semantic.ExprNode;
import tla2sany.semantic.ExprOrOpArgNode;
import tla2sany.semantic.FormalParamNode;
import tla2sany.semantic.LetInNode;
import tla2sany.semantic.ModuleNode;
import tla2sany.semantic.NumeralNode;
import tla2sany.semantic.OpApplNode;
import tla2sany.semantic.OpDeclNode;
import tla2sany.semantic.OpDefNode;
import tla2sany.semantic.StringNode;
import tla2sany.semantic.SymbolNode;
import tlc2.tool.BuiltInOPs;
import tlc2.value.ModelValue;
import tlc2.value.SetEnumValue;
import tlc2.value.StringValue;
import tlc2.value.Value;
import tlc2.value.ValueConstants;
import de.be4.classicalb.core.parser.Definitions;
import de.be4.classicalb.core.parser.node.*;
import de.tla2b.analysis.BOperation;
import de.tla2b.analysis.PredicateVsExpression;
import de.tla2b.analysis.RecursiveDefinition;
import de.tla2b.analysis.SpecAnalyser;
import de.tla2b.analysis.UsedExternalFunctions;
import de.tla2b.analysis.PredicateVsExpression.DefinitionType;
import de.tla2b.analysis.UsedExternalFunctions.EXTERNAL_FUNCTIONS;
import de.tla2b.config.ConfigfileEvaluator;
import de.tla2b.config.ValueObj;
import de.tla2b.exceptions.NotImplementedException;
import de.tla2b.global.BBuildIns;
import de.tla2b.global.BBuiltInOPs;
import de.tla2b.global.OperatorTypes;
import de.tla2b.global.Priorities;
import de.tla2b.global.TranslationGlobals;
import de.tla2b.translation.BMacroHandler;
import de.tla2b.translation.RecursiveFunctionHandler;
import de.tla2b.types.EnumType;
import de.tla2b.types.FunctionType;
import de.tla2b.types.IType;
import de.tla2b.types.SetType;
import de.tla2b.types.StructType;
import de.tla2b.types.TLAType;
import de.tla2b.types.TupleType;

public class BAstCreator extends BuiltInOPs implements TranslationGlobals,
		ASTConstants, BBuildIns, Priorities, ValueConstants {

	List<PMachineClause> machineClauseList;
	ConfigfileEvaluator conEval;
	SpecAnalyser specAnalyser;
	private final PredicateVsExpression predicateVsExpression;
	private final BMacroHandler bMacroHandler;
	private final RecursiveFunctionHandler recursiveFunctionHandler;

	private List<OpDeclNode> bConstants;

	private ModuleNode moduleNode;
	private UsedExternalFunctions usedExternalFunctions;

	private Definitions bDefinitions = new Definitions();

	private Start start;
	private final Hashtable<Node, TLAType> typeTable = new Hashtable<Node, TLAType>();

	public Start expressionStart;

	/**
	 * Creates a B AST node for a TLA expression
	 * 
	 * @param moduleNode
	 * @param specAnalyser
	 */
	public BAstCreator(ModuleNode moduleNode, SpecAnalyser specAnalyser) {
		this.moduleNode = moduleNode;
		this.specAnalyser = specAnalyser;
		this.bMacroHandler = new BMacroHandler();
		this.predicateVsExpression = new PredicateVsExpression(moduleNode);
		this.recursiveFunctionHandler = new RecursiveFunctionHandler(
				specAnalyser);

		ExprNode expr = moduleNode.getOpDefs()[moduleNode.getOpDefs().length - 1]
				.getBody();
		if (expressionIsAPredicate(expr)) {
			APredicateParseUnit predicateParseUnit = new APredicateParseUnit();
			predicateParseUnit.setPredicate(visitExprNodePredicate(expr));
			expressionStart = new Start(predicateParseUnit, new EOF());
		} else {
			AExpressionParseUnit expressionParseUnit = new AExpressionParseUnit();
			expressionParseUnit.setExpression(visitExprNodeExpression(expr));
			expressionStart = new Start(expressionParseUnit, new EOF());
		}
	}

	private boolean expressionIsAPredicate(ExprNode expr) {
		if (expr.getKind() == OpApplKind) {
			OpApplNode opApplNode = (OpApplNode) expr;
			int kind = opApplNode.getOperator().getKind();
			if (kind == BuiltInKind) {
				int opcode = getOpCode(opApplNode.getOperator().getName());
				return OperatorTypes.tlaOperatorIsPredicate(opcode);
			} else if (kind == UserDefinedOpKind
					&& BBuiltInOPs.contains(opApplNode.getOperator().getName())) {
				int opcode = BBuiltInOPs.getOpcode(opApplNode.getOperator()
						.getName());
				return OperatorTypes.bbuiltInOperatorIsPredicate(opcode);
			}
		}
		return false;
	}

	public BAstCreator(ModuleNode moduleNode, ConfigfileEvaluator conEval,
			SpecAnalyser specAnalyser,
			UsedExternalFunctions usedExternalFunctions,
			PredicateVsExpression predicateVsExpression,
			BMacroHandler bMacroHandler,
			RecursiveFunctionHandler recursiveFunctionHandler) {
		this.predicateVsExpression = predicateVsExpression;
		this.bMacroHandler = bMacroHandler;
		this.recursiveFunctionHandler = recursiveFunctionHandler;

		this.conEval = conEval;
		this.moduleNode = moduleNode;
		this.specAnalyser = specAnalyser;
		this.usedExternalFunctions = usedExternalFunctions;

		if (conEval != null) {
			this.bConstants = conEval.getbConstantList();
		} else {
			this.bConstants = Arrays.asList(moduleNode.getConstantDecls());
		}

		machineClauseList = new ArrayList<PMachineClause>();

		AAbstractMachineParseUnit aAbstractMachineParseUnit = new AAbstractMachineParseUnit();
		aAbstractMachineParseUnit.setVariant(new AMachineMachineVariant());
		AMachineHeader machineHeader = new AMachineHeader();
		List<TIdentifierLiteral> headerName = createTIdentifierLiteral(getName(moduleNode));
		machineHeader.setName(headerName);
		aAbstractMachineParseUnit.setHeader(machineHeader);

		createSetsClause();
		createDefintionClause();
		createAbstractConstantsClause();
		createConstantsClause();
		createPropertyClause();
		createVariableClause();
		createInvariantClause();
		createInitClause();
		createOperationsClause();

		aAbstractMachineParseUnit.setMachineClauses(machineClauseList);
		start = new Start(aAbstractMachineParseUnit, new EOF());

	}

	private void createSetsClause() {
		if (conEval == null || conEval.getEnumerationSet() == null
				|| conEval.getEnumerationSet().size() == 0)
			return;
		ASetsMachineClause setsClause = new ASetsMachineClause();

		ArrayList<EnumType> printed = new ArrayList<EnumType>();
		OpDeclNode[] cons = moduleNode.getConstantDecls();
		for (int i = 0; i < cons.length; i++) {
			TLAType type = (TLAType) cons[i].getToolObject(TYPE_ID);

			EnumType e = null;
			if (type instanceof SetType) {
				if (((SetType) type).getSubType() instanceof EnumType) {
					e = (EnumType) ((SetType) type).getSubType();
					if (!printed.contains(e)) {
						printed.add(e);
					}
				}
			} else if ((type instanceof EnumType)) {
				e = (EnumType) type;
				if (!printed.contains(e)) {
					printed.add(e);
				}
			}
		}

		ArrayList<PSet> sets = new ArrayList<PSet>();
		for (int i = 0; i < printed.size(); i++) {
			AEnumeratedSetSet eSet = new AEnumeratedSetSet();
			printed.get(i).id = i + 1;
			eSet.setIdentifier(createTIdentifierLiteral("ENUM" + (i + 1)));
			List<PExpression> list = new ArrayList<PExpression>();
			for (Iterator<String> iterator = printed.get(i).modelvalues
					.iterator(); iterator.hasNext();) {
				list.add(createIdentifierNode(iterator.next()));
			}
			eSet.setElements(list);
			sets.add(eSet);
		}
		setsClause.setSetDefinitions(sets);
		machineClauseList.add(setsClause);

	}

	private void createDefintionClause() {
		ArrayList<OpDefNode> bDefs = new ArrayList<OpDefNode>();
		for (int i = 0; i < moduleNode.getOpDefs().length; i++) {
			OpDefNode def = moduleNode.getOpDefs()[i];
			if (specAnalyser.getBDefinitions().contains(def)) {
				if (conEval != null
						&& conEval.getConstantOverrideTable()
								.containsValue(def)) {
					continue;
				}
				if (def.getOriginallyDefinedInModuleNode().getName().toString()
						.equals("MC")) {
					continue;
				}

				bDefs.add(def);
			}

		}

		List<PDefinition> defs = new ArrayList<PDefinition>();

		Set<EXTERNAL_FUNCTIONS> set = usedExternalFunctions
				.getUsedExternalFunctions();
		defs.addAll(createDefinitionsForExternalFunctions(set));

		for (OpDefNode opDefNode : bDefs) {
			List<PExpression> list = new ArrayList<PExpression>();
			for (int i = 0; i < opDefNode.getParams().length; i++) {
				FormalParamNode p = opDefNode.getParams()[i];
				list.add(createIdentifierNode(p));
			}
			// TLAType type = (TLAType) opDefNode.getToolObject(TYPE_ID);
			// if (opDefNode.level == 2 || type instanceof BoolType) {
			if (predicateVsExpression.getDefinitionType(opDefNode) == DefinitionType.PREDICATE) {
				APredicateDefinitionDefinition d = new APredicateDefinitionDefinition();
				d.setName(new TDefLiteralPredicate(getName(opDefNode)));
				d.setParameters(list);
				d.setRhs(visitExprNodePredicate(opDefNode.getBody()));
				defs.add(d);
			} else {
				AExpressionDefinitionDefinition d = new AExpressionDefinitionDefinition();
				d.setName(new TIdentifierLiteral(getName(opDefNode)));

				d.setParameters(list);
				d.setRhs(visitExprNodeExpression(opDefNode.getBody()));
				defs.add(d);
			}

		}

		if (defs.size() > 0) {
			ADefinitionsMachineClause defClause = new ADefinitionsMachineClause();
			defClause.setDefinitions(defs);
			machineClauseList.add(defClause);
			for (PDefinition def : defs) {
				if (def instanceof AExpressionDefinitionDefinition) {
					bDefinitions.addDefinition(
							(AExpressionDefinitionDefinition) def,
							Definitions.Type.Expression);
				} else if (def instanceof APredicateDefinitionDefinition) {
					bDefinitions.addDefinition(
							(APredicateDefinitionDefinition) def,
							Definitions.Type.Predicate);
				} else {
					bDefinitions.addDefinition(
							(ASubstitutionDefinitionDefinition) def,
							Definitions.Type.Substitution);
				}
			}
		}

	}

	private ArrayList<PDefinition> createDefinitionsForExternalFunctions(
			Set<EXTERNAL_FUNCTIONS> set) {
		ArrayList<PDefinition> list = new ArrayList<PDefinition>();

		if (set.contains(UsedExternalFunctions.EXTERNAL_FUNCTIONS.CHOOSE)) {
			AExpressionDefinitionDefinition def1 = new AExpressionDefinitionDefinition();
			def1.setName(new TIdentifierLiteral("CHOOSE"));
			def1.setParameters(createIdentifierList("X"));
			def1.setRhs(new AStringExpression(new TStringLiteral(
					"a member of X")));
			list.add(def1);
			AExpressionDefinitionDefinition def2 = new AExpressionDefinitionDefinition();
			def2.setName(new TIdentifierLiteral("EXTERNAL_FUNCTION_CHOOSE"));
			def2.setParameters(createIdentifierList("T"));
			ATotalFunctionExpression total = new ATotalFunctionExpression();
			total.setLeft(new APowSubsetExpression(createIdentifierNode("T")));
			total.setRight(createIdentifierNode("T"));
			def2.setRhs(total);
			list.add(def2);
		}
		if (set.contains(UsedExternalFunctions.EXTERNAL_FUNCTIONS.ASSERT)) {
			APredicateDefinitionDefinition def1 = new APredicateDefinitionDefinition();
			def1.setName(new TDefLiteralPredicate("ASSERT_TRUE"));
			ArrayList<PExpression> params = new ArrayList<PExpression>();
			params.add(createIdentifierNode("P"));
			params.add(createIdentifierNode("Msg"));
			def1.setParameters(params);
			def1.setRhs(new AEqualPredicate(new AIntegerExpression(
					new TIntegerLiteral("1")), new AIntegerExpression(
					new TIntegerLiteral("1"))));
			list.add(def1);

			AExpressionDefinitionDefinition def2 = new AExpressionDefinitionDefinition();
			def2.setName(new TIdentifierLiteral(
					"EXTERNAL_PREDICATE_ASSERT_TRUE"));
			def2.setParameters(new ArrayList<PExpression>());
			AMultOrCartExpression cart = new AMultOrCartExpression();
			cart.setLeft(new ABoolSetExpression());
			cart.setRight(new AStringSetExpression());
			def2.setRhs(cart);
			list.add(def2);
		}
		return list;
	}

	private void createOperationsClause() {
		ArrayList<BOperation> bOperations = specAnalyser.getBOperations();
		if (bOperations == null || bOperations.size() == 0) {
			return;
		}

		List<POperation> opList = new ArrayList<POperation>();
		for (int i = 0; i < bOperations.size(); i++) {
			BOperation op = bOperations.get(i);

			String defName = op.getName();

			List<PExpression> paramList = new ArrayList<PExpression>();
			ArrayList<PPredicate> whereList = new ArrayList<PPredicate>();
			for (int j = 0; j < op.getFormalParams().size(); j++) {
				paramList
						.add(createIdentifierNode(op.getFormalParams().get(j)));
			}
			for (int j = 0; j < op.getExistQuans().size(); j++) {
				OpApplNode o = op.getExistQuans().get(j);
				whereList.add(visitBoundsOfLocalVariables(o));
			}

			AOperation operation = new AOperation();
			operation.setOpName(createTIdentifierLiteral(defName));
			operation.setParameters(paramList);
			operation.setReturnValues(new ArrayList<PExpression>());

			AAnySubstitution any = new AAnySubstitution();
			OpDeclNode[] vars = moduleNode.getVariableDecls();
			List<PExpression> anyParams = new ArrayList<PExpression>();
			for (int j = 0; j < vars.length; j++) {
				String varName = getName(vars[j]);
				String nextName = varName + "_n";
				if (op.getUnchangedVariables().contains(varName))
					continue;
				anyParams.add(createIdentifierNode(nextName));

				AMemberPredicate member = new AMemberPredicate();
				member.setLeft(createIdentifierNode(nextName));
				TLAType t = (TLAType) vars[j].getToolObject(TYPE_ID);
				member.setRight(t.getBNode());
				whereList.add(member);
			}
			any.setIdentifiers(anyParams);

			PPredicate body = null;
			if (op.getNode() instanceof OpApplNode) {
				OpApplNode opApplNode = (OpApplNode) op.getNode();
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
					body = visitExprNodePredicate(def.getBody());
				}
			}
			if (body == null) {
				body = visitExprOrOpArgNodePredicate(op.getNode());
			}
			whereList.add(body);
			any.setWhere(createConjunction(whereList));

			List<PExpression> varList = new ArrayList<PExpression>();
			List<PExpression> valueList = new ArrayList<PExpression>();
			for (int j = 0; j < vars.length; j++) {
				String varName = getName(vars[j]);
				if (op.getUnchangedVariables().contains(varName))
					continue;
				varList.add(createIdentifierNode(vars[j]));

				valueList.add(createIdentifierNode(varName + "_n"));
			}
			AAssignSubstitution assign = new AAssignSubstitution(varList,
					valueList);
			any.setThen(assign);
			operation.setOperationBody(any);
			// opList.add(operation);

			opList.add(op.getBOperation(this));
		}

		AOperationsMachineClause opClause = new AOperationsMachineClause(opList);
		machineClauseList.add(opClause);
	}

	private void createInitClause() {
		OpDeclNode[] vars = moduleNode.getVariableDecls();
		if (vars.length == 0)
			return;
		List<PExpression> varList = new ArrayList<PExpression>();
		for (int i = 0; i < vars.length; i++) {
			varList.add(createIdentifierNode(vars[i]));
		}
		ABecomesSuchSubstitution becomes = new ABecomesSuchSubstitution();
		becomes.setIdentifiers(varList);

		List<PPredicate> predList = new ArrayList<PPredicate>();
		for (ExprNode node : specAnalyser.getInits()) {
			predList.add(visitExprNodePredicate(node));
		}
		becomes.setPredicate(createConjunction(predList));
		AInitialisationMachineClause initClause = new AInitialisationMachineClause(
				becomes);
		machineClauseList.add(initClause);
	}

	private void createVariableClause() {
		List<OpDeclNode> bVariables = Arrays.asList(moduleNode
				.getVariableDecls());
		if (bVariables.size() > 0) {
			List<PExpression> list = new ArrayList<PExpression>();
			for (OpDeclNode opDeclNode : bVariables) {
				AIdentifierExpression id = new AIdentifierExpression(
						createTIdentifierLiteral(getName(opDeclNode)));
				list.add(id);
				TLAType type = (TLAType) opDeclNode.getToolObject(TYPE_ID);
				typeTable.put(id, type);
			}
			AVariablesMachineClause varClause = new AVariablesMachineClause(
					list);
			machineClauseList.add(varClause);
		}
	}

	private void createAbstractConstantsClause() {
		List<PExpression> constantsList = new ArrayList<PExpression>();

		for (RecursiveDefinition recDef : specAnalyser
				.getRecursiveDefinitions()) {
			AIdentifierExpression id = new AIdentifierExpression(
					createTIdentifierLiteral(getName(recDef.getOpDefNode())));
			constantsList.add(id);
			TLAType type = (TLAType) recDef.getOpDefNode().getToolObject(
					TYPE_ID);
			typeTable.put(id, type);
		}

		for (OpDefNode recFunc : specAnalyser.getRecursiveFunctions()) {
			AIdentifierExpression id = new AIdentifierExpression(
					createTIdentifierLiteral(getName(recFunc)));
			constantsList.add(id);
			TLAType type = (TLAType) recFunc.getToolObject(TYPE_ID);
			typeTable.put(id, type);
		}

		if (constantsList.size() > 0) {
			AAbstractConstantsMachineClause abstractConstantsClause = new AAbstractConstantsMachineClause(
					constantsList);
			machineClauseList.add(abstractConstantsClause);
		}
	}

	private void createConstantsClause() {
		List<OpDeclNode> bConstants;
		if (conEval != null) {
			bConstants = conEval.getbConstantList();
		} else {
			bConstants = Arrays.asList(moduleNode.getConstantDecls());
		}

		List<PExpression> constantsList = new ArrayList<PExpression>();
		for (OpDeclNode opDeclNode : bConstants) {
			AIdentifierExpression id = new AIdentifierExpression(
					createTIdentifierLiteral(getName(opDeclNode)));
			constantsList.add(id);
			TLAType type = (TLAType) opDeclNode.getToolObject(TYPE_ID);
			typeTable.put(id, type);
		}
		if (constantsList.size() > 0) {
			AConstantsMachineClause constantsClause = new AConstantsMachineClause(
					constantsList);
			machineClauseList.add(constantsClause);
		}
	}

	public AIdentifierExpression createIdentifierNode(SymbolNode symbolNode) {
		if (bMacroHandler.containsSymbolNode(symbolNode)) {
			return createIdentifierNode(bMacroHandler.getNewName(symbolNode));
		} else {
			return createIdentifierNode(symbolNode.getName().toString());
		}
	}

	private void createPropertyClause() {
		List<PPredicate> propertiesList = new ArrayList<PPredicate>();

		propertiesList.addAll(evalRecursiveDefinitions());

		propertiesList.addAll(evalRecursiveFunctions());

		for (OpDeclNode con : bConstants) {
			if (conEval != null
					&& conEval.getConstantAssignments().containsKey(con)
					&& bConstants.contains(con)) {
				ValueObj v = conEval.getConstantAssignments().get(con);
				TLAType t = v.getType();
				boolean isEnum = false;
				if (t instanceof SetType) {
					TLAType sub = ((SetType) t).getSubType();
					if (sub instanceof EnumType) {
						EnumType en = (EnumType) sub;
						SetEnumValue set = (SetEnumValue) v.getValue();
						if (set.elems.size() == en.modelvalues.size()) {
							isEnum = true;
						}
					}
				}
				if (isEnum) {
					AEqualPredicate equal = new AEqualPredicate();
					equal.setLeft(createIdentifierNode(con));
					equal.setRight(createIdentifierNode(((SetType) t)
							.getSubType().toString()));
					propertiesList.add(equal);
				} else {
					AEqualPredicate equal = new AEqualPredicate();
					equal.setLeft(createIdentifierNode(con));
					Value tlcValue = v.getValue();
					equal.setRight(createTLCValue(tlcValue));
					propertiesList.add(equal);
				}
			} else {
				AMemberPredicate member = new AMemberPredicate();
				member.setLeft(createIdentifierNode(con));
				TLAType t = (TLAType) con.getToolObject(TYPE_ID);
				member.setRight(t.getBNode());
				propertiesList.add(member);
			}
		}

		if (conEval != null) {
			Iterator<Entry<OpDeclNode, OpDefNode>> iter = conEval
					.getConstantOverrideTable().entrySet().iterator();
			while (iter.hasNext()) {
				Entry<OpDeclNode, OpDefNode> entry = iter.next();
				OpDeclNode con = entry.getKey();
				OpDefNode generatedDef = entry.getValue();
				OpDefNode def = null;
				try {
					OpApplNode opApplNode = (OpApplNode) generatedDef.getBody();
					if (opApplNode.getKind() == UserDefinedOpKind) {
						def = (OpDefNode) opApplNode.getOperator();
					} else {
						def = generatedDef;
					}
				} catch (ClassCastException e) {
					def = generatedDef;
				}

				AEqualPredicate equal = new AEqualPredicate();
				equal.setLeft(createIdentifierNode(con));
				equal.setRight(visitExprNodeExpression(def.getBody()));
				propertiesList.add(equal);
			}
		}

		AssumeNode[] assumes = moduleNode.getAssumptions();
		for (AssumeNode assumeNode : assumes) {
			propertiesList.add(visitAssumeNode(assumeNode));
		}

		if (propertiesList.size() > 0) {
			APropertiesMachineClause propertiesClause = new APropertiesMachineClause();
			propertiesClause.setPredicates(createConjunction(propertiesList));

			machineClauseList.add(propertiesClause);
		}
	}

	private List<PPredicate> evalRecursiveFunctions() {
		List<PPredicate> propertiesList = new ArrayList<PPredicate>();
		for (OpDefNode def : specAnalyser.getRecursiveFunctions()) {
			AEqualPredicate equals = new AEqualPredicate(
					createIdentifierNode(def),
					visitExprNodeExpression(def.getBody()));
			propertiesList.add(equals);
		}

		return propertiesList;
	}

	private List<PPredicate> evalRecursiveDefinitions() {
		List<PPredicate> propertiesList = new ArrayList<PPredicate>();

		for (RecursiveDefinition recDef : specAnalyser
				.getRecursiveDefinitions()) {
			OpDefNode def = recDef.getOpDefNode();
			// TLAType t = (TLAType) def.getToolObject(TYPE_ID);
			// OpApplNode ifThenElse = recDef.getIfThenElse();
			FormalParamNode[] params = def.getParams();
			ArrayList<PExpression> paramList1 = new ArrayList<PExpression>();
			ArrayList<PPredicate> typeList = new ArrayList<PPredicate>();
			// ArrayList<PExpression> paramList2 = new ArrayList<PExpression>();
			for (FormalParamNode p : params) {
				paramList1.add(createIdentifierNode(p));
				// paramList2.add(createIdentifierNode(p.getName().toString()));
				TLAType paramType = (TLAType) p.getToolObject(TYPE_ID);
				AEqualPredicate equal = new AEqualPredicate(
						createIdentifierNode(p), paramType.getBNode());
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

			AEqualPredicate equals = new AEqualPredicate(
					createIdentifierNode(def), lambda1);
			propertiesList.add(equals);
		}

		return propertiesList;
	}

	private PExpression createTLCValue(Value tlcValue) {
		switch (tlcValue.getKind()) {
		case INTVALUE:
			return new AIntegerExpression(new TIntegerLiteral(
					tlcValue.toString()));

		case SETENUMVALUE: {
			SetEnumValue s = (SetEnumValue) tlcValue;
			ArrayList<PExpression> list = new ArrayList<PExpression>();
			for (int i = 0; i < s.elems.size(); i++) {
				Value v = s.elems.elementAt(i);
				list.add(createTLCValue(v));
			}
			return new ASetExtensionExpression(list);
		}
		case MODELVALUE: {
			ModelValue m = (ModelValue) tlcValue;
			return createIdentifierNode(m.toString());
		}

		case STRINGVALUE: {
			StringValue stringValue = (StringValue) tlcValue;
			return new AStringExpression(new TStringLiteral(stringValue
					.getVal().toString()));

		}
		default:
			throw new NotImplementedException(
					"TLC value in configuration file: " + tlcValue.getClass());
		}
	}

	private void createInvariantClause() {
		OpDeclNode[] vars = moduleNode.getVariableDecls();

		List<PPredicate> predList = new ArrayList<PPredicate>();
		for (int i = 0; i < vars.length; i++) {
			TLAType varType = (TLAType) vars[i].getToolObject(TYPE_ID);

			AMemberPredicate member = new AMemberPredicate();
			member.setLeft(createIdentifierNode(vars[i]));
			member.setRight(varType.getBNode());

			predList.add(member);
		}

		for (OpDefNode def : specAnalyser.getInvariants()) {
			if (def.getOriginallyDefinedInModuleNode().getName().toString()
					.equals("MC")) {
				predList.add(visitExprNodePredicate(def.getBody()));
			} else {
				if (predicateVsExpression.getDefinitionType(def) == DefinitionType.PREDICATE) {
					ADefinitionPredicate defPred = new ADefinitionPredicate();
					defPred.setDefLiteral(new TDefLiteralPredicate(getName(def)));
					predList.add(defPred);
				} else {
					ADefinitionExpression defExpr = new ADefinitionExpression();
					defExpr.setDefLiteral(new TIdentifierLiteral(getName(def)));
					predList.add(new AEqualPredicate(defExpr,
							new ABooleanTrueExpression()));
				}

			}
		}

		if (predList.size() > 0) {
			AInvariantMachineClause invClause = new AInvariantMachineClause(
					createConjunction(predList));
			machineClauseList.add(invClause);
		}

	}

	private PPredicate visitAssumeNode(AssumeNode assumeNode) {
		return visitExprNodePredicate(assumeNode.getAssume());
	}

	public PPredicate visitExprNodePredicate(ExprNode n) {
		switch (n.getKind()) {
		case OpApplKind:
			return visitOpApplNodePredicate((OpApplNode) n);

		case LetInKind: {
			LetInNode letInNode = (LetInNode) n;
			return visitExprNodePredicate(letInNode.getBody());
		}

		case NumeralKind: {
			throw new RuntimeException();
		}

		}

		throw new RuntimeException(n.getClass().toString());
	}

	private PExpression visitExprNodeExpression(ExprNode n) {

		switch (n.getKind()) {

		case OpApplKind:
			return visitOpApplNodeExpression((OpApplNode) n);

		case NumeralKind: {
			String number = String.valueOf(((NumeralNode) n).val());
			return new AIntegerExpression(new TIntegerLiteral(number));
		}

		case StringKind: {
			StringNode s = (StringNode) n;
			return new AStringExpression(new TStringLiteral(s.getRep()
					.toString()));
		}

		case AtNodeKind: { // @
			AtNode at = (AtNode) n;
			TLAType type = (TLAType) at.getExceptRef().getToolObject(TYPE_ID);
			OpApplNode seq = at.getAtModifier();
			LinkedList<ExprOrOpArgNode> list = new LinkedList<ExprOrOpArgNode>();
			for (int j = 0; j < seq.getArgs().length; j++) {
				list.add(seq.getArgs()[j]);
			}
			// PExpression base = visitExprNodeExpression(at.getAtBase());
			PExpression base = (PExpression) at.getExceptComponentRef()
					.getToolObject(EXCEPT_BASE);

			return evalAtNode(list, type, (PExpression) base.clone());
		}

		case LetInKind: {
			LetInNode letInNode = (LetInNode) n;
			return visitExprNodeExpression(letInNode.getBody());
		}

		}

		throw new RuntimeException(n.getClass().toString());
	}

	private PExpression evalAtNode(LinkedList<ExprOrOpArgNode> list,
			TLAType type, PExpression base) {
		if (list.size() == 0) {
			return base;
		}

		if (type instanceof FunctionType) {
			FunctionType funcType = (FunctionType) type;
			PExpression param = visitExprOrOpArgNodeExpression(list.poll());
			List<PExpression> params = new ArrayList<PExpression>();
			params.add(param);

			AFunctionExpression funCall = new AFunctionExpression();
			funCall.setIdentifier(base);
			funCall.setParameters(params);
			return evalAtNode(list, funcType.getRange(), funCall);
		} else {
			StructType structType = (StructType) type;
			ARecordFieldExpression select = new ARecordFieldExpression();
			select.setRecord(base);
			StringNode stringNode = (StringNode) list.poll();
			String fieldName = stringNode.getRep().toString();
			select.setIdentifier(createIdentifierNode(fieldName)); // TODO
																	// renamed
			return evalAtNode(list, structType.getType(fieldName), select);
		}
	}

	private PPredicate visitOpApplNodePredicate(OpApplNode n) {
		switch (n.getOperator().getKind()) {
		case VariableDeclKind:
		case ConstantDeclKind:
		case FormalParamKind: {
			return new AEqualPredicate(createIdentifierNode(n.getOperator()),
					new ABooleanTrueExpression());
		}
		case BuiltInKind:
			return visitBuiltInKindPredicate(n);

		case UserDefinedOpKind: {
			return visitUserdefinedOpPredicate(n);
		}

		}
		throw new RuntimeException(n.getOperator().getName().toString());
	}

	private PExpression visitOpApplNodeExpression(OpApplNode n) {
		switch (n.getOperator().getKind()) {
		case ConstantDeclKind: {
			return createIdentifierNode(n.getOperator());
		}
		case VariableDeclKind: {
			return createIdentifierNode(n.getOperator());
		}

		case FormalParamKind: {
			FormalParamNode param = (FormalParamNode) n.getOperator();
			ExprOrOpArgNode e = (ExprOrOpArgNode) param
					.getToolObject(SUBSTITUTE_PARAM);
			if (e != null) {
				return visitExprOrOpArgNodeExpression(e);
			}

			if (recursiveFunctionHandler.isRecursiveFunction(param)) {
				ArrayList<SymbolNode> list = recursiveFunctionHandler
						.getAdditionalParams(param);
				if (list.size() > 0) {
					AFunctionExpression call = new AFunctionExpression();
					call.setIdentifier(createIdentifierNode(param));
					ArrayList<PExpression> params = new ArrayList<PExpression>();
					for (SymbolNode symbolNode : list) {
						params.add(createIdentifierNode(symbolNode));
					}
					call.setParameters(params);
					return call;
				}
			}

			FormalParamNode[] tuple = (FormalParamNode[]) param
					.getToolObject(TUPLE);
			if (tuple != null) {
				if (tuple.length == 1) {
					AFunctionExpression functionCall = new AFunctionExpression();
					functionCall.setIdentifier(createIdentifierNode(n
							.getOperator()));
					List<PExpression> paramList = new ArrayList<PExpression>();
					paramList.add(new AIntegerExpression(new TIntegerLiteral(
							"1")));
					functionCall.setParameters(paramList);
					return functionCall;
				} else {

					StringBuilder sb = new StringBuilder();
					List<TLAType> typeList = new ArrayList<TLAType>();
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
					TupleType tupleType = new TupleType(typeList);
					PExpression id = createIdentifierNode(sb.toString());
					PExpression prj = createProjectionFunction(id, number,
							tupleType);
					return prj;
				}
			}
			return createIdentifierNode(n.getOperator());

		}

		case BuiltInKind:
			return visitBuiltInKindExpression(n);

		case UserDefinedOpKind: {
			return visitUserdefinedOpExpression(n);
		}
		}

		throw new RuntimeException(n.getOperator().getName().toString());
	}

	private PPredicate visitUserdefinedOpPredicate(OpApplNode n) {
		OpDefNode def = (OpDefNode) n.getOperator();
		if (BBuiltInOPs.contains(def.getName()) // Operator is a B built-in
												// operator
				&& STANDARD_MODULES.contains(def.getSource()
						.getOriginallyDefinedInModuleNode().getName()
						.toString())) {
			return visitBBuitInsPredicate(n);
		}

		if (specAnalyser.getRecursiveFunctions().contains(def)) {
			return new AEqualPredicate(createIdentifierNode(def),
					new ABooleanTrueExpression());
		}

		List<PExpression> params = new ArrayList<PExpression>();
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
	}

	private String getName(SymbolNode def) {
		return def.getName().toString();
	}

	private PExpression visitUserdefinedOpExpression(OpApplNode n) {
		OpDefNode def = (OpDefNode) n.getOperator();
		// Operator is a B built-in operator
		if (BBuiltInOPs.contains(def.getName())
				&& STANDARD_MODULES.contains(def.getSource()
						.getOriginallyDefinedInModuleNode().getName()
						.toString())) {
			return visitBBuitInsExpression(n);
		}

		if (specAnalyser.getRecursiveFunctions().contains(def)) {
			ArrayList<SymbolNode> list = recursiveFunctionHandler
					.getAdditionalParams(def);
			if (list.size() > 0) {
				AFunctionExpression call = new AFunctionExpression();
				call.setIdentifier(createIdentifierNode(def));
				ArrayList<PExpression> params = new ArrayList<PExpression>();
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
			List<PExpression> params = new ArrayList<PExpression>();
			for (int i = 0; i < n.getArgs().length; i++) {
				params.add(visitExprOrOpArgNodeExpression(n.getArgs()[i]));
			}

			if (conEval != null
					&& conEval.getConstantOverrideTable().containsValue(def)) {
				// used constants name instead of the definition overriding the
				// constant
				Iterator<Entry<OpDeclNode, OpDefNode>> iter = conEval
						.getConstantOverrideTable().entrySet().iterator();
				String name = null;
				while (iter.hasNext()) {
					Entry<OpDeclNode, OpDefNode> entry = iter.next();
					if (entry.getValue().equals(def)) {
						name = getName(entry.getKey());
					}
				}
				if (params.size() == 0) {
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
					defPred.setDefLiteral(new TDefLiteralPredicate(getName(n
							.getOperator())));
					defPred.setParameters(params);
					return new AConvertBoolExpression(defPred);
				} else {
					ADefinitionExpression defExpr = new ADefinitionExpression();
					defExpr.setDefLiteral(new TIdentifierLiteral(getName(n
							.getOperator())));
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
			PExpression result = visitExprNodeExpression(def.getBody());
			return result;
		}

	}

	private PPredicate visitBBuitInsPredicate(OpApplNode n) {
		switch (BBuiltInOPs.getOpcode(n.getOperator().getName())) {

		case B_OPCODE_lt: // <
			return new ALessPredicate(
					visitExprOrOpArgNodeExpression(n.getArgs()[0]),
					visitExprOrOpArgNodeExpression(n.getArgs()[1]));

		case B_OPCODE_gt: // >
			return new AGreaterPredicate(
					visitExprOrOpArgNodeExpression(n.getArgs()[0]),
					visitExprOrOpArgNodeExpression(n.getArgs()[1]));

		case B_OPCODE_leq: // <=
			return new ALessEqualPredicate(
					visitExprOrOpArgNodeExpression(n.getArgs()[0]),
					visitExprOrOpArgNodeExpression(n.getArgs()[1]));

		case B_OPCODE_geq: // >=
			return new AGreaterEqualPredicate(
					visitExprOrOpArgNodeExpression(n.getArgs()[0]),
					visitExprOrOpArgNodeExpression(n.getArgs()[1]));

		case B_OPCODE_finite: // IsFiniteSet({1,2,3})
		{
			AMemberPredicate member = new AMemberPredicate();
			member.setLeft(visitExprOrOpArgNodeExpression(n.getArgs()[0]));
			member.setRight(new AFinSubsetExpression(
					visitExprOrOpArgNodeExpression(n.getArgs()[0])));
			return member;
		}
		case B_OPCODE_true: // TRUE
			return new AEqualPredicate(new ABooleanTrueExpression(),
					new ABooleanTrueExpression());

		case B_OPCODE_false: // FALSE
			return new AEqualPredicate(new ABooleanFalseExpression(),
					new ABooleanTrueExpression());

		case B_OPCODE_assert: {
			ADefinitionPredicate pred = new ADefinitionPredicate();
			pred.setDefLiteral(new TDefLiteralPredicate("ASSERT_TRUE"));
			ArrayList<PExpression> list = new ArrayList<PExpression>();
			list.add(visitExprOrOpArgNodeExpression(n.getArgs()[0]));
			if (n.getArgs()[1] instanceof StringNode) {
				StringNode stringNode = (StringNode) n.getArgs()[1];
				list.add(new AStringExpression(new TStringLiteral(stringNode
						.getRep().toString())));
			} else {
				list.add(new AStringExpression(new TStringLiteral("Error")));
			}
			pred.setParameters(list);
			return pred;
		}

		}
		throw new RuntimeException(n.getOperator().getName().toString());
	}

	private PExpression visitBBuitInsExpression(OpApplNode n) {
		switch (BBuiltInOPs.getOpcode(n.getOperator().getName())) {

		case B_OPCODE_bool: // BOOLEAN
			return new ABoolSetExpression();

		case B_OPCODE_true: // TRUE
			return new ABooleanTrueExpression();
		case B_OPCODE_false: // FALSE
			return new ABooleanFalseExpression();

			/**********************************************************************
			 * Standard Module Naturals
			 **********************************************************************/
		case B_OPCODE_nat: // Nat
			return new ANaturalSetExpression();

		case B_OPCODE_plus: // +
			return new AAddExpression(
					visitExprOrOpArgNodeExpression(n.getArgs()[0]),
					visitExprOrOpArgNodeExpression(n.getArgs()[1]));

		case B_OPCODE_minus: // -
			return new AMinusOrSetSubtractExpression(
					visitExprOrOpArgNodeExpression(n.getArgs()[0]),
					visitExprOrOpArgNodeExpression(n.getArgs()[1]));

		case B_OPCODE_times: // *
			return new AMultOrCartExpression(
					visitExprOrOpArgNodeExpression(n.getArgs()[0]),
					visitExprOrOpArgNodeExpression(n.getArgs()[1]));

		case B_OPCODE_exp: // x^y
			return new APowerOfExpression(
					visitExprOrOpArgNodeExpression(n.getArgs()[0]),
					visitExprOrOpArgNodeExpression(n.getArgs()[1]));

		case B_OPCODE_lt: // <
			return new AConvertBoolExpression(new ALessPredicate(
					visitExprOrOpArgNodeExpression(n.getArgs()[0]),
					visitExprOrOpArgNodeExpression(n.getArgs()[1])));

		case B_OPCODE_gt: // >
			return new AConvertBoolExpression(new AGreaterPredicate(
					visitExprOrOpArgNodeExpression(n.getArgs()[0]),
					visitExprOrOpArgNodeExpression(n.getArgs()[1])));

		case B_OPCODE_leq: // <=
			return new AConvertBoolExpression(new ALessEqualPredicate(
					visitExprOrOpArgNodeExpression(n.getArgs()[0]),
					visitExprOrOpArgNodeExpression(n.getArgs()[1])));

		case B_OPCODE_geq: // >=
			return new AConvertBoolExpression(new AGreaterEqualPredicate(
					visitExprOrOpArgNodeExpression(n.getArgs()[0]),
					visitExprOrOpArgNodeExpression(n.getArgs()[1])));

		case B_OPCODE_mod: // modulo
		{
			PExpression f = visitExprOrOpArgNodeExpression(n.getArgs()[0]);
			PExpression s = visitExprOrOpArgNodeExpression(n.getArgs()[1]);
			PExpression f2 = visitExprOrOpArgNodeExpression(n.getArgs()[0]);
			PExpression s2 = visitExprOrOpArgNodeExpression(n.getArgs()[1]);

			ADivExpression div = new ADivExpression(f, s);
			AMultOrCartExpression mult = new AMultOrCartExpression(s2, div);
			AMinusOrSetSubtractExpression minus = new AMinusOrSetSubtractExpression(
					f2, mult);
			return minus;
		}

		case B_OPCODE_div: // /
			return new ADivExpression(
					visitExprOrOpArgNodeExpression(n.getArgs()[0]),
					visitExprOrOpArgNodeExpression(n.getArgs()[1]));

		case B_OPCODE_dotdot: // ..
			return new AIntervalExpression(
					visitExprOrOpArgNodeExpression(n.getArgs()[0]),
					visitExprOrOpArgNodeExpression(n.getArgs()[1]));

		case B_OPCODE_int: // Int
			return new AIntegerSetExpression();

		case B_OPCODE_uminus: // -x
			return new AUnaryMinusExpression(
					visitExprOrOpArgNodeExpression(n.getArgs()[0]));

		case B_OPCODE_card: // Cardinality
			return new ACardExpression(
					visitExprOrOpArgNodeExpression(n.getArgs()[0]));

		case B_OPCODE_finite: // IsFiniteSet({1,2,3})
		{
			AMemberPredicate member = new AMemberPredicate();
			member.setLeft(visitExprOrOpArgNodeExpression(n.getArgs()[0]));
			member.setRight(new AFinSubsetExpression(
					visitExprOrOpArgNodeExpression(n.getArgs()[0])));
			return new AConvertBoolExpression(member);
		}

		case B_OPCODE_string: // STRING
			return new AStringSetExpression();

			/**********************************************************************
			 * Standard Module Sequences
			 **********************************************************************/

		case B_OPCODE_seq: // Seq(S) - set of sequences
			return new ASeqExpression(
					visitExprOrOpArgNodeExpression(n.getArgs()[0]));

		case B_OPCODE_len: // length of the sequence
			return new ASizeExpression(
					visitExprOrOpArgNodeExpression(n.getArgs()[0]));

		case B_OPCODE_conc: // s \o s2 - concatenation of s and s2
			return new AConcatExpression(
					visitExprOrOpArgNodeExpression(n.getArgs()[0]),
					visitExprOrOpArgNodeExpression(n.getArgs()[1]));

		case B_OPCODE_append: // Append(s,x)
			return new AInsertTailExpression(
					visitExprOrOpArgNodeExpression(n.getArgs()[0]),
					visitExprOrOpArgNodeExpression(n.getArgs()[1]));

		case B_OPCODE_head: // Head(s)
			return new AFirstExpression(
					visitExprOrOpArgNodeExpression(n.getArgs()[0]));

		case B_OPCODE_tail: // Tail(s)
			return new ATailExpression(
					visitExprOrOpArgNodeExpression(n.getArgs()[0]));

		case B_OPCODE_subseq: { // SubSeq(s,a,b)
			// %p.(p : 1..(b-a+1)| s(p+a-1))
			ALambdaExpression lambda = new ALambdaExpression();
			lambda.setIdentifiers(createIdentifierList("t_"));
			AMemberPredicate member = new AMemberPredicate();
			member.setLeft(createIdentifierNode("t_"));
			AIntervalExpression interval = new AIntervalExpression();
			interval.setLeftBorder(new AIntegerExpression(new TIntegerLiteral(
					"1")));
			AMinusOrSetSubtractExpression minus = new AMinusOrSetSubtractExpression();
			minus.setLeft(visitExprOrOpArgNodeExpression(n.getArgs()[2]));
			minus.setRight(visitExprOrOpArgNodeExpression(n.getArgs()[1]));
			AAddExpression add = new AAddExpression();
			add.setLeft(minus);
			add.setRight(new AIntegerExpression(new TIntegerLiteral("1")));
			interval.setRightBorder(add);
			member.setRight(interval);
			lambda.setPredicate(member);
			AAddExpression add2 = new AAddExpression();
			add2.setLeft(createIdentifierNode("t_"));
			add2.setRight(visitExprOrOpArgNodeExpression(n.getArgs()[1]));
			AMinusOrSetSubtractExpression minus2 = new AMinusOrSetSubtractExpression();
			minus2.setLeft(add2);
			minus2.setRight(new AIntegerExpression(new TIntegerLiteral("1")));
			ArrayList<PExpression> params = new ArrayList<PExpression>();
			params.add(minus2);
			AFunctionExpression func = new AFunctionExpression();
			func.setIdentifier(visitExprOrOpArgNodeExpression(n.getArgs()[0]));
			func.setParameters(params);
			lambda.setExpression(func);
			return lambda;

			// ARestrictFrontExpression restrictFront = new
			// ARestrictFrontExpression();
			// restrictFront
			// .setLeft(visitExprOrOpArgNodeExpression(n.getArgs()[0]));
			// restrictFront
			// .setRight(visitExprOrOpArgNodeExpression(n.getArgs()[2]));
			//
			// ARestrictTailExpression restrictTail = new
			// ARestrictTailExpression();
			// restrictTail.setLeft(restrictFront);
			// restrictTail
			// .setRight(visitExprOrOpArgNodeExpression(n.getArgs()[1]));
			// return restrictTail;
		}

		case B_OPCODE_assert: {
			ADefinitionPredicate pred = new ADefinitionPredicate();
			pred.setDefLiteral(new TDefLiteralPredicate("ASSERT_TRUE"));
			ArrayList<PExpression> list = new ArrayList<PExpression>();
			list.add(visitExprOrOpArgNodeExpression(n.getArgs()[0]));
			list.add(new AStringExpression(new TStringLiteral("Error")));
			pred.setParameters(list);
			return new AConvertBoolExpression(pred);
		}

		case B_OPCODE_setsum: {
			AGeneralSumExpression sum = new AGeneralSumExpression();
			String variableName = "t_"; // TODO unused identifier name
			List<PExpression> exprList = createPexpressionList(createIdentifierNode(variableName));
			sum.setIdentifiers(exprList);
			AMemberPredicate memberPredicate = new AMemberPredicate();
			memberPredicate.setLeft(createIdentifierNode(variableName));
			memberPredicate
					.setRight(visitExprOrOpArgNodeExpression(n.getArgs()[0]));
			sum.setPredicates(memberPredicate);
			sum.setExpression(createIdentifierNode(variableName));
			return sum;
		}

		}
		throw new RuntimeException(n.getOperator().getName().toString());
	}

	private PExpression visitBuiltInKindExpression(OpApplNode n) {
		switch (getOpCode(n.getOperator().getName())) {

		case OPCODE_land: // \land
		{
			AConjunctPredicate conjunction = new AConjunctPredicate();
			conjunction.setLeft(visitExprOrOpArgNodePredicate(n.getArgs()[0]));
			conjunction.setRight(visitExprOrOpArgNodePredicate(n.getArgs()[1]));
			return new AConvertBoolExpression(conjunction);
		}

		case OPCODE_cl: // $ConjList
		{
			List<PPredicate> list = new ArrayList<PPredicate>();
			for (int i = 0; i < n.getArgs().length; i++) {
				list.add(visitExprOrOpArgNodePredicate(n.getArgs()[i]));
			}
			return new AConvertBoolExpression(createConjunction(list));
		}

		case OPCODE_dl: // $DisjList
		{
			List<PPredicate> list = new ArrayList<PPredicate>();
			for (int i = 0; i < n.getArgs().length; i++) {
				list.add(visitExprOrOpArgNodePredicate(n.getArgs()[i]));
			}
			return new AConvertBoolExpression(createDisjunction(list));
		}

		case OPCODE_lor: // \/
		{
			ADisjunctPredicate disjunction = new ADisjunctPredicate();
			disjunction.setLeft(visitExprOrOpArgNodePredicate(n.getArgs()[0]));
			disjunction.setRight(visitExprOrOpArgNodePredicate(n.getArgs()[1]));
			return new AConvertBoolExpression(disjunction);
		}

		case OPCODE_lnot: // \lnot
			return new AConvertBoolExpression(new ANegationPredicate(
					visitExprOrOpArgNodePredicate(n.getArgs()[0])));

		case OPCODE_in: // \in
		{
			AMemberPredicate memberPredicate = new AMemberPredicate();
			memberPredicate
					.setLeft(visitExprOrOpArgNodeExpression(n.getArgs()[0]));
			memberPredicate
					.setRight(visitExprOrOpArgNodeExpression(n.getArgs()[1]));
			return new AConvertBoolExpression(memberPredicate);
		}

		case OPCODE_notin: // \notin
		{
			ANotMemberPredicate notMemberPredicate = new ANotMemberPredicate();
			notMemberPredicate.setLeft(visitExprOrOpArgNodeExpression(n
					.getArgs()[0]));
			notMemberPredicate.setRight(visitExprOrOpArgNodeExpression(n
					.getArgs()[1]));
			return new AConvertBoolExpression(notMemberPredicate);
		}

		case OPCODE_eq: { // =
			AEqualPredicate equal = new AEqualPredicate();
			equal.setLeft(visitExprOrOpArgNodeExpression(n.getArgs()[0]));
			equal.setRight(visitExprOrOpArgNodeExpression(n.getArgs()[1]));
			return new AConvertBoolExpression(equal);
		}

		case OPCODE_noteq: // /=
		{
			ANotEqualPredicate notEqual = new ANotEqualPredicate();
			notEqual.setLeft(visitExprOrOpArgNodeExpression(n.getArgs()[0]));
			notEqual.setRight(visitExprOrOpArgNodeExpression(n.getArgs()[1]));
			return new AConvertBoolExpression(notEqual);
		}

		/**********************************************************************
		 * Set Operators
		 **********************************************************************/

		case OPCODE_se: // SetEnumeration {..}
		{
			if (n.getArgs().length == 0) {
				return new AEmptySetExpression();
			} else {
				List<PExpression> list = new ArrayList<PExpression>();

				for (int i = 0; i < n.getArgs().length; i++) {
					list.add(visitExprOrOpArgNodeExpression(n.getArgs()[i]));
				}
				return new ASetExtensionExpression(list);
			}
		}

		case 0: {
			return visitBBuitInsExpression(n);
		}

		case OPCODE_setdiff: // set difference
		{
			AMinusOrSetSubtractExpression minus = new AMinusOrSetSubtractExpression();
			minus.setLeft(visitExprOrOpArgNodeExpression(n.getArgs()[0]));
			minus.setRight(visitExprOrOpArgNodeExpression(n.getArgs()[1]));
			return minus;
		}

		case OPCODE_cup: // set union
		{
			AUnionExpression union = new AUnionExpression();
			union.setLeft(visitExprOrOpArgNodeExpression(n.getArgs()[0]));
			union.setRight(visitExprOrOpArgNodeExpression(n.getArgs()[1]));
			return union;
		}

		case OPCODE_cap: // set intersection
		{
			AIntersectionExpression inter = new AIntersectionExpression();
			inter.setLeft(visitExprOrOpArgNodeExpression(n.getArgs()[0]));
			inter.setRight(visitExprOrOpArgNodeExpression(n.getArgs()[1]));
			return inter;
		}

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
			List<PExpression> list = new ArrayList<PExpression>();
			for (int i = 0; i < params[0].length; i++) {
				FormalParamNode p = params[0][i];
				list.add(createIdentifierNode(p));
			}
			AComprehensionSetExpression compre = new AComprehensionSetExpression();
			compre.setIdentifiers(list);
			PPredicate typing = visitBoundsOfFunctionsVariables(n);
			AConjunctPredicate conj = new AConjunctPredicate(typing,
					visitExprOrOpArgNodePredicate(n.getArgs()[0]));
			compre.setPredicates(conj);
			return compre;
		}

		case OPCODE_soa: { // $SetOfAll Represents {e : p1 \in S, p2,p3 \in S2}
			FormalParamNode[][] params = n.getBdedQuantSymbolLists();
			List<PExpression> idList = createListOfIdentifier(params);
			List<PPredicate> predList = new ArrayList<PPredicate>();

			predList.add(visitBoundsOfLocalVariables(n));
			final String nameOfTempVariable = "t_";
			AEqualPredicate equals = new AEqualPredicate();
			equals.setLeft(createIdentifierNode(nameOfTempVariable));
			equals.setRight(visitExprOrOpArgNodeExpression(n.getArgs()[0]));
			predList.add(equals);
			AExistsPredicate exist = new AExistsPredicate();
			exist.setIdentifiers(idList);
			exist.setPredicate(createConjunction(predList));

			AComprehensionSetExpression compre = new AComprehensionSetExpression();
			List<PExpression> tList = new ArrayList<PExpression>();
			tList.add(createIdentifierNode(nameOfTempVariable));
			compre.setIdentifiers(tList);
			compre.setPredicates(exist);
			return compre;
		}

		case OPCODE_nrfs:
		case OPCODE_fc: // Represents [x \in S |-> e].
		case OPCODE_rfs: {
			FormalParamNode[][] params = n.getBdedQuantSymbolLists();
			List<PExpression> idList = new ArrayList<PExpression>();
			for (int i = 0; i < params.length; i++) {
				for (int j = 0; j < params[i].length; j++) {
					FormalParamNode p = params[i][j];
					idList.add(createIdentifierNode(p));
				}
			}
			boolean[] isTuple = n.isBdedQuantATuple();
			ALambdaExpression lambda = new ALambdaExpression();
			List<PExpression> idList2 = new ArrayList<PExpression>();
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

				ArrayList<SymbolNode> externParams = recursiveFunctionHandler
						.getAdditionalParams(n);
				if (externParams.size() > 0) {
					ALambdaExpression lambda2 = new ALambdaExpression();
					ArrayList<PExpression> shiftedParams = new ArrayList<PExpression>();
					List<PPredicate> predList2 = new ArrayList<PPredicate>();
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
			if (t != null && t instanceof TupleType) {
				NumeralNode num = (NumeralNode) n.getArgs()[1];
				int field = num.val();
				PExpression pair = visitExprOrOpArgNodeExpression(n.getArgs()[0]);
				return createProjectionFunction(pair, field, t);
			} else {
				AFunctionExpression func = new AFunctionExpression();
				func.setIdentifier(visitExprOrOpArgNodeExpression(n.getArgs()[0]));
				List<PExpression> paramList = new ArrayList<PExpression>();

				ExprOrOpArgNode dom = n.getArgs()[1];
				if (dom instanceof OpApplNode
						&& ((OpApplNode) dom).getOperator().getName()
								.toString().equals("$Tuple")) {
					OpApplNode domOpAppl = (OpApplNode) dom;
					if (domOpAppl.getArgs().length == 1) {
						List<PExpression> list = new ArrayList<PExpression>();
						list.add(visitExprOrOpArgNodeExpression(domOpAppl
								.getArgs()[0]));
						ASequenceExtensionExpression seq = new ASequenceExtensionExpression(
								list);
						paramList.add(seq);
					} else {
						for (int i = 0; i < domOpAppl.getArgs().length; i++) {
							paramList
									.add(visitExprOrOpArgNodeExpression(domOpAppl
											.getArgs()[i]));
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
			return new ADomainExpression(
					visitExprOrOpArgNodeExpression(n.getArgs()[0]));

		case OPCODE_sof: // [ A -> B]
			return new ATotalFunctionExpression(
					visitExprOrOpArgNodeExpression(n.getArgs()[0]),
					visitExprOrOpArgNodeExpression(n.getArgs()[1]));

		case OPCODE_tup: { // $Tuple
			List<PExpression> list = new ArrayList<PExpression>();
			for (int i = 0; i < n.getArgs().length; i++) {
				list.add(visitExprOrOpArgNodeExpression(n.getArgs()[i]));
			}
			TLAType t = (TLAType) n.getToolObject(TYPE_ID);
			if (t instanceof TupleType) {
				return new ACoupleExpression(list);
			} else {
				if (list.size() == 0) {
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
			Hashtable<String, PExpression> pairTable = new Hashtable<String, PExpression>();
			for (int i = 0; i < args.length; i++) {
				OpApplNode pair = (OpApplNode) args[i];
				StringNode stringNode = (StringNode) pair.getArgs()[0];
				pairTable.put(stringNode.getRep().toString(),
						visitExprOrOpArgNodeExpression(pair.getArgs()[1]));

			}
			List<PRecEntry> recList = new ArrayList<PRecEntry>();
			if (struct.isExtensible()) {
				for (int i = 0; i < struct.getFields().size(); i++) {
					String fieldName = struct.getFields().get(i); // name
					AIdentifierExpression field = createIdentifierNode(fieldName);
					ARecEntry rec = new ARecEntry();
					rec.setIdentifier(field);
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
					AIdentifierExpression field = createIdentifierNode(fieldName);
					ARecEntry rec = new ARecEntry();
					rec.setIdentifier(field);
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
				Hashtable<String, PExpression> pairTable = new Hashtable<String, PExpression>();
				ExprOrOpArgNode[] args = n.getArgs();
				for (int i = 0; i < args.length; i++) {
					OpApplNode pair = (OpApplNode) args[i];
					StringNode stringNode = (StringNode) pair.getArgs()[0];
					pairTable.put(stringNode.getRep().toString(),
							visitExprOrOpArgNodeExpression(pair.getArgs()[1]));
				}
				List<PRecEntry> recList = new ArrayList<PRecEntry>();
				for (int i = 0; i < struct.getFields().size(); i++) {
					String fieldName = struct.getFields().get(i);
					AIdentifierExpression field = createIdentifierNode(fieldName);
					ARecEntry rec = new ARecEntry();
					rec.setIdentifier(field);
					if (pairTable.containsKey(fieldName)) {

						ACoupleExpression couple = new ACoupleExpression();
						List<PExpression> coupleList = new ArrayList<PExpression>();
						coupleList.add(new ABooleanTrueExpression());
						coupleList.add(pairTable.get(fieldName));
						couple.setList(coupleList);
						ASetExtensionExpression set = new ASetExtensionExpression(
								createPexpressionList(couple));
						rec.setValue(set);
					} else {
						AEmptySetExpression emptySet = new AEmptySetExpression();
						rec.setValue(emptySet);
					}
					recList.add(rec);
				}
				return new ARecExpression(recList);

			} else {
				Hashtable<String, PExpression> pairTable = new Hashtable<String, PExpression>();
				ExprOrOpArgNode[] args = n.getArgs();
				for (int i = 0; i < args.length; i++) {
					OpApplNode pair = (OpApplNode) args[i];
					StringNode stringNode = (StringNode) pair.getArgs()[0];
					pairTable.put(stringNode.getRep().toString(),
							visitExprOrOpArgNodeExpression(pair.getArgs()[1]));
				}
				List<PRecEntry> recList = new ArrayList<PRecEntry>();
				for (int i = 0; i < struct.getFields().size(); i++) {
					String fieldName = struct.getFields().get(i);
					AIdentifierExpression field = createIdentifierNode(fieldName);
					ARecEntry rec = new ARecEntry();
					rec.setIdentifier(field);
					if (pairTable.containsKey(fieldName)) {
						rec.setValue(pairTable.get(fieldName));
					} else {
						// this struct is extensible
						throw new NotImplementedException(
								"Missing case handling extensible structs.");
					}
					recList.add(rec);
				}
				return new ARecExpression(recList);
			}

		}

		case OPCODE_rs: { // $RcdSelect r.c
			StructType struct = (StructType) n.getArgs()[0]
					.getToolObject(TYPE_ID);
			if (struct.isExtensible()) {
				ARecordFieldExpression rcdSelect = new ARecordFieldExpression();
				rcdSelect
						.setRecord(visitExprOrOpArgNodeExpression(n.getArgs()[0]));
				StringNode stringNode = (StringNode) n.getArgs()[1];
				rcdSelect.setIdentifier(createIdentifierNode(stringNode
						.getRep().toString()));
				AFunctionExpression funcCall = new AFunctionExpression();
				funcCall.setIdentifier(rcdSelect);
				funcCall.setParameters(createPexpressionList(new ABooleanTrueExpression()));
				return funcCall;
			} else {
				ARecordFieldExpression rcdSelect = new ARecordFieldExpression();
				rcdSelect
						.setRecord(visitExprOrOpArgNodeExpression(n.getArgs()[0]));
				StringNode stringNode = (StringNode) n.getArgs()[1];
				rcdSelect.setIdentifier(createIdentifierNode(stringNode
						.getRep().toString()));
				return rcdSelect;
			}
		}

		case OPCODE_prime: // prime
		{
			OpApplNode node = (OpApplNode) n.getArgs()[0];
			return createIdentifierNode(node.getOperator().getName().toString()
					+ "_n");
		}

		case OPCODE_ite: { // IF THEN ELSE
			ALambdaExpression lambda1 = new ALambdaExpression();
			lambda1.setIdentifiers(createIdentifierList("t_"));
			AEqualPredicate eq1 = new AEqualPredicate(
					createIdentifierNode("t_"), new AIntegerExpression(
							new TIntegerLiteral("0")));
			AConjunctPredicate c1 = new AConjunctPredicate();
			c1.setLeft(eq1);
			c1.setRight(visitExprOrOpArgNodePredicate(n.getArgs()[0]));
			lambda1.setPredicate(c1);
			lambda1.setExpression(visitExprOrOpArgNodeExpression(n.getArgs()[1]));

			ALambdaExpression lambda2 = new ALambdaExpression();
			lambda2.setIdentifiers(createIdentifierList("t_"));
			AEqualPredicate eq2 = new AEqualPredicate(
					createIdentifierNode("t_"), new AIntegerExpression(
							new TIntegerLiteral("0")));
			AConjunctPredicate c2 = new AConjunctPredicate();
			c2.setLeft(eq2);
			ANegationPredicate not = new ANegationPredicate(
					visitExprOrOpArgNodePredicate(n.getArgs()[0]));
			c2.setRight(not);
			lambda2.setPredicate(c2);
			lambda2.setExpression(visitExprOrOpArgNodeExpression(n.getArgs()[2]));

			AUnionExpression union = new AUnionExpression(lambda1, lambda2);
			AFunctionExpression funCall = new AFunctionExpression();
			funCall.setIdentifier(union);
			List<PExpression> list = new ArrayList<PExpression>();
			list.add(new AIntegerExpression(new TIntegerLiteral("0")));
			funCall.setParameters(list);
			return funCall;
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

					LinkedList<ExprOrOpArgNode> seqList = new LinkedList<ExprOrOpArgNode>();
					for (int j = 0; j < seq.getArgs().length; j++) {
						seqList.add(seq.getArgs()[j]);
					}

					pair.setToolObject(EXCEPT_BASE, res.clone());
					res = evalExceptValue((PExpression) res.clone(), seqList,
							structType, val);
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

					LinkedList<ExprOrOpArgNode> seqList = new LinkedList<ExprOrOpArgNode>();
					for (int j = 0; j < seq.getArgs().length; j++) {
						seqList.add(seq.getArgs()[j]);
					}

					pair.setToolObject(EXCEPT_BASE, res.clone());
					res = evalExceptValue((PExpression) res.clone(), seqList,
							func, val);
				}
				return res;
			}
		}

		case OPCODE_seq: // !
		{
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
			ArrayList<PExpression> list = new ArrayList<PExpression>();
			for (int i = 0; i < params.length; i++) {
				for (int j = 0; j < params[i].length; j++) {
					list.add(createIdentifierNode(params[i][j]));
				}
			}
			AImplicationPredicate implication = new AImplicationPredicate();
			implication.setLeft(visitBoundsOfLocalVariables(n));
			implication.setRight(visitExprOrOpArgNodePredicate(n.getArgs()[0]));
			return new AConvertBoolExpression(new AForallPredicate(list,
					implication));
		}

		case OPCODE_be: { // \E x \in S : P
			FormalParamNode[][] params = n.getBdedQuantSymbolLists();
			ArrayList<PExpression> list = new ArrayList<PExpression>();
			for (int i = 0; i < params.length; i++) {
				for (int j = 0; j < params[i].length; j++) {
					list.add(createIdentifierNode(params[i][j]));
				}
			}
			AConjunctPredicate conjunction = new AConjunctPredicate();
			conjunction.setLeft(visitBoundsOfLocalVariables(n));
			conjunction.setRight(visitExprOrOpArgNodePredicate(n.getArgs()[0]));
			AExistsPredicate exists = new AExistsPredicate(list, conjunction);
			return new AConvertBoolExpression(exists);
		}

		}

		throw new RuntimeException(n.getOperator().getName().toString());
	}

	private List<PExpression> createListOfIdentifier(FormalParamNode[][] params) {
		List<PExpression> list = new ArrayList<PExpression>();
		for (int i = 0; i < params.length; i++) {
			for (int j = 0; j < params[i].length; j++) {
				FormalParamNode param = params[i][j];
				list.add(createIdentifierNode(param));
			}
		}
		return list;
	}

	private PExpression evalExceptValue(PExpression prefix,
			LinkedList<ExprOrOpArgNode> seqList, TLAType tlaType,
			ExprOrOpArgNode val) {

		ExprOrOpArgNode head = seqList.poll();
		if (head == null) {
			return visitExprOrOpArgNodeExpression(val);
		}

		if (tlaType instanceof StructType) {
			StructType structType = (StructType) tlaType;
			String field = ((StringNode) head).getRep().toString();

			List<PRecEntry> list = new ArrayList<PRecEntry>();
			for (int i = 0; i < structType.getFields().size(); i++) {
				ARecEntry entry = new ARecEntry();
				String fieldName = structType.getFields().get(i);
				entry.setIdentifier(createIdentifierNode(fieldName));

				PExpression value = null;
				ARecordFieldExpression select = new ARecordFieldExpression();
				select.setRecord((PExpression) prefix.clone());
				select.setIdentifier(createIdentifierNode(fieldName));
				if (fieldName.equals(field)) {
					value = evalExceptValue(select, seqList,
							structType.getType(fieldName), val);
				} else {
					value = select;
				}
				entry.setValue(value);
				list.add(entry);

			}

			ARecExpression rec = new ARecExpression(list);
			return rec;

		} else {
			FunctionType func = (FunctionType) tlaType;

			ACoupleExpression couple = new ACoupleExpression();
			List<PExpression> coupleList = new ArrayList<PExpression>();
			coupleList.add(visitExprOrOpArgNodeExpression(head));

			AFunctionExpression funcCall = new AFunctionExpression();
			funcCall.setIdentifier(prefix);
			List<PExpression> argList = new ArrayList<PExpression>();
			argList.add(visitExprOrOpArgNodeExpression(head));
			funcCall.setParameters(argList);
			coupleList.add(evalExceptValue(funcCall, seqList, func.getRange(),
					val));
			couple.setList(coupleList);
			List<PExpression> setList = new ArrayList<PExpression>();
			setList.add(couple);
			ASetExtensionExpression setExtension = new ASetExtensionExpression(
					setList);
			AOverwriteExpression overwrite = new AOverwriteExpression();
			overwrite.setLeft((PExpression) prefix.clone());
			overwrite.setRight(setExtension);
			return overwrite;
		}
	}

	private PExpression createProjectionFunction(PExpression pair, int field,
			TLAType t) {
		TupleType tuple = (TupleType) t;
		int size = tuple.getTypes().size();

		AFunctionExpression returnFunc = new AFunctionExpression();
		int index;
		if (field == 1) {
			index = 2;
			AFirstProjectionExpression first = new AFirstProjectionExpression();
			first.setExp1(tuple.getTypes().get(0).getBNode());
			first.setExp2(tuple.getTypes().get(1).getBNode());
			returnFunc.setIdentifier(first);
		} else {
			index = field;
			ASecondProjectionExpression second = new ASecondProjectionExpression();
			ArrayList<TLAType> typeList = new ArrayList<TLAType>();
			for (int i = 0; i < field - 1; i++) {
				typeList.add(tuple.getTypes().get(i));
			}
			second.setExp1(createNestedCouple(typeList));
			second.setExp2(tuple.getTypes().get(field - 1).getBNode());
			returnFunc.setIdentifier(second);
		}
		AFunctionExpression func = returnFunc;
		for (int i = index; i < size; i++) {
			AFunctionExpression newfunc = new AFunctionExpression();
			AFirstProjectionExpression first = new AFirstProjectionExpression();
			ArrayList<TLAType> typeList = new ArrayList<TLAType>();
			for (int j = 0; j < i; j++) {
				typeList.add(tuple.getTypes().get(j));
			}
			first.setExp1(createNestedCouple(typeList));
			first.setExp2(tuple.getTypes().get(i).getBNode());
			newfunc.setIdentifier(first);

			ArrayList<PExpression> list = new ArrayList<PExpression>();
			list.add(newfunc);
			func.setParameters(list);
			func = newfunc;
		}
		ArrayList<PExpression> list = new ArrayList<PExpression>();
		list.add(pair);
		func.setParameters(list);
		return returnFunc;
	}

	public static PExpression createNestedCouple(List<TLAType> typeList) {
		if (typeList.size() == 1) {
			return typeList.get(0).getBNode();
		}
		List<PExpression> list = new ArrayList<PExpression>();
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
		ADefinitionExpression defCall = new ADefinitionExpression();
		defCall.setDefLiteral(new TIdentifierLiteral("CHOOSE"));
		AComprehensionSetExpression comprehension = new AComprehensionSetExpression();
		List<PExpression> paramList = new ArrayList<PExpression>();
		for (FormalParamNode param : n.getUnbdedQuantSymbols()) {
			paramList.add(createIdentifierNode(param));
		}
		comprehension.setIdentifiers(paramList);
		comprehension
				.setPredicates(visitExprOrOpArgNodePredicate(n.getArgs()[0]));
		List<PExpression> list = new ArrayList<PExpression>();
		list.add(comprehension);
		defCall.setParameters(list);
		return defCall;
	}

	private PExpression createBoundedChoose(OpApplNode n) {
		ADefinitionExpression defCall = new ADefinitionExpression();
		defCall.setDefLiteral(new TIdentifierLiteral("CHOOSE"));
		AComprehensionSetExpression comprehension = new AComprehensionSetExpression();
		List<PExpression> paramList = new ArrayList<PExpression>();
		for (FormalParamNode param : n.getBdedQuantSymbolLists()[0]) {
			paramList.add(createIdentifierNode(param));
		}
		comprehension.setIdentifiers(paramList);
		PPredicate typingPredicate = visitBoundsOfLocalVariables(n);
		AConjunctPredicate conj = new AConjunctPredicate();
		conj.setLeft(typingPredicate);
		conj.setRight(visitExprOrOpArgNodePredicate(n.getArgs()[0]));
		comprehension.setPredicates(conj);
		List<PExpression> list = new ArrayList<PExpression>();
		list.add(comprehension);
		defCall.setParameters(list);
		return defCall;
	}

	private PExpression createCaseNode(OpApplNode n) {
		List<PPredicate> conditions = new ArrayList<PPredicate>();
		List<PPredicate> disjunctionList = new ArrayList<PPredicate>();
		for (int i = 0; i < n.getArgs().length; i++) {
			OpApplNode pair = (OpApplNode) n.getArgs()[i];

			AConjunctPredicate conj = new AConjunctPredicate();
			if (pair.getArgs()[0] == null) {
				ANegationPredicate neg = new ANegationPredicate();
				neg.setPredicate(createDisjunction(conditions));
				conj.setLeft(neg);
			} else {
				conditions
						.add(visitExprOrOpArgNodePredicate(pair.getArgs()[0]));
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
		List<PExpression> params = new ArrayList<PExpression>();
		params.add(comprehension);
		defCall.setParameters(params);
		return defCall;
	}

	private List<PExpression> createIdentifierList(String name) {
		ArrayList<PExpression> list = new ArrayList<PExpression>();
		list.add(createIdentifierNode(name));
		return list;
	}

	private PPredicate visitBuiltInKindPredicate(OpApplNode n) {
		switch (getOpCode(n.getOperator().getName())) {
		case OPCODE_land: // \land
		{
			AConjunctPredicate conjunction = new AConjunctPredicate();
			conjunction.setLeft(visitExprOrOpArgNodePredicate(n.getArgs()[0]));
			conjunction.setRight(visitExprOrOpArgNodePredicate(n.getArgs()[1]));
			return conjunction;
		}

		case OPCODE_cl: // $ConjList
		{
			List<PPredicate> list = new ArrayList<PPredicate>();
			for (int i = 0; i < n.getArgs().length; i++) {
				list.add(visitExprOrOpArgNodePredicate(n.getArgs()[i]));
			}
			return createConjunction(list);
		}

		case OPCODE_lor: // \/
		{
			ADisjunctPredicate disjunction = new ADisjunctPredicate();
			disjunction.setLeft(visitExprOrOpArgNodePredicate(n.getArgs()[0]));
			disjunction.setRight(visitExprOrOpArgNodePredicate(n.getArgs()[1]));
			return disjunction;
		}

		case OPCODE_dl: // $DisjList
		{
			List<PPredicate> list = new ArrayList<PPredicate>();
			for (int i = 0; i < n.getArgs().length; i++) {
				list.add(visitExprOrOpArgNodePredicate(n.getArgs()[i]));
			}
			return createDisjunction(list);
		}

		case OPCODE_lnot: // \lnot
			return new ANegationPredicate(
					visitExprOrOpArgNodePredicate(n.getArgs()[0]));

		case OPCODE_equiv: // \equiv
			return new AEquivalencePredicate(
					visitExprOrOpArgNodePredicate(n.getArgs()[0]),
					visitExprOrOpArgNodePredicate(n.getArgs()[1]));

		case OPCODE_implies: // =>
			return new AImplicationPredicate(
					visitExprOrOpArgNodePredicate(n.getArgs()[0]),
					visitExprOrOpArgNodePredicate(n.getArgs()[1]));

		case OPCODE_be: { // \E x \in S : P
			FormalParamNode[][] params = n.getBdedQuantSymbolLists();
			ArrayList<PExpression> list = new ArrayList<PExpression>();
			for (int i = 0; i < params.length; i++) {
				for (int j = 0; j < params[i].length; j++) {
					list.add(createIdentifierNode(params[i][j]));
				}
			}
			AConjunctPredicate conjunction = new AConjunctPredicate();
			conjunction.setLeft(visitBoundsOfLocalVariables(n));
			conjunction.setRight(visitExprOrOpArgNodePredicate(n.getArgs()[0]));
			return new AExistsPredicate(list, conjunction);
		}

		case OPCODE_bf: { // \A x \in S : P
			FormalParamNode[][] params = n.getBdedQuantSymbolLists();
			ArrayList<PExpression> list = new ArrayList<PExpression>();
			for (int i = 0; i < params.length; i++) {
				for (int j = 0; j < params[i].length; j++) {
					list.add(createIdentifierNode(params[i][j]));
				}
			}
			AImplicationPredicate implication = new AImplicationPredicate();
			implication.setLeft(visitBoundsOfLocalVariables(n));
			implication.setRight(visitExprOrOpArgNodePredicate(n.getArgs()[0]));
			return new AForallPredicate(list, implication);
		}

		case OPCODE_eq: { // =
			AEqualPredicate equal = new AEqualPredicate();
			equal.setLeft(visitExprOrOpArgNodeExpression(n.getArgs()[0]));
			equal.setRight(visitExprOrOpArgNodeExpression(n.getArgs()[1]));
			return equal;
		}

		case OPCODE_noteq: // /=
		{
			ANotEqualPredicate notEqual = new ANotEqualPredicate();
			notEqual.setLeft(visitExprOrOpArgNodeExpression(n.getArgs()[0]));
			notEqual.setRight(visitExprOrOpArgNodeExpression(n.getArgs()[1]));
			return notEqual;
		}

		case OPCODE_in: // \in
		{
			AMemberPredicate memberPredicate = new AMemberPredicate();
			memberPredicate
					.setLeft(visitExprOrOpArgNodeExpression(n.getArgs()[0]));
			memberPredicate
					.setRight(visitExprOrOpArgNodeExpression(n.getArgs()[1]));
			return memberPredicate;
		}

		case OPCODE_notin: // \notin
		{
			ANotMemberPredicate notMemberPredicate = new ANotMemberPredicate();
			notMemberPredicate.setLeft(visitExprOrOpArgNodeExpression(n
					.getArgs()[0]));
			notMemberPredicate.setRight(visitExprOrOpArgNodeExpression(n
					.getArgs()[1]));
			return notMemberPredicate;
		}

		case OPCODE_subseteq: // \subseteq {1,2} <: {1,2,3}
		{
			ASubsetPredicate subset = new ASubsetPredicate();
			subset.setLeft(visitExprOrOpArgNodeExpression(n.getArgs()[0]));
			subset.setRight(visitExprOrOpArgNodeExpression(n.getArgs()[1]));
			return subset;
		}

		case OPCODE_fa: { // f[1]
			AFunctionExpression func = new AFunctionExpression();
			func.setIdentifier(visitExprOrOpArgNodeExpression(n.getArgs()[0]));
			List<PExpression> paramList = new ArrayList<PExpression>();

			ExprOrOpArgNode dom = n.getArgs()[1];
			if (dom instanceof OpApplNode
					&& ((OpApplNode) dom).getOperator().getName().toString()
							.equals("$Tuple")) {
				OpApplNode domOpAppl = (OpApplNode) dom;
				for (int i = 0; i < domOpAppl.getArgs().length; i++) {
					paramList.add(visitExprOrOpArgNodeExpression(domOpAppl
							.getArgs()[i]));
				}
			} else {
				paramList.add(visitExprOrOpArgNodeExpression(dom));
			}
			func.setParameters(paramList);
			return new AEqualPredicate(func, new ABooleanTrueExpression());
		}

		case OPCODE_rs: { // $RcdSelect r.c
			ARecordFieldExpression rcdSelect = new ARecordFieldExpression();
			rcdSelect.setRecord(visitExprOrOpArgNodeExpression(n.getArgs()[0]));
			StringNode stringNode = (StringNode) n.getArgs()[1];
			rcdSelect.setIdentifier(createIdentifierNode(stringNode.getRep()
					.toString()));
			return new AEqualPredicate(rcdSelect, new ABooleanTrueExpression());
		}

		case OPCODE_case: {
			return new AEqualPredicate(createCaseNode(n),
					new ABooleanTrueExpression());
		}

		case OPCODE_prime: // prime
		{
			OpApplNode node = (OpApplNode) n.getArgs()[0];
			return new AEqualPredicate(
					createIdentifierNode(getName(node.getOperator()) + "_n"),
					new ABooleanTrueExpression());
		}

		case OPCODE_unchanged: {
			OpApplNode node = (OpApplNode) n.getArgs()[0];
			if (node.getOperator().getKind() == VariableDeclKind) {
				AEqualPredicate equal = new AEqualPredicate();
				equal.setLeft(createIdentifierNode(getName(node.getOperator())
						+ "_n"));
				equal.setRight(createIdentifierNode(node.getOperator()));
				return equal;
			} else if (node.getOperator().getKind() == UserDefinedOpKind) {
				OpDefNode operator = (OpDefNode) node.getOperator();
				ExprNode e = operator.getBody();
				OpApplNode opApplNode = (OpApplNode) e;
				node = opApplNode;
			}

			ArrayList<PPredicate> list = new ArrayList<PPredicate>();
			for (int i = 0; i < node.getArgs().length; i++) {
				OpApplNode var = (OpApplNode) node.getArgs()[i];
				AEqualPredicate equal = new AEqualPredicate();
				equal.setLeft(createIdentifierNode(getName(var.getOperator())
						+ "_n"));
				equal.setRight(createIdentifierNode(var.getOperator()));
				list.add(equal);
			}
			return createConjunction(list);
		}

		case OPCODE_uc: { // CHOOSE x : P
			return new AEqualPredicate(createUnboundedChoose(n),
					new ABooleanTrueExpression());
		}

		case OPCODE_bc: { // CHOOSE x \in S: P
			return new AEqualPredicate(createBoundedChoose(n),
					new ABooleanTrueExpression());
		}

		case OPCODE_ite: // IF THEN ELSE
		{
			AImplicationPredicate impl1 = new AImplicationPredicate();
			impl1.setLeft(visitExprOrOpArgNodePredicate(n.getArgs()[0]));
			impl1.setRight(visitExprOrOpArgNodePredicate(n.getArgs()[1]));

			AImplicationPredicate impl2 = new AImplicationPredicate();
			ANegationPredicate neg = new ANegationPredicate(
					visitExprOrOpArgNodePredicate(n.getArgs()[0]));
			impl2.setLeft(neg);
			impl2.setRight(visitExprOrOpArgNodePredicate(n.getArgs()[2]));
			return new AConjunctPredicate(impl1, impl2);
		}

		case 0:
			return visitBBuitInsPredicate(n);

		}

		throw new RuntimeException(n.getOperator().getName().toString());
	}

	public PPredicate visitBoundsOfLocalVariables(OpApplNode n) {
		FormalParamNode[][] params = n.getBdedQuantSymbolLists();
		ExprNode[] in = n.getBdedQuantBounds();
		boolean[] isTuple = n.isBdedQuantATuple();

		List<PPredicate> predList = new ArrayList<PPredicate>();
		for (int i = 0; i < params.length; i++) {
			if (isTuple[i]) {
				if (params[i].length == 1) {
					// one-tuple is handled is translated as a sequence
					FormalParamNode param = params[i][0];
					AMemberPredicate member = new AMemberPredicate();
					ASequenceExtensionExpression seq = new ASequenceExtensionExpression();
					List<PExpression> list = new ArrayList<PExpression>();
					list.add(createIdentifierNode(param));
					seq.setExpression(list);
					member.setLeft(seq);
					member.setRight(visitExprNodeExpression(in[i]));
					predList.add(member);

				} else {
					ArrayList<PExpression> list = new ArrayList<PExpression>();
					for (int j = 0; j < params[i].length; j++) {
						FormalParamNode param = params[i][j];
						list.add(createIdentifierNode(param));
					}
					AMemberPredicate member = new AMemberPredicate();
					member.setLeft(new ACoupleExpression(list));
					member.setRight(visitExprNodeExpression(in[i]));
					predList.add(member);
				}
			} else {
				for (int j = 0; j < params[i].length; j++) {
					AMemberPredicate member = new AMemberPredicate();
					member.setLeft(createIdentifierNode(params[i][j]));
					member.setRight(visitExprNodeExpression(in[i]));
					predList.add(member);
				}
			}
		}
		return createConjunction(predList);
	}

	public PPredicate visitBoundsOfFunctionsVariables(OpApplNode n) {
		FormalParamNode[][] params = n.getBdedQuantSymbolLists();
		ExprNode[] in = n.getBdedQuantBounds();
		boolean[] isTuple = n.isBdedQuantATuple();

		List<PPredicate> predList = new ArrayList<PPredicate>();
		for (int i = 0; i < params.length; i++) {
			if (isTuple[i]) {
				if (params[i].length == 1) { // one-tuple is handled as a
												// sequence
					FormalParamNode param = params[i][0];
					param.setToolObject(TUPLE, params[i]);

					AMemberPredicate member = new AMemberPredicate();
					member.setLeft(createIdentifierNode(param));
					member.setRight(visitExprNodeExpression(in[i]));
					predList.add(member);

				} else if (i == 0) {
					ArrayList<PExpression> list = new ArrayList<PExpression>();
					for (int j = 0; j < params[i].length; j++) {
						FormalParamNode param = params[i][j];
						list.add(createIdentifierNode(param));
					}
					AMemberPredicate member = new AMemberPredicate();
					member.setLeft(new ACoupleExpression(list));
					member.setRight(visitExprNodeExpression(in[i]));
					predList.add(member);
				} else {
					ArrayList<PExpression> list = new ArrayList<PExpression>();
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
					PExpression id = createIdentifierNode(sb.toString());
					AMemberPredicate member = new AMemberPredicate();
					member.setLeft(id);
					member.setRight(visitExprNodeExpression(in[i]));
					predList.add(member);
				}
			} else {
				for (int j = 0; j < params[i].length; j++) {
					AMemberPredicate member = new AMemberPredicate();
					member.setLeft(createIdentifierNode(params[i][j]));
					member.setRight(visitExprNodeExpression(in[i]));
					predList.add(member);
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
		List<TIdentifierLiteral> list = new ArrayList<TIdentifierLiteral>();
		TIdentifierLiteral tid = new TIdentifierLiteral(name);
		list.add(tid);
		return list;
	}

	public static List<PExpression> createPexpressionList(PExpression expr) {
		ArrayList<PExpression> list = new ArrayList<PExpression>();
		list.add(expr);
		return list;
	}

	public Start getStartNode() {
		return start;
	}

	public Definitions getBDefinitions() {
		// used for the recursive machine loader
		return bDefinitions;
	}

	public Hashtable<Node, TLAType> getTypeTable() {
		return this.typeTable;
	}

}
