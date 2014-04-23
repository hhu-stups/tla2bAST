package de.tla2bAst;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
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
import tlc2.tool.BuiltInOPs;
import tlc2.value.SetEnumValue;
import tlc2.value.Value;
import tlc2.value.ValueConstants;
import de.be4.classicalb.core.parser.Definitions;
import de.be4.classicalb.core.parser.node.AAbstractConstantsMachineClause;
import de.be4.classicalb.core.parser.node.AAbstractMachineParseUnit;
import de.be4.classicalb.core.parser.node.AAddExpression;
import de.be4.classicalb.core.parser.node.AAnySubstitution;
import de.be4.classicalb.core.parser.node.AAssignSubstitution;
import de.be4.classicalb.core.parser.node.ABecomesSuchSubstitution;
import de.be4.classicalb.core.parser.node.ABoolSetExpression;
import de.be4.classicalb.core.parser.node.ABooleanFalseExpression;
import de.be4.classicalb.core.parser.node.ABooleanTrueExpression;
import de.be4.classicalb.core.parser.node.ACardExpression;
import de.be4.classicalb.core.parser.node.AComprehensionSetExpression;
import de.be4.classicalb.core.parser.node.AConcatExpression;
import de.be4.classicalb.core.parser.node.AConjunctPredicate;
import de.be4.classicalb.core.parser.node.AConvertBoolExpression;
import de.be4.classicalb.core.parser.node.ACoupleExpression;
import de.be4.classicalb.core.parser.node.ADefinitionExpression;
import de.be4.classicalb.core.parser.node.ADefinitionPredicate;
import de.be4.classicalb.core.parser.node.ADefinitionsMachineClause;
import de.be4.classicalb.core.parser.node.ADisjunctPredicate;
import de.be4.classicalb.core.parser.node.ADivExpression;
import de.be4.classicalb.core.parser.node.ADomainExpression;
import de.be4.classicalb.core.parser.node.AEmptySequenceExpression;
import de.be4.classicalb.core.parser.node.AEmptySetExpression;
import de.be4.classicalb.core.parser.node.AEnumeratedSetSet;
import de.be4.classicalb.core.parser.node.AEqualPredicate;
import de.be4.classicalb.core.parser.node.AEquivalencePredicate;
import de.be4.classicalb.core.parser.node.AExistsPredicate;
import de.be4.classicalb.core.parser.node.AExpressionDefinitionDefinition;
import de.be4.classicalb.core.parser.node.AFinSubsetExpression;
import de.be4.classicalb.core.parser.node.AFirstExpression;
import de.be4.classicalb.core.parser.node.AForallPredicate;
import de.be4.classicalb.core.parser.node.AFunctionExpression;
import de.be4.classicalb.core.parser.node.AGeneralUnionExpression;
import de.be4.classicalb.core.parser.node.AGreaterEqualPredicate;
import de.be4.classicalb.core.parser.node.AGreaterPredicate;
import de.be4.classicalb.core.parser.node.AIdentifierExpression;
import de.be4.classicalb.core.parser.node.AImplicationPredicate;
import de.be4.classicalb.core.parser.node.AInitialisationMachineClause;
import de.be4.classicalb.core.parser.node.AInsertTailExpression;
import de.be4.classicalb.core.parser.node.AIntegerExpression;
import de.be4.classicalb.core.parser.node.AIntegerSetExpression;
import de.be4.classicalb.core.parser.node.AIntersectionExpression;
import de.be4.classicalb.core.parser.node.AIntervalExpression;
import de.be4.classicalb.core.parser.node.AInvariantMachineClause;
import de.be4.classicalb.core.parser.node.ALambdaExpression;
import de.be4.classicalb.core.parser.node.ALessEqualPredicate;
import de.be4.classicalb.core.parser.node.ALessPredicate;
import de.be4.classicalb.core.parser.node.AMachineHeader;
import de.be4.classicalb.core.parser.node.AMachineMachineVariant;
import de.be4.classicalb.core.parser.node.AMemberPredicate;
import de.be4.classicalb.core.parser.node.AMinusOrSetSubtractExpression;
import de.be4.classicalb.core.parser.node.AMultOrCartExpression;
import de.be4.classicalb.core.parser.node.ANaturalSetExpression;
import de.be4.classicalb.core.parser.node.ANegationPredicate;
import de.be4.classicalb.core.parser.node.ANotEqualPredicate;
import de.be4.classicalb.core.parser.node.ANotMemberPredicate;
import de.be4.classicalb.core.parser.node.AOperation;
import de.be4.classicalb.core.parser.node.AOperationsMachineClause;
import de.be4.classicalb.core.parser.node.AOverwriteExpression;
import de.be4.classicalb.core.parser.node.APowSubsetExpression;
import de.be4.classicalb.core.parser.node.APowerOfExpression;
import de.be4.classicalb.core.parser.node.APredicateDefinitionDefinition;
import de.be4.classicalb.core.parser.node.APropertiesMachineClause;
import de.be4.classicalb.core.parser.node.ARecEntry;
import de.be4.classicalb.core.parser.node.ARecExpression;
import de.be4.classicalb.core.parser.node.ARecordFieldExpression;
import de.be4.classicalb.core.parser.node.ARestrictFrontExpression;
import de.be4.classicalb.core.parser.node.ARestrictTailExpression;
import de.be4.classicalb.core.parser.node.ASeqExpression;
import de.be4.classicalb.core.parser.node.ASequenceExtensionExpression;
import de.be4.classicalb.core.parser.node.ASetExtensionExpression;
import de.be4.classicalb.core.parser.node.ASetsMachineClause;
import de.be4.classicalb.core.parser.node.ASizeExpression;
import de.be4.classicalb.core.parser.node.AStringExpression;
import de.be4.classicalb.core.parser.node.AStringSetExpression;
import de.be4.classicalb.core.parser.node.AStructExpression;
import de.be4.classicalb.core.parser.node.ASubsetPredicate;
import de.be4.classicalb.core.parser.node.ASubstitutionDefinitionDefinition;
import de.be4.classicalb.core.parser.node.ATailExpression;
import de.be4.classicalb.core.parser.node.ATotalFunctionExpression;
import de.be4.classicalb.core.parser.node.AUnaryMinusExpression;
import de.be4.classicalb.core.parser.node.AUnionExpression;
import de.be4.classicalb.core.parser.node.AVariablesMachineClause;
import de.be4.classicalb.core.parser.node.EOF;
import de.be4.classicalb.core.parser.node.PDefinition;
import de.be4.classicalb.core.parser.node.PExpression;
import de.be4.classicalb.core.parser.node.PMachineClause;
import de.be4.classicalb.core.parser.node.POperation;
import de.be4.classicalb.core.parser.node.PPredicate;
import de.be4.classicalb.core.parser.node.PRecEntry;
import de.be4.classicalb.core.parser.node.PSet;
import de.be4.classicalb.core.parser.node.Start;
import de.be4.classicalb.core.parser.node.TDefLiteralPredicate;
import de.be4.classicalb.core.parser.node.TIdentifierLiteral;
import de.be4.classicalb.core.parser.node.TIntegerLiteral;
import de.be4.classicalb.core.parser.node.TStringLiteral;
import de.tla2b.analysis.BOperation;
import de.tla2b.analysis.PredicateVsExpression;
import de.tla2b.analysis.RecursiveDefinition;
import de.tla2b.analysis.SpecAnalyser;
import de.tla2b.analysis.UsedExternalFunctions;
import de.tla2b.analysis.PredicateVsExpression.DefinitionType;
import de.tla2b.analysis.UsedExternalFunctions.EXTERNAL_FUNCTIONS;
import de.tla2b.config.ConfigfileEvaluator;
import de.tla2b.config.ValueObj;
import de.tla2b.global.BBuildIns;
import de.tla2b.global.BBuiltInOPs;
import de.tla2b.global.Priorities;
import de.tla2b.global.TranslationGlobals;
import de.tla2b.types.EnumType;
import de.tla2b.types.FunctionType;
import de.tla2b.types.IType;
import de.tla2b.types.SetType;
import de.tla2b.types.StructType;
import de.tla2b.types.TLAType;
import de.tla2b.types.TupleType;

public class BAstCreator extends BuiltInOPs implements TranslationGlobals,
		ASTConstants, IType, BBuildIns, Priorities, ValueConstants {
	Start start;
	List<PMachineClause> machineClauseList;
	ConfigfileEvaluator conEval;
	SpecAnalyser specAnalyser;
	private final PredicateVsExpression predicateVsExpression;

	final int SUBSTITUTE_PARAM = 29;

	final HashSet<OpDefNode> allTLADefinitions;
	List<OpDeclNode> bConstants;

	private ModuleNode moduleNode;
	private final UsedExternalFunctions usedExternalFunctions;

	private Definitions bDefinitions = new Definitions();

	public Start getStartNode() {
		return start;
	}

	public Definitions getBDefinitions() {
		// used for the recursive machine loader
		return bDefinitions;
	}

	public BAstCreator(ModuleNode moduleNode, ConfigfileEvaluator conEval,
			SpecAnalyser specAnalyser,
			UsedExternalFunctions usedExternalFunctions,
			PredicateVsExpression predicateVsExpression) {
		this.predicateVsExpression = predicateVsExpression;
		this.conEval = conEval;
		this.moduleNode = moduleNode;
		this.specAnalyser = specAnalyser;
		this.usedExternalFunctions = usedExternalFunctions;
		this.allTLADefinitions = new HashSet<OpDefNode>(
				Arrays.asList(moduleNode.getOpDefs()));

		if (conEval != null) {
			this.bConstants = conEval.getbConstantList();
		} else {
			this.bConstants = Arrays.asList(moduleNode.getConstantDecls());
		}

		machineClauseList = new ArrayList<PMachineClause>();

		AAbstractMachineParseUnit aAbstractMachineParseUnit = new AAbstractMachineParseUnit();
		aAbstractMachineParseUnit.setVariant(new AMachineMachineVariant());
		AMachineHeader machineHeader = new AMachineHeader();
		List<TIdentifierLiteral> headerName = createTIdentifierLiteral(moduleNode
				.getName().toString());
		machineHeader.setName(headerName);
		aAbstractMachineParseUnit.setHeader(machineHeader);

		createSetsClause();
		createDefintionClause();
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
				list.add(createIdentifierNode(p.getName().toString()));
			}

			// TLAType type = (TLAType) opDefNode.getToolObject(TYPE_ID);
			// if (opDefNode.level == 2 || type instanceof BoolType) {
			if (predicateVsExpression.getDefinitionType(opDefNode) == DefinitionType.PREDICATE) {
				APredicateDefinitionDefinition d = new APredicateDefinitionDefinition();
				d.setName(new TDefLiteralPredicate(opDefNode.getName()
						.toString()));
				d.setParameters(list);
				d.setRhs(visitExprNodePredicate(opDefNode.getBody()));
				defs.add(d);
			} else {
				AExpressionDefinitionDefinition d = new AExpressionDefinitionDefinition();
				d.setName(new TIdentifierLiteral(opDefNode.getName().toString()));

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
			for (int j = 0; j < op.getOpParams().size(); j++) {
				paramList.add(createIdentifierNode(op.getOpParams().get(j)));
			}
			for (int j = 0; j < op.getExistQuans().size(); j++) {
				OpApplNode o = op.getExistQuans().get(j);
				whereList.add(visitBounded(o));
			}

			AOperation operation = new AOperation();
			operation.setOpName(createTIdentifierLiteral(defName));
			operation.setParameters(paramList);
			operation.setReturnValues(new ArrayList<PExpression>());

			AAnySubstitution any = new AAnySubstitution();
			OpDeclNode[] vars = moduleNode.getVariableDecls();
			List<PExpression> anyParams = new ArrayList<PExpression>();
			for (int j = 0; j < vars.length; j++) {
				String varName = vars[j].getName().toString();
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
				String varName = vars[j].getName().toString();
				if (op.getUnchangedVariables().contains(varName))
					continue;
				varList.add(createIdentifierNode(varName));
				valueList.add(createIdentifierNode(varName + "_n"));
			}
			AAssignSubstitution assign = new AAssignSubstitution(varList,
					valueList);
			any.setThen(assign);
			operation.setOperationBody(any);
			opList.add(operation);
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
			varList.add(createIdentifierNode(vars[i].getName().toString()));
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
						createTIdentifierLiteral(opDeclNode.getName()
								.toString()));
				list.add(id);
			}
			AVariablesMachineClause varClause = new AVariablesMachineClause(
					list);
			machineClauseList.add(varClause);
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
					createTIdentifierLiteral(opDeclNode.getName().toString()));
			constantsList.add(id);
		}

		for (RecursiveDefinition recDef : specAnalyser
				.getRecursiveDefinitions()) {

			AIdentifierExpression id = new AIdentifierExpression(
					createTIdentifierLiteral(recDef.getOpDefNode().getName()
							.toString()));
			constantsList.add(id);
		}

		if (constantsList.size() > 0) {
			AAbstractConstantsMachineClause abstractConstantsClause = new AAbstractConstantsMachineClause(
					constantsList);
			machineClauseList.add(abstractConstantsClause);
		}

	}

	private void createPropertyClause() {
		List<PPredicate> propertiesList = new ArrayList<PPredicate>();

		for (RecursiveDefinition recDef : specAnalyser
				.getRecursiveDefinitions()) {
			OpDefNode def = recDef.getOpDefNode();
			TLAType t = (TLAType) def.getToolObject(TYPE_ID);
			// OpApplNode ifThenElse = recDef.getIfThenElse();
			FormalParamNode[] params = def.getParams();
			ArrayList<PExpression> paramList1 = new ArrayList<PExpression>();
			ArrayList<PPredicate> typeList = new ArrayList<PPredicate>();
			// ArrayList<PExpression> paramList2 = new ArrayList<PExpression>();
			for (FormalParamNode p : params) {
				paramList1.add(createIdentifierNode(p.getName().toString()));
				// paramList2.add(createIdentifierNode(p.getName().toString()));
				TLAType paramType = (TLAType) p.getToolObject(TYPE_ID);
				System.out.println(paramType);
				AEqualPredicate equal = new AEqualPredicate(
						createIdentifierNode(p.getName().toString()),
						paramType.getBNode());
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
					createIdentifierNode(def.getName().toString()), lambda1);
			propertiesList.add(equals);
		}

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
					equal.setLeft(createIdentifierNode(con.getName().toString()));
					equal.setRight(createIdentifierNode(((SetType) t)
							.getSubType().toString()));
					propertiesList.add(equal);
				} else {
					AEqualPredicate equal = new AEqualPredicate();
					equal.setLeft(createIdentifierNode(con.getName().toString()));
					Value tlcValue = v.getValue();
					equal.setRight(createTLCValue(tlcValue));
					propertiesList.add(equal);
				}
			} else {
				AMemberPredicate member = new AMemberPredicate();
				member.setLeft(createIdentifierNode(con.getName().toString()));
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
				equal.setLeft(createIdentifierNode(con.getName().toString()));
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

	private PExpression createTLCValue(Value tlcValue) {
		switch (tlcValue.getKind()) {
		case INTVALUE:

			return new AIntegerExpression(new TIntegerLiteral(
					tlcValue.toString()));

		}

		throw new RuntimeException();
	}

	private void createInvariantClause() {
		OpDeclNode[] vars = moduleNode.getVariableDecls();
		if (vars.length == 0)
			return;

		List<PPredicate> predList = new ArrayList<PPredicate>();
		for (int i = 0; i < vars.length; i++) {
			TLAType varType = (TLAType) vars[i].getToolObject(TYPE_ID);

			AMemberPredicate member = new AMemberPredicate();
			member.setLeft(createIdentifierNode(vars[i].getName().toString()));
			member.setRight(varType.getBNode());

			predList.add(member);
		}

		if (conEval != null) {
			for (OpDefNode def : conEval.getInvariants()) {
				ADefinitionPredicate defPred = new ADefinitionPredicate();
				defPred.setDefLiteral(new TDefLiteralPredicate(def.getName()
						.toString()));
				predList.add(defPred);
			}
		}

		AInvariantMachineClause invClause = new AInvariantMachineClause(
				createConjunction(predList));
		machineClauseList.add(invClause);
	}

	private PPredicate visitAssumeNode(AssumeNode assumeNode) {
		return visitExprNodePredicate(assumeNode.getAssume());
	}

	private PPredicate visitExprNodePredicate(ExprNode n) {
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

		System.out.println(n);
		System.out.println(n.getClass());
		throw new RuntimeException();
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
			if (type instanceof FunctionType) {

				List<PExpression> params = new ArrayList<PExpression>();
				params.add(visitExprOrOpArgNodeExpression(list.get(0)));

				AFunctionExpression funCall = new AFunctionExpression();
				funCall.setIdentifier(visitExprNodeExpression(at.getAtBase()));
				funCall.setParameters(params);
				return funCall;
			} else {
				ARecordFieldExpression select = new ARecordFieldExpression();
				select.setRecord(visitExprNodeExpression(at.getAtBase()));
				StringNode stringNode = (StringNode) list.get(0);
				select.setIdentifier(createIdentifierNode(stringNode.getRep()
						.toString()));
				return select;
			}
		}

		case LetInKind: {
			LetInNode letInNode = (LetInNode) n;
			return visitExprNodeExpression(letInNode.getBody());
		}

		}

		System.out.println(n.getClass());
		throw new RuntimeException();
	}

	private PPredicate visitOpApplNodePredicate(OpApplNode n) {
		switch (n.getOperator().getKind()) {
		case ConstantDeclKind: {
			return new AEqualPredicate(createIdentifierNode(n.getOperator()
					.getName().toString()), new ABooleanTrueExpression());
		}
		case VariableDeclKind: {
			return new AEqualPredicate(createIdentifierNode(n.getOperator()
					.getName().toString()), new ABooleanTrueExpression());

		}
		case BuiltInKind:
			return visitBuiltInKindPredicate(n);

		case UserDefinedOpKind: {
			return visitUserdefinedOpPredicate(n);
		}

		}
		System.out.println(n.getOperator().getName());
		throw new RuntimeException();
	}

	private PExpression visitOpApplNodeExpression(OpApplNode n) {
		switch (n.getOperator().getKind()) {
		case ConstantDeclKind: {
			return createIdentifierNode(n.getOperator().getName().toString());
		}
		case VariableDeclKind: {
			return createIdentifierNode(n.getOperator().getName().toString());
		}

		case FormalParamKind: {
			FormalParamNode param = (FormalParamNode) n.getOperator();
			ExprOrOpArgNode e = (ExprOrOpArgNode) param
					.getToolObject(SUBSTITUTE_PARAM);
			if (e == null) {
				return createIdentifierNode(n.getOperator().getName()
						.toString());
			} else {
				return visitExprOrOpArgNodeExpression(e);
			}

		}

		case BuiltInKind:
			return visitBuiltInKindExpression(n);

		case UserDefinedOpKind: {
			return visitUserdefinedOpExpression(n);
		}
		}

		System.out.println(n.getOperator().getName());
		throw new RuntimeException();
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

		List<PExpression> params = new ArrayList<PExpression>();
		for (int i = 0; i < n.getArgs().length; i++) {
			params.add(visitExprOrOpArgNodeExpression(n.getArgs()[i]));
		}
		if (predicateVsExpression.getDefinitionType(def) == DefinitionType.EXPRESSION) {
			ADefinitionExpression defCall = new ADefinitionExpression();
			defCall.setDefLiteral(new TIdentifierLiteral(def.getName()
					.toString()));
			;
			defCall.setParameters(params);
			return new AEqualPredicate(defCall, new ABooleanTrueExpression());

		} else {
			ADefinitionPredicate defCall = new ADefinitionPredicate();
			defCall.setDefLiteral(new TDefLiteralPredicate(def.getName()
					.toString()));

			defCall.setParameters(params);
			return defCall;
		}
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

		if (allTLADefinitions.contains(def)) {
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
						name = entry.getKey().getName().toString();
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
				ADefinitionExpression defExpr = new ADefinitionExpression();
				defExpr.setDefLiteral(new TIdentifierLiteral(n.getOperator()
						.getName().toString()));
				defExpr.setParameters(params);
				return defExpr;
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

		}
		System.out.println(n.getOperator().getName());
		throw new RuntimeException();
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

		case B_OPCODE_subseq: { // SubSeq(s,m,n)
			ARestrictFrontExpression restrictFront = new ARestrictFrontExpression();
			restrictFront
					.setLeft(visitExprOrOpArgNodeExpression(n.getArgs()[0]));
			restrictFront
					.setRight(visitExprOrOpArgNodeExpression(n.getArgs()[2]));

			ARestrictTailExpression restrictTail = new ARestrictTailExpression();
			restrictTail.setLeft(restrictFront);
			restrictTail
					.setRight(visitExprOrOpArgNodeExpression(n.getArgs()[1]));
			return restrictTail;
		}

		}
		System.out.println(n.getOperator().getName());
		throw new RuntimeException();
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
			// TODO tuple with more than 2 arguments
			FormalParamNode[][] params = n.getBdedQuantSymbolLists();
			ExprNode[] bounds = n.getBdedQuantBounds();

			List<PExpression> list = new ArrayList<PExpression>();
			FormalParamNode p = n.getBdedQuantSymbolLists()[0][0];
			list.add(createIdentifierNode(p.getName().toString()));

			AComprehensionSetExpression compre = new AComprehensionSetExpression();
			compre.setIdentifiers(list);

			AMemberPredicate member = new AMemberPredicate();
			member.setLeft(createIdentifierNode(p.getName().toString()));
			ExprNode in = n.getBdedQuantBounds()[0];
			member.setRight(visitExprNodeExpression(in));

			AConjunctPredicate conj = new AConjunctPredicate(member,
					visitExprOrOpArgNodePredicate(n.getArgs()[0]));
			compre.setPredicates(conj);
			return compre;
		}

		case OPCODE_soa: { // $SetOfAll Represents {e : p1 \in S, p2,p3 \in S2}

			AExistsPredicate exist = new AExistsPredicate();
			FormalParamNode[][] params = n.getBdedQuantSymbolLists();
			ExprNode[] bounds = n.getBdedQuantBounds();

			List<PExpression> idList = new ArrayList<PExpression>();
			List<PPredicate> predList = new ArrayList<PPredicate>();
			for (int i = 0; i < bounds.length; i++) {
				FormalParamNode p = params[i][0];
				AMemberPredicate member = new AMemberPredicate();
				member.setLeft(createIdentifierNode(p.getName().toString()));
				ExprNode in = n.getBdedQuantBounds()[i];
				member.setRight(visitExprNodeExpression(in));
				predList.add(member);
				idList.add(createIdentifierNode(p.getName().toString()));
			}
			final String nameOfTempVariable = "t_";
			AEqualPredicate equals = new AEqualPredicate();
			equals.setLeft(createIdentifierNode(nameOfTempVariable));
			equals.setRight(visitExprOrOpArgNodeExpression(n.getArgs()[0]));
			predList.add(equals);
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
			ExprNode[] bounds = n.getBdedQuantBounds();
			List<PExpression> idList = new ArrayList<PExpression>();
			List<PPredicate> predList = new ArrayList<PPredicate>();
			for (int i = 0; i < params.length; i++) {
				for (int j = 0; j < params[i].length; j++) {
					FormalParamNode p = params[i][j];
					AMemberPredicate member = new AMemberPredicate();
					member.setLeft(createIdentifierNode(p.getName().toString()));
					ExprNode in = n.getBdedQuantBounds()[i];
					member.setRight(visitExprNodeExpression(in));
					predList.add(member);
					idList.add(createIdentifierNode(p.getName().toString()));
				}
			}
			ALambdaExpression lambda = new ALambdaExpression();
			lambda.setIdentifiers(idList);
			lambda.setPredicate(createConjunction(predList));
			lambda.setExpression(visitExprOrOpArgNodeExpression(n.getArgs()[0]));
			return lambda;
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
			return func;
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
			return new AMultOrCartExpression(
					visitExprOrOpArgNodeExpression(n.getArgs()[0]),
					visitExprOrOpArgNodeExpression(n.getArgs()[1]));

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

			return new AStructExpression(recList);
		}

		case OPCODE_rc: { // [h_1 |-> 1, h_2 |-> 2]
			StructType struct = (StructType) n.getToolObject(TYPE_ID);
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
					// insert null element
				}
				recList.add(rec);
			}

			return new ARecExpression(recList);
		}

		case OPCODE_rs: { // $RcdSelect r.c
			ARecordFieldExpression rcdSelect = new ARecordFieldExpression();
			rcdSelect.setRecord(visitExprOrOpArgNodeExpression(n.getArgs()[0]));
			StringNode stringNode = (StringNode) n.getArgs()[1];
			rcdSelect.setIdentifier(createIdentifierNode(stringNode.getRep()
					.toString()));
			return rcdSelect;
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

		case OPCODE_exc: // Except
		{
			TLAType type = (TLAType) n.getToolObject(TYPE_ID);
			if (type.getKind() == STRUCT) {
				Hashtable<String, PExpression> temp = new Hashtable<String, PExpression>();
				for (int i = 1; i < n.getArgs().length; i++) {
					OpApplNode pair = (OpApplNode) n.getArgs()[i];
					ExprOrOpArgNode first = pair.getArgs()[0];
					ExprOrOpArgNode second = pair.getArgs()[1];
					OpApplNode seq = (OpApplNode) first;

					PExpression val = visitExprOrOpArgNodeExpression(second);

					StringNode stringNode = (StringNode) seq.getArgs()[0];
					String fieldName = stringNode.getRep().toString();
					temp.put(fieldName, val);
				}

				StructType st = (StructType) type;
				List<PRecEntry> list = new ArrayList<PRecEntry>();
				for (int i = 0; i < st.getFields().size(); i++) {
					ARecEntry entry = new ARecEntry();
					String fieldName = st.getFields().get(i);
					entry.setIdentifier(createIdentifierNode(fieldName));
					PExpression value = temp.get(fieldName);
					if (value == null) {
						value = new ARecordFieldExpression(
								visitExprOrOpArgNodeExpression(n.getArgs()[0]),
								createIdentifierNode(fieldName));
					}
					entry.setValue(value);
					list.add(entry);
				}
				ARecExpression rec = new ARecExpression(list);
				return rec;

			} else {
				FunctionType func = (FunctionType) type;

				List<PExpression> list = new ArrayList<PExpression>();
				for (int i = 1; i < n.getArgs().length; i++) {
					OpApplNode pair = (OpApplNode) n.getArgs()[i];

					ACoupleExpression couple = new ACoupleExpression();
					List<PExpression> coupleList = new ArrayList<PExpression>();
					coupleList.add(visitExprOrOpArgNodeExpression(pair
							.getArgs()[0]));
					coupleList.add(visitExprOrOpArgNodeExpression(pair
							.getArgs()[1]));
					couple.setList(coupleList);
					list.add(couple);
				}
				ASetExtensionExpression setExtension = new ASetExtensionExpression(
						list);
				AOverwriteExpression overwrite = new AOverwriteExpression();
				overwrite
						.setLeft(visitExprOrOpArgNodeExpression(n.getArgs()[0]));
				overwrite.setRight(setExtension);
				return overwrite;
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

		}

		System.out.println(n.getOperator().getName());
		throw new RuntimeException();
	}

	private PExpression createUnboundedChoose(OpApplNode n) {
		ADefinitionExpression defCall = new ADefinitionExpression();
		defCall.setDefLiteral(new TIdentifierLiteral("CHOOSE"));
		AComprehensionSetExpression comprehension = new AComprehensionSetExpression();
		FormalParamNode x = n.getUnbdedQuantSymbols()[0];
		comprehension.setIdentifiers(createIdentifierList(x.getName()
				.toString()));
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
		FormalParamNode x = n.getBdedQuantSymbolLists()[0][0];
		comprehension.setIdentifiers(createIdentifierList(x.getName()
				.toString()));
		AMemberPredicate member = new AMemberPredicate();
		member.setLeft(createIdentifierNode(x.getName().toString()));
		ExprNode in = n.getBdedQuantBounds()[0];
		member.setRight(visitExprNodeExpression(in));
		AConjunctPredicate conj = new AConjunctPredicate();
		conj.setLeft(member);
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
					list.add(createIdentifierNode(params[i][j].getName()
							.toString()));
				}
			}
			AConjunctPredicate conjunction = new AConjunctPredicate();
			conjunction.setLeft(visitBounded(n));
			conjunction.setRight(visitExprOrOpArgNodePredicate(n.getArgs()[0]));
			return new AExistsPredicate(list, conjunction);
		}

		case OPCODE_bf: { // \A x \in S : P
			FormalParamNode[][] params = n.getBdedQuantSymbolLists();
			ArrayList<PExpression> list = new ArrayList<PExpression>();
			for (int i = 0; i < params.length; i++) {
				for (int j = 0; j < params[i].length; j++) {
					list.add(createIdentifierNode(params[i][j].getName()
							.toString()));
				}
			}
			AImplicationPredicate implication = new AImplicationPredicate();
			implication.setLeft(visitBounded(n));
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
			return new AEqualPredicate(createIdentifierNode(node.getOperator()
					.getName().toString()
					+ "_n"), new ABooleanTrueExpression());
		}

		case OPCODE_unchanged: {
			return new AEqualPredicate(new ABooleanTrueExpression(),
					new ABooleanTrueExpression());
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

		System.out.println(n.getOperator().getName());
		throw new RuntimeException();
	}

	private PPredicate visitBounded(OpApplNode n) {
		FormalParamNode[][] params = n.getBdedQuantSymbolLists();
		ExprNode[] in = n.getBdedQuantBounds();
		boolean[] isTuple = n.isBdedQuantATuple();

		List<PPredicate> predList = new ArrayList<PPredicate>();
		for (int i = 0; i < params.length; i++) {
			if (isTuple[i]) {

				ArrayList<PExpression> list = new ArrayList<PExpression>();
				for (int j = 0; j < params[i].length; j++) {
					list.add(createIdentifierNode(params[i][j].getName()
							.toString()));
				}
				AMemberPredicate member = new AMemberPredicate();
				member.setLeft(new ACoupleExpression(list));
				member.setRight(visitExprNodeExpression(in[i]));
				predList.add(member);
			} else {
				for (int j = 0; j < params[i].length; j++) {
					AMemberPredicate member = new AMemberPredicate();
					member.setLeft(createIdentifierNode(params[i][j].getName()
							.toString()));
					member.setRight(visitExprNodeExpression(in[i]));
					predList.add(member);
				}
			}
		}
		return createConjunction(predList);
	}

	private PPredicate visitExprOrOpArgNodePredicate(ExprOrOpArgNode n) {
		if (n instanceof ExprNode) {
			return visitExprNodePredicate((ExprNode) n);
		} else {
			throw new RuntimeException("OpArgNode not implemented jet");
		}
	}

	private PExpression visitExprOrOpArgNodeExpression(ExprOrOpArgNode n) {

		if (n instanceof ExprNode) {
			return visitExprNodeExpression((ExprNode) n);
		} else {
			throw new RuntimeException("OpArgNode not implemented jet");
		}
	}

	public static AIdentifierExpression createIdentifierNode(String name) {
		return new AIdentifierExpression(createTIdentifierLiteral(name));
	}

	private PPredicate createConjunction(List<PPredicate> list) {
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

}
