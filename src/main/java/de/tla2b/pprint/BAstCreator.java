package de.tla2b.pprint;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Hashtable;
import java.util.List;

import tla2sany.semantic.ASTConstants;
import tla2sany.semantic.AssumeNode;
import tla2sany.semantic.ExprNode;
import tla2sany.semantic.ExprOrOpArgNode;
import tla2sany.semantic.FormalParamNode;
import tla2sany.semantic.ModuleNode;
import tla2sany.semantic.NumeralNode;
import tla2sany.semantic.OpApplNode;
import tla2sany.semantic.OpDeclNode;
import tla2sany.semantic.OpDefNode;
import tla2sany.semantic.StringNode;
import tlc2.tool.BuiltInOPs;
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
import de.be4.classicalb.core.parser.node.ADisjunctPredicate;
import de.be4.classicalb.core.parser.node.ADivExpression;
import de.be4.classicalb.core.parser.node.ADomainExpression;
import de.be4.classicalb.core.parser.node.AEmptySetExpression;
import de.be4.classicalb.core.parser.node.AEqualPredicate;
import de.be4.classicalb.core.parser.node.AEquivalencePredicate;
import de.be4.classicalb.core.parser.node.AExistsPredicate;
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
import de.be4.classicalb.core.parser.node.APowSubsetExpression;
import de.be4.classicalb.core.parser.node.APowerOfExpression;
import de.be4.classicalb.core.parser.node.APropertiesMachineClause;
import de.be4.classicalb.core.parser.node.ARecEntry;
import de.be4.classicalb.core.parser.node.ARecExpression;
import de.be4.classicalb.core.parser.node.ARecordFieldExpression;
import de.be4.classicalb.core.parser.node.ASeqExpression;
import de.be4.classicalb.core.parser.node.ASequenceExtensionExpression;
import de.be4.classicalb.core.parser.node.ASetExtensionExpression;
import de.be4.classicalb.core.parser.node.ASizeExpression;
import de.be4.classicalb.core.parser.node.AStringExpression;
import de.be4.classicalb.core.parser.node.AStringSetExpression;
import de.be4.classicalb.core.parser.node.AStructExpression;
import de.be4.classicalb.core.parser.node.ASubsetPredicate;
import de.be4.classicalb.core.parser.node.ATailExpression;
import de.be4.classicalb.core.parser.node.ATotalFunctionExpression;
import de.be4.classicalb.core.parser.node.AUnaryMinusExpression;
import de.be4.classicalb.core.parser.node.AUnionExpression;
import de.be4.classicalb.core.parser.node.AVariablesMachineClause;
import de.be4.classicalb.core.parser.node.EOF;
import de.be4.classicalb.core.parser.node.PExpression;
import de.be4.classicalb.core.parser.node.PMachineClause;
import de.be4.classicalb.core.parser.node.POperation;
import de.be4.classicalb.core.parser.node.PPredicate;
import de.be4.classicalb.core.parser.node.PRecEntry;
import de.be4.classicalb.core.parser.node.Start;
import de.be4.classicalb.core.parser.node.TIdentifierLiteral;
import de.be4.classicalb.core.parser.node.TIntegerLiteral;
import de.be4.classicalb.core.parser.node.TStringLiteral;
import de.tla2b.analysis.BOperation;
import de.tla2b.analysis.SpecAnalyser;
import de.tla2b.config.ConfigfileEvaluator;
import de.tla2b.global.BBuildIns;
import de.tla2b.global.BBuiltInOPs;
import de.tla2b.global.Priorities;
import de.tla2b.global.TranslationGlobals;
import de.tla2b.types.IType;
import de.tla2b.types.SetType;
import de.tla2b.types.StructType;
import de.tla2b.types.TLAType;
import de.tla2b.types.TupleType;

public class BAstCreator extends BuiltInOPs implements TranslationGlobals,
		ASTConstants, IType, BBuildIns, Priorities {
	Start start;
	List<PMachineClause> machineClauseList;
	ConfigfileEvaluator conEval;
	SpecAnalyser specAnalyser;

	private ModuleNode moduleNode;

	public Start getStartNode() {
		return start;
	}

	public BAstCreator(ModuleNode moduleNode, ConfigfileEvaluator conEval,
			SpecAnalyser specAnalyser) {
		this.conEval = conEval;
		this.moduleNode = moduleNode;
		this.specAnalyser = specAnalyser;

		machineClauseList = new ArrayList<PMachineClause>();

		AAbstractMachineParseUnit aAbstractMachineParseUnit = new AAbstractMachineParseUnit();
		aAbstractMachineParseUnit.setVariant(new AMachineMachineVariant());
		AMachineHeader machineHeader = new AMachineHeader();
		List<TIdentifierLiteral> headerName = createTIdentifierLiteral(moduleNode
				.getName().toString());
		machineHeader.setName(headerName);
		aAbstractMachineParseUnit.setHeader(machineHeader);

		createConstantsClause();
		createPropertyClause();
		createVariableClause();
		createInvariantClause();
		createInitClause();
		createOperationsClause();

		aAbstractMachineParseUnit.setMachineClauses(machineClauseList);

		start = new Start(aAbstractMachineParseUnit, new EOF());

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
			for (int j = 0; j < op.getOpParams().size(); j++) {
				paramList.add(createIdentifierNode(op.getOpParams().get(j)));
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
				if (op.getUnchangedVariables().contains(varName))
					continue;
				anyParams.add(createIdentifierNode(varName + "_n"));
			}
			any.setIdentifiers(anyParams);
			any.setWhere(visitExprOrOpArgNodePredicate(op.getNode()));

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
		List<OpDeclNode> bConstants = Arrays.asList(moduleNode
				.getConstantDecls());
		if (bConstants.size() > 0) {
			List<PExpression> list = new ArrayList<PExpression>();
			for (OpDeclNode opDeclNode : bConstants) {
				AIdentifierExpression id = new AIdentifierExpression(
						createTIdentifierLiteral(opDeclNode.getName()
								.toString()));
				list.add(id);
			}
			AAbstractConstantsMachineClause abstractConstantsClause = new AAbstractConstantsMachineClause(
					list);
			machineClauseList.add(abstractConstantsClause);
		}
	}

	private void createPropertyClause() {
		List<PPredicate> list = new ArrayList<PPredicate>();
		AssumeNode[] assumes = moduleNode.getAssumptions();
		if (assumes.length == 0) {
			return;
		}
		for (AssumeNode assumeNode : assumes) {
			list.add(visitAssumeNode(assumeNode));
		}

		APropertiesMachineClause propertiesClause = new APropertiesMachineClause();
		propertiesClause.setPredicates(createConjunction(list));

		machineClauseList.add(propertiesClause);
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
			member.setRight(new AIntegerSetExpression());

			predList.add(member);
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

		case NumeralKind: {
		}

		}

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

		}

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
			return createIdentifierNode(n.getOperator().getName().toString());
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
		// Operator is a B built-in operator
		if (BBuiltInOPs.contains(def.getName())
				&& STANDARD_MODULES.contains(def.getSource()
						.getOriginallyDefinedInModuleNode().getName()
						.toString())) {
			return visitBBuitInsPredicate(n);
		}

		// new Definition or what else

		throw new RuntimeException();
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

		// new Definition or what else

		throw new RuntimeException();
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
			// StringBuilder s = visitExprOrOpArgNode(n.getArgs()[0], d,
			// NOBOOL).out;
			// out.append("(");
			// out.append(s);
			// out.append("/|\\"); // taking first n elements
			// out.append(visitExprOrOpArgNode(n.getArgs()[2], d, NOBOOL).out);
			// out.append(")\\|/"); // dropping first m-1 elements
			// out.append(visitExprOrOpArgNode(n.getArgs()[1], d, NOBOOL).out);
			// out.append("-1");
			// return new ExprReturn(out, P_drop_last);
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
				return new ASequenceExtensionExpression(list);
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

		}

		System.out.println(n.getOperator().getName());
		throw new RuntimeException();
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

		case OPCODE_prime: // prime
		{
			OpApplNode node = (OpApplNode) n.getArgs()[0];
			return new AEqualPredicate(createIdentifierNode(node.getOperator()
					.getName().toString()
					+ "_n"), new ABooleanTrueExpression());
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
				conj.setRight(list.get(i));
				conj = new AConjunctPredicate(conj, null);
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
