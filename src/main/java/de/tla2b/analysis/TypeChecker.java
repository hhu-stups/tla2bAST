package de.tla2b.analysis;

import java.lang.ref.WeakReference;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.tla2b.config.ConfigfileEvaluator;
import de.tla2b.config.TLCValueNode;
import de.tla2b.exceptions.NotImplementedException;
import de.tla2b.exceptions.TLA2BException;
import de.tla2b.exceptions.TLA2BFrontEndException;
import de.tla2b.exceptions.TypeErrorException;
import de.tla2b.exceptions.UnificationException;
import de.tla2b.global.BBuildIns;
import de.tla2b.global.BBuiltInOPs;
import de.tla2b.global.TranslationGlobals;
import de.tla2b.types.AbstractHasFollowers;
import de.tla2b.types.BoolType;
import de.tla2b.types.FunctionType;
import de.tla2b.types.IDefaultableType;
import de.tla2b.types.IntType;
import de.tla2b.types.IntegerOrRealType;
import de.tla2b.types.RealType;
import de.tla2b.types.SetType;
import de.tla2b.types.StringType;
import de.tla2b.types.StructOrFunctionType;
import de.tla2b.types.StructType;
import de.tla2b.types.TLAType;
import de.tla2b.types.TupleOrFunction;
import de.tla2b.types.TupleType;
import de.tla2b.types.UntypedType;
import de.tla2b.util.DebugUtils;

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
import tla2sany.semantic.SemanticNode;
import tla2sany.semantic.StringNode;
import tla2sany.semantic.SymbolNode;
import tlc2.tool.BuiltInOPs;

public class TypeChecker extends BuiltInOPs implements BBuildIns, TranslationGlobals {

	private static final int TEMP_TYPE_ID = 6;
	private int paramId = TYPE_ID;

	private List<ExprNode> inits;
	private ExprNode nextExpr;
	private final Set<OpDefNode> usedDefinitions;
	private final Set<OpDefNode> bDefinitions;

	private final List<SymbolNode> symbolNodeList = new ArrayList<>();
	private final Map<WeakReference<IDefaultableType>, Void> possibleUnfinishedTypes = new HashMap<>();

	private final ModuleNode moduleNode;
	private List<OpDeclNode> bConstList;
	private final SpecAnalyser specAnalyser;

	private Map<OpDeclNode, TLCValueNode> constantAssignments;

	private ConfigfileEvaluator conEval;

	/**
	 * for module translation
	 */
	public TypeChecker(ModuleNode moduleNode, ConfigfileEvaluator conEval, SpecAnalyser specAnalyser) {
		this.moduleNode = moduleNode;
		this.specAnalyser = specAnalyser;
		if (conEval != null) {
			this.bConstList = conEval.getbConstantList();
			this.constantAssignments = conEval.getConstantAssignments();
			this.conEval = conEval;
		}
		this.inits = specAnalyser.getInits();
		this.nextExpr = specAnalyser.getNext();
		this.usedDefinitions = specAnalyser.getUsedDefinitions();
		this.bDefinitions = specAnalyser.getBDefinitions();
	}

	/**
	 * for expression translation
	 */
	public TypeChecker(ModuleNode moduleNode, SpecAnalyser specAnalyser) {
		this.moduleNode = moduleNode;
		this.specAnalyser = specAnalyser;
		OpDefNode[] defs = moduleNode.getOpDefs();
		// use the last definition of the module
		this.usedDefinitions = Collections.singleton(defs[defs.length - 1]);
		this.bDefinitions = specAnalyser.getBDefinitions();
	}

	public void start() throws TLA2BException {
		for (OpDeclNode con : moduleNode.getConstantDecls()) {
			if (constantAssignments != null && constantAssignments.containsKey(con)) {
				setLocalTypeAndFollowers(con, constantAssignments.get(con).getType());
			} else {
				// if constant already has a type: keep type; otherwise add an untyped type
				if (getLocalType(con) == null)
					setLocalTypeAndFollowers(con, new UntypedType());
			}
		}

		for (OpDeclNode var : moduleNode.getVariableDecls()) {
			// if variable already has a type: keep type; otherwise add an untyped type
			if (getLocalType(var) == null)
				setLocalTypeAndFollowers(var, new UntypedType());
		}

		evalDefinitions(moduleNode.getOpDefs());

		if (conEval != null) {
			for (Entry<OpDeclNode, OpDefNode> entry : conEval.getConstantOverrides().entrySet()) {
				OpDeclNode con = entry.getKey();
				if (!bConstList.contains(con))
					continue;

				TLAType defType = getLocalType(entry.getValue());
				TLAType conType = getLocalType(con);
				try {
					setLocalType(con, defType.unify(conType));
				} catch (UnificationException e) {
					throw new TypeErrorException(
						String.format("Expected %s, found %s at constant '%s'.", defType, conType, con.getName()));
				}
			}
		}

		evalAssumptions(moduleNode.getAssumptions());

		if (inits != null) {
			for (ExprNode init : inits) {
				visitExprNode(init, BoolType.getInstance());
			}
		}

		if (nextExpr != null) {
			visitExprNode(nextExpr, BoolType.getInstance());
		}

		checkIfAllIdentifiersHaveAType();
	}

	private void checkIfAllIdentifiersHaveAType() throws TLA2BException {
		for (WeakReference<IDefaultableType> typeRef : possibleUnfinishedTypes.keySet()) {
			IDefaultableType type = typeRef.get();
			if (type != null) {
				type.setToDefault();
			}
		}

		// check if a variable has no type
		for (OpDeclNode var : moduleNode.getVariableDecls()) {
			TLAType varType = getLocalType(var);
			if (varType == null || varType.isUntyped()) {
				throw new TypeErrorException(
					"The type of the variable '" + var.getName() + "' can not be inferred: " + varType);
			}
		}

		// check if a constant has no type, only constants which will appear in
		// the resulting B Machine are considered
		for (OpDeclNode con : moduleNode.getConstantDecls()) {
			if (bConstList == null || bConstList.contains(con)) {
				TLAType conType = getLocalType(con);
				if (conType == null || conType.isUntyped()) {
					throw new TypeErrorException(
						"The type of constant " + con.getName() + " is still untyped: " + conType);
				}
			}
		}

		/* TODO: for (SymbolNode symbol : symbolNodeList) {
			TLAType type = getLocalType(symbol);
			if (type == null || type.isUntyped()) {
				throw new TypeErrorException("Symbol '" + symbol.getName() + "' has no type.\n" + symbol.getLocation());
			}
		}*/
	}

	private void evalDefinitions(OpDefNode[] opDefs) throws TLA2BException {
		for (OpDefNode def : opDefs) {
			// Definition in this module
			String moduleName = def.getOriginallyDefinedInModuleNode().getName().toString();
			if (STANDARD_MODULES.contains(moduleName) || BBuiltInOPs.isBBuiltInOp(def))
				continue;
			if (usedDefinitions.contains(def) || bDefinitions.contains(def))
				visitOpDefNode(def);
		}
	}

	public void visitOpDefNode(OpDefNode def) throws TLA2BException {
		for (FormalParamNode p : def.getParams()) {
			if (p.getArity() > 0) {
				throw new TLA2BFrontEndException(String.format("TLA2B does not support 2nd-order operators: '%s'%n %s ",
					def.getName(), def.getLocation()));
			}
			setLocalTypeAndFollowers(p, new UntypedType());
		}
		TLAType found = visitExprNode(def.getBody(), new UntypedType());
		setLocalTypeAndFollowers(def, found);
	}

	private void evalAssumptions(AssumeNode[] assumptions) throws TLA2BException {
		for (AssumeNode assumeNode : assumptions) {
			visitExprNode(assumeNode.getAssume(), BoolType.getInstance());
		}
	}

	private TLAType visitExprOrOpArgNode(ExprOrOpArgNode n, TLAType expected) throws TLA2BException {
		if (n instanceof ExprNode) {
			return visitExprNode((ExprNode) n, expected);
		} else {
			throw new NotImplementedException("OpArgNode not implemented yet");
		}
	}

	private TLAType visitExprNode(ExprNode exprNode, TLAType expected) throws TLA2BException {
		switch (exprNode.getKind()) {
			case TLCValueKind: {
				TLCValueNode valueNode = (TLCValueNode) exprNode;
				return unify(valueNode.getType(), expected, valueNode.getValue().toString()
					                                            + " (assigned in the configuration file)", exprNode);
			}
			case OpApplKind:
				return visitOpApplNode((OpApplNode) exprNode, expected);
			case NumeralKind:
				return unify(IntType.getInstance(), expected, exprNode.toString(), exprNode);
			case DecimalKind:
				return unify(RealType.getInstance(), expected, exprNode.toString(), exprNode);
			case StringKind:
				return unify(StringType.getInstance(), expected, ((StringNode) exprNode).getRep().toString(), exprNode);
			case AtNodeKind: { // @
				TLAType type = getLocalType((((AtNode) exprNode).getExceptComponentRef()).getArgs()[1]); // right side
				return unifyAndSetLocalTypeWithFollowers(type, expected, "@", exprNode);
			}
			case LetInKind: {
				LetInNode l = (LetInNode) exprNode;
				for (OpDefNode let : l.getLets()) {
					visitOpDefNode(let);
				}
				return visitExprNode(l.getBody(), expected);
			}
			case SubstInKind:
				throw new RuntimeException("SubstInKind should never occur after InstanceTransformation");
			default: // should be only LabelKind
				throw new NotImplementedException("ExprNode not yet supported: " + exprNode.toString(2));
		}
	}

	private TLAType visitOpApplNode(OpApplNode n, TLAType expected) throws TLA2BException {
		switch (n.getOperator().getKind()) {
			case ConstantDeclKind: {
				SymbolNode symbolNode = n.getOperator();
				String vName = symbolNode.getName().toString();
				TLAType c = getLocalType(symbolNode);
				if (c == null) {
					throw new TypeErrorException(vName + " has no type yet!");
				}
				return unifyAndSetLocalTypeWithFollowers(c, expected, vName, n);
			}

			case VariableDeclKind: {
				SymbolNode symbolNode = n.getOperator();
				String vName = symbolNode.getName().toString();
				TLAType v = getLocalType(symbolNode);
				if (v == null) {
					SymbolNode var = this.specAnalyser.getSymbolNodeByName(vName);
					if (var != null) {
						// symbolNode is variable of an expression, e.g. v + 1
						v = getLocalType(var);
					} else {
						throw new TypeErrorException(vName + " has no type yet!");
					}
				}
				return unifyAndSetLocalTypeWithFollowers(v, expected, vName, n);
			}

			case BuiltInKind:
				return evalBuiltInKind(n, expected);

			case FormalParamKind: {
				SymbolNode symbolNode = n.getOperator();
				String vName = symbolNode.getName().toString();
				TLAType t = getLocalType(symbolNode);
				if (t == null) {
					t = new UntypedType(); // TODO is this correct?
					// throw new RuntimeException();
				}
				return unifyAndSetLocalType(t, expected, vName, n);
			}

			case UserDefinedOpKind: {
				OpDefNode def = (OpDefNode) n.getOperator();
				ExprOrOpArgNode[] args = n.getArgs();
				FormalParamNode[] params = def.getParams();

				// Definition is a BBuilt-in definition
				if (BBuiltInOPs.isBBuiltInOp(def)) {
					return evalBBuiltIns(n, expected);
				}

				boolean generic = def.getParams().length != 0;

				TLAType opType = getType(def);
				if (opType == null) {
					int prevParamId = paramId;
					paramId = TYPE_ID;
					try {
						visitOpDefNode(def);
					} finally {
						paramId = prevParamId;
					}
					opType = getType(def);
				}
				if (generic) {
					opType = opType.cloneTLAType();
				}
				expected = unify(opType, expected, def.getName().toString(), def);

				// we have no real monomorphization, one implementation needs to fit all

				// set param types
				assert params.length == args.length;
				for (int i = 0; i < args.length; i++) {
					FormalParamNode param = params[i];
					ExprOrOpArgNode arg = args[i];

					// clone the parameter type, because the parameter type is not
					// set/changed at a definition call
					TLAType pType = getType(param).cloneTLAType();
					pType = visitExprOrOpArgNode(arg, pType);

					// unify both types,
					// set types of the arguments of the definition call to the parameters for reevaluation the def body
					int prevParamId = paramId;
					paramId = TEMP_TYPE_ID;
					try {
						setLocalType(param, pType);
					} finally {
						paramId = prevParamId;
					}
				}

				TLAType found;
				if (generic) {
					// evaluate the body of the definition again
					int prevParamId = paramId;
					paramId = TEMP_TYPE_ID;
					try {
						found = visitExprNode(def.getBody(), expected);
					} finally {
						paramId = prevParamId;
					}
				} else {
					found = expected;
				}

				setLocalTypeAndFollowers(n, found);
				return found;
			}

			default:
				throw new NotImplementedException(n.getOperator().getName().toString());
		}
	}

	private TLAType evalBuiltInKind(OpApplNode n, TLAType expected) throws TLA2BException {
		switch (getOpCode(n.getOperator().getName())) {
			/*
			 * equality and inequality: =, #, /=
			 */
			case OPCODE_eq: // =
			case OPCODE_noteq: { // /=, #
				TLAType opType = unify(BoolType.getInstance(), expected, n);
				TLAType left = visitExprOrOpArgNode(n.getArgs()[0], new UntypedType());
				visitExprOrOpArgNode(n.getArgs()[1], left);
				return opType;
			}

			/*
			 * Logic Operators: \neg, \lnot, \land, \cl, \lor, \dl, \equiv, =>
			 */
			case OPCODE_neg: // Negation
			case OPCODE_lnot: // Negation
			case OPCODE_cl: // $ConjList
			case OPCODE_dl: // $DisjList
			case OPCODE_land: // \land
			case OPCODE_lor: // \lor
			case OPCODE_equiv: // \equiv
			case OPCODE_implies: { // =>
				TLAType opType = unify(BoolType.getInstance(), expected, n);
				for (int i = 0; i < n.getArgs().length; i++) {
					visitExprOrOpArgNode(n.getArgs()[i], BoolType.getInstance());
				}
				return opType;
			}

			/*
			 * Quantification: \A x \in S : P or \E x \in S : P
			 */
			case OPCODE_be: // \E x \in S : P
			case OPCODE_bf: { // \A x \in S : P
				TLAType opType = unify(BoolType.getInstance(), expected, n);
				evalBoundedVariables(n);
				visitExprOrOpArgNode(n.getArgs()[0], BoolType.getInstance());
				return opType;
			}

			/*
			 * Set Operators
			 */
			case OPCODE_se: { // SetEnumeration {..}
				SetType found = (SetType) unify(new SetType(new UntypedType()), expected, n);
				TLAType current = found.getSubType();
				for (ExprOrOpArgNode arg : n.getArgs()) {
					current = visitExprOrOpArgNode(arg, current);
				}
				return found;
			}

			case OPCODE_in: // \in
			case OPCODE_notin: { // \notin
				TLAType boolType = unify(BoolType.getInstance(), expected, n);
				TLAType element = visitExprOrOpArgNode(n.getArgs()[0], new UntypedType());
				visitExprOrOpArgNode(n.getArgs()[1], new SetType(element));
				return boolType;
			}

			case OPCODE_setdiff: // set difference
			case OPCODE_cup: // set union
			case OPCODE_cap: { // set intersection
				TLAType found = unify(new SetType(new UntypedType()), expected, n);
				TLAType left = visitExprOrOpArgNode(n.getArgs()[0], found);
				return visitExprOrOpArgNode(n.getArgs()[1], left); // right
			}

			case OPCODE_subseteq: { // \subseteq - subset or equal
				TLAType boolType = unify(BoolType.getInstance(), expected, n);
				TLAType left = visitExprOrOpArgNode(n.getArgs()[0], new SetType(new UntypedType()));
				visitExprOrOpArgNode(n.getArgs()[1], left);
				return boolType;
			}

			/*
			 * Set Constructor
			 */
			case OPCODE_sso: { // $SubsetOf Represents {x \in S : P}
				SetType found = (SetType) unify(new SetType(evalBoundedVariables(n)), expected, n);
				visitExprOrOpArgNode(n.getArgs()[0], BoolType.getInstance());
				return found;
			}

			case OPCODE_soa: { // $SetOfAll Represents {e : p1 \in S, p2,p3 \in S2}
				SetType found = (SetType) unify(new SetType(new UntypedType()), expected, n);
				evalBoundedVariables(n);
				visitExprOrOpArgNode(n.getArgs()[0], found.getSubType());
				return found;
			}

			case OPCODE_subset: { // SUBSET (conforms POW in B)
				SetType found = (SetType) unify(new SetType(new UntypedType()), expected, n);
				visitExprOrOpArgNode(n.getArgs()[0], found.getSubType());
				return found;
			}

			case OPCODE_union: { // Union - Union{{1},{2}}
				TLAType found = unify(new SetType(new UntypedType()), expected, n);
				SetType setOfSet = (SetType) visitExprOrOpArgNode(n.getArgs()[0], new SetType(found));
				return setOfSet.getSubType();
			}

			/*
			 * Prime
			 */
			case OPCODE_prime: { // prime
				try {
					OpApplNode node = (OpApplNode) n.getArgs()[0];
					if (node.getOperator().getKind() != VariableDeclKind) {
						throw new TypeErrorException(
							"Expected variable at \"" + node.getOperator().getName() + "\":\n" + node.getLocation());
					}
					return visitExprOrOpArgNode(n.getArgs()[0], expected);
				} catch (ClassCastException e) {
					throw new TypeErrorException(
						"Expected variable as argument of prime operator:\n" + n.getArgs()[0].getLocation());
				}
			}

			/*
			 * Tuple: Tuple as Function 1..n to Set (Sequence)
			 */
			case OPCODE_tup: { // $Tuple
				List<TLAType> list = new ArrayList<>();
				for (ExprOrOpArgNode arg : n.getArgs()) {
					list.add(visitExprOrOpArgNode(arg, new UntypedType()));
				}
				TLAType found = TupleOrFunction.createTupleOrFunctionType(list);
				return unifyAndSetLocalTypeWithFollowers(found, expected, "tuple", n);
			}

			/*
			 * Function constructors
			 */
			case OPCODE_rfs: { // recursive function ( f[x\in Nat] == IF x = 0 THEN 1 ELSE f[n-1]
				FormalParamNode recFunc = n.getUnbdedQuantSymbols()[0];
				symbolNodeList.add(recFunc);
				setLocalTypeAndFollowers(recFunc, new FunctionType());

				TLAType domainType = evalBoundedVariables(n);
				FunctionType found = new FunctionType(domainType, new UntypedType());
				visitExprOrOpArgNode(n.getArgs()[0], found.getRange());

				found = (FunctionType) unify(found, expected, n);
				return unify(found, getLocalType(recFunc), n);
			}

			case OPCODE_nrfs: // succ[n \in Nat] == n + 1
			case OPCODE_fc: { // [n \in Nat |-> n+1]
				TLAType domainType = evalBoundedVariables(n);
				FunctionType found = new FunctionType(domainType, new UntypedType());
				visitExprOrOpArgNode(n.getArgs()[0], found.getRange());
				return unify(found, expected, n);
			}

			/*
			 * Function call
			 */
			case OPCODE_fa: { // $FcnApply f[1]
				TLAType domType;
				ExprOrOpArgNode fun = n.getArgs()[0];
				ExprOrOpArgNode dom = n.getArgs()[1];
				if (dom instanceof OpApplNode && ((OpApplNode) dom).getOperator().getName().equals("$Tuple")) {
					List<TLAType> domList = new ArrayList<>();
					for (ExprOrOpArgNode arg : ((OpApplNode) dom).getArgs()) {
						domList.add(visitExprOrOpArgNode(arg, new UntypedType()));
					}
					domType = domList.size() == 1
						          ? new FunctionType(IntType.getInstance(), domList.get(0)) // one-tuple
						          : new TupleType(domList);
				} else if (dom instanceof NumeralNode && ((NumeralNode) dom).val() >= 1) {
					NumeralNode num = (NumeralNode) dom;
					UntypedType u = new UntypedType();
					setLocalTypeAndFollowers(n, u);

					TLAType res = visitExprOrOpArgNode(fun, new TupleOrFunction(num.val(), u));
					setLocalTypeAndFollowers(fun, res);
					return unify(getLocalType(n), expected, fun.toString(), n);
				} else {
					domType = visitExprOrOpArgNode(dom, new UntypedType());
				}
				FunctionType func = new FunctionType(domType, expected);
				setLocalTypeAndFollowers(n, func);
				TLAType res = visitExprOrOpArgNode(n.getArgs()[0], func);
				setLocalTypeAndFollowers(n.getArgs()[0], res);
				return ((FunctionType) res).getRange();
			}

			/*
			 * Domain of Function
			 */
			case OPCODE_domain: {
				FunctionType func = new FunctionType();
				func = (FunctionType) visitExprOrOpArgNode(n.getArgs()[0], func);
				return unify(new SetType(func.getDomain()), expected, n);
			}

			/*
			 * Set of Functions
			 */
			case OPCODE_sof: { // [ A -> B]
				SetType A = (SetType) visitExprOrOpArgNode(n.getArgs()[0], new SetType(new UntypedType()));
				SetType B = (SetType) visitExprOrOpArgNode(n.getArgs()[1], new SetType(new UntypedType()));

				TLAType found = new SetType(new FunctionType(A.getSubType(), B.getSubType()));
				found = unify(found, expected, "set of functions", n);
				return found;
			}

			/*
			 * Except
			 */
			case OPCODE_exc: // $Except
				return evalExcept(n, expected);

			/*
			 * Cartesian Product: A \X B
			 */
			case OPCODE_cp: { // $CartesianProd A \X B \X C as $CartesianProd(A, B, C)
				List<TLAType> list = new ArrayList<>();
				for (int i = 0; i < n.getArgs().length; i++) {
					SetType t = (SetType) visitExprOrOpArgNode(n.getArgs()[i], new SetType(new UntypedType()));
					list.add(t.getSubType());
				}
				TLAType found = new SetType(new TupleType(list));
				found = unify(found, expected, "cartesian product", n);
				return found;
			}

			/*
			 * Records
			 */
			case OPCODE_sor: { // $SetOfRcds [L1 : e1, L2 : e2]
				StructType struct = new StructType();
				for (int i = 0; i < n.getArgs().length; i++) {
					OpApplNode pair = (OpApplNode) n.getArgs()[i];
					StringNode field = (StringNode) pair.getArgs()[0];
					SetType fieldType = (SetType) visitExprOrOpArgNode(pair.getArgs()[1], new SetType(new UntypedType()));
					struct.add(field.getRep().toString(), fieldType.getSubType());
				}
				return unifyAndSetLocalTypeWithFollowers(new SetType(struct), expected, "set of records", n);
			}

			case OPCODE_rc: { // [h_1 |-> 1, h_2 |-> 2]
				StructType found = new StructType();
				for (int i = 0; i < n.getArgs().length; i++) {
					OpApplNode pair = (OpApplNode) n.getArgs()[i];
					StringNode field = (StringNode) pair.getArgs()[0];
					TLAType fieldType = visitExprOrOpArgNode(pair.getArgs()[1], new UntypedType());
					found.add(field.getRep().toString(), fieldType);
				}
				return unifyAndSetLocalTypeWithFollowers(found, expected, "record constructor", n);
			}

			case OPCODE_rs: { // $RcdSelect r.c
				String fieldName = ((StringNode) n.getArgs()[1]).getRep().toString();
				StructType r = (StructType) visitExprOrOpArgNode(n.getArgs()[0], StructType.getIncompleteStruct());

				StructType expectedStruct = StructType.getIncompleteStruct();
				expectedStruct.add(fieldName, expected);

				try {
					r = r.unify(expectedStruct);
				} catch (UnificationException e) {
					throw new TypeErrorException(String.format("Struct has no field %s with type %s: %s%n%s", fieldName,
						r.getType(fieldName), r, n.getLocation()));
				}
				setLocalTypeAndFollowers(n.getArgs()[0], r);
				return r.getType(fieldName);
			}

			/*
			 * miscellaneous constructs
			 */
			case OPCODE_ite: { // IF THEN ELSE
				visitExprOrOpArgNode(n.getArgs()[0], BoolType.getInstance());
				TLAType then = visitExprOrOpArgNode(n.getArgs()[1], expected);
				TLAType eelse = visitExprOrOpArgNode(n.getArgs()[2], then);
				setLocalTypeAndFollowers(n, eelse);
				return eelse;
			}

			case OPCODE_case: {
				/* CASE p1 -> e1 [] p2 -> e2 represented as $Case( $Pair(p1,e1),$Pair(p2, e2) )
				 * and CASE p1 -> e1 [] p2 -> e2 [] OTHER -> e3
				 * represented as $Case( $Pair(p1, e1), $Pair(p2, e2), $Pair(null, e3)) */
				TLAType found = expected;
				for (int i = 0; i < n.getArgs().length; i++) {
					OpApplNode pair = (OpApplNode) n.getArgs()[i];
					if (pair.getArgs()[0] != null) {
						visitExprOrOpArgNode(pair.getArgs()[0], BoolType.getInstance());
					}
					found = visitExprOrOpArgNode(pair.getArgs()[1], found);
				}
				return found;
			}

			case OPCODE_uc: {
				List<TLAType> list = new ArrayList<>();
				for (FormalParamNode param : n.getUnbdedQuantSymbols()) {
					TLAType paramType = new UntypedType();
					symbolNodeList.add(param);
					setLocalTypeAndFollowers(param, paramType);
					list.add(paramType);
				}
				TLAType found;
				if (list.size() == 1) {
					found = list.get(0);
				} else {
					found = new TupleType(list);
				}
				found = unifyAndSetLocalTypeWithFollowers(found, expected, n.getOperator().getName().toString(), n);
				visitExprOrOpArgNode(n.getArgs()[0], BoolType.getInstance());
				return found;
			}

			case OPCODE_bc: { // CHOOSE x \in S: P
				TLAType found = evalBoundedVariables(n);
				found = unify(found, expected, n);
				visitExprOrOpArgNode(n.getArgs()[0], BoolType.getInstance());
				return found;
			}

			case OPCODE_unchanged:
				return BoolType.getInstance().unify(expected);

			/*
			 * no TLA+ Built-ins
			 */
			case 0:
				return evalBBuiltIns(n, expected);

			default:
				throw new NotImplementedException(
					"Not supported Operator: " + n.getOperator().getName() + "\n" + n.getLocation());
		}
	}

	private TLAType evalBoundedVariables(OpApplNode n) throws TLA2BException {
		List<TLAType> domList = new ArrayList<>();
		FormalParamNode[][] params = n.getBdedQuantSymbolLists();
		ExprNode[] bounds = n.getBdedQuantBounds();
		for (int i = 0; i < bounds.length; i++) {
			SetType boundType = (SetType) visitExprNode(bounds[i], new SetType(new UntypedType()));
			TLAType subType = boundType.getSubType();

			if (n.isBdedQuantATuple()[i]) {
				if (params[i].length == 1) {
					FormalParamNode p = params[i][0];
					FunctionType expected = new FunctionType(IntType.getInstance(), new UntypedType());
					expected = (FunctionType) unify(expected, subType, "parameter " + p.getName(), bounds[i]);
					domList.add(expected);
					symbolNodeList.add(p);
					setLocalTypeAndFollowers(p, expected.getRange());
				} else {
					TupleType tuple = new TupleType(params[i].length);
					tuple = (TupleType) unify(tuple, subType, "tuple", bounds[i]);
					domList.add(tuple);
					for (int j = 0; j < params[i].length; j++) {
						FormalParamNode p = params[i][j];
						symbolNodeList.add(p);
						setLocalTypeAndFollowers(p, tuple.getTypes().get(j));
					}
				}
			} else { // is not a tuple: all parameter have the same type
				for (int j = 0; j < params[i].length; j++) {
					domList.add(subType);
					FormalParamNode p = params[i][j];
					symbolNodeList.add(p);
					setLocalTypeAndFollowers(p, subType);
				}
			}
		}
		return domList.size() == 1 ? domList.get(0) : new TupleType(domList);
	}

	private TLAType evalExcept(OpApplNode n, TLAType expected) throws TLA2BException {
		TLAType t = visitExprOrOpArgNode(n.getArgs()[0], expected);
		setLocalTypeAndFollowers(n, t);

		for (int i = 1; i < n.getArgs().length; i++) { // start at 1
			OpApplNode pair = (OpApplNode) n.getArgs()[i];
			// stored for @ node
			UntypedType untyped = new UntypedType();
			setLocalTypeAndFollowers(pair.getArgs()[1], untyped);
			TLAType valueType = visitExprOrOpArgNode(pair.getArgs()[1], untyped); // right side

			OpApplNode seq = (OpApplNode) pair.getArgs()[0]; // left side
			LinkedList<ExprOrOpArgNode> list = new LinkedList<>(Arrays.asList(seq.getArgs()));
			ExprOrOpArgNode domExpr = list.poll();

			if (domExpr instanceof StringNode) {
				String field = ((StringNode) domExpr).getRep().toString();
				TLAType res = evalType(list, valueType);
				t = unify(t, new StructOrFunctionType(field, res), pair);
			} else {
				// Function
				TLAType domType;
				if (domExpr instanceof OpApplNode
						&& ((OpApplNode) domExpr).getOperator().getName().equals("$Tuple")) {
					List<TLAType> domList = new ArrayList<>();
					for (ExprOrOpArgNode arg : ((OpApplNode) domExpr).getArgs()) {
						domList.add(visitExprOrOpArgNode(arg, new UntypedType()));
					}
					domType = new TupleType(domList);
					setLocalType(domExpr, domType); // store type
				} else {
					domType = visitExprOrOpArgNode(domExpr, new UntypedType());
				}

				TLAType rangeType = evalType(list, valueType);
				t = unify(t, new FunctionType(domType, rangeType), pair);
			}
		}
		return t;
	}

	private TLAType evalType(LinkedList<ExprOrOpArgNode> list, TLAType valueType) throws TLA2BException {
		if (list.isEmpty()) {
			return valueType;
		}
		ExprOrOpArgNode head = list.poll();
		if (head instanceof StringNode) {
			// record or function of strings
			String name = ((StringNode) head).getRep().toString();
			return new StructOrFunctionType(name, evalType(list, valueType));
		}
		TLAType t = visitExprOrOpArgNode(head, new UntypedType());
		return new FunctionType(t, evalType(list, valueType));
	}

	private TLAType evalBBuiltIns(OpApplNode n, TLAType expected) throws TLA2BException {
		switch (BBuiltInOPs.getOpcode(n.getOperator().getName())) {
			// B Builtins

			/*
			 * Standard Module Naturals
			 */
			case B_OPCODE_gt: // >
			case B_OPCODE_lt: // <
			case B_OPCODE_leq: // <=
			case B_OPCODE_geq: { // >=
				TLAType boolType = unify(BoolType.getInstance(), expected, n);
				TLAType numberType = new IntegerOrRealType();
				for (ExprOrOpArgNode arg : n.getArgs()) {
					numberType = visitExprOrOpArgNode(arg, numberType);
					setLocalTypeAndFollowers(arg, numberType);
				}
				return boolType;
			}

			// arithmetic operators: support both integers and reals
			// for UntypedTypes the default is integer; if this leads to a TypeErrorException real is tried instead
			case B_OPCODE_plus: // +
			case B_OPCODE_minus: // -
			case B_OPCODE_uminus: // -x
			case B_OPCODE_times: // *
			case B_OPCODE_div: // /
			case B_OPCODE_mod: // % modulo
			case B_OPCODE_exp: { // x to the power of y, x^y
				TLAType type = unify(new IntegerOrRealType(), expected, n);
				for (ExprOrOpArgNode arg : n.getArgs()) {
					type = visitExprOrOpArgNode(arg, type);
					setLocalTypeAndFollowers(arg, type);
				}
				return type;
			}

			case B_OPCODE_realdiv: { // /
				TLAType realType = unify(RealType.getInstance(), expected, n);
				for (ExprOrOpArgNode arg : n.getArgs()) {
					visitExprOrOpArgNode(arg, realType);
				}
				return realType;
			}

			case B_OPCODE_dotdot: { // ..
				TLAType type = unify(new SetType(IntType.getInstance()), expected, n);
				for (ExprOrOpArgNode arg : n.getArgs()) {
					visitExprOrOpArgNode(arg, IntType.getInstance());
				}
				return type;
			}

			case B_OPCODE_nat: // Nat
				return unify(new SetType(IntType.getInstance()), expected, n);

			/*
			 * Standard Module Integers / Reals
			 */
			case B_OPCODE_int: // Int
				return unify(new SetType(IntType.getInstance()), expected, n);

			case B_OPCODE_real: // Real
				return unify(new SetType(RealType.getInstance()), expected, n);

			/*
			 * Standard Module FiniteSets
			 */
			case B_OPCODE_finite: { // IsFiniteSet
				TLAType boolType = unify(BoolType.getInstance(), expected, n);
				visitExprOrOpArgNode(n.getArgs()[0], new SetType(new UntypedType()));
				return boolType;
			}

			case B_OPCODE_card: { // Cardinality
				TLAType intType = unify(IntType.getInstance(), expected, n);
				visitExprOrOpArgNode(n.getArgs()[0], new SetType(new UntypedType()));
				return intType;
			}

			/*
			 * Standard Module Sequences
			 */
			case B_OPCODE_seq: { // Seq(S) - set of sequences, S must be a set
				SetType S = (SetType) visitExprOrOpArgNode(n.getArgs()[0], new SetType(new UntypedType()));
				SetType set_of_seq = new SetType(new FunctionType(IntType.getInstance(), S.getSubType()));
				return unify(set_of_seq, expected, n);
			}

			case B_OPCODE_len: { // length of the sequence
				TLAType intType = unify(IntType.getInstance(), expected, n);
				visitExprOrOpArgNode(n.getArgs()[0], new FunctionType(intType, new UntypedType()));
				return intType;
			}

			case B_OPCODE_conc: { // s \o s2 - concatenation of s and s2
				TLAType found = new FunctionType(IntType.getInstance(), new UntypedType());
				found = visitExprOrOpArgNode(n.getArgs()[0], found);
				found = visitExprOrOpArgNode(n.getArgs()[1], found);
				return unify(found, expected, n);
			}

			case B_OPCODE_append: { // Append(s, e)
				FunctionType found = new FunctionType(IntType.getInstance(), new UntypedType());
				found = (FunctionType) visitExprOrOpArgNode(n.getArgs()[0], found);
				visitExprOrOpArgNode(n.getArgs()[1], found.getRange());
				return unify(found, expected, n);
			}

			case B_OPCODE_head: { // HEAD(s) - the first element of the sequence
				FunctionType func = new FunctionType(IntType.getInstance(), new UntypedType());
				func = (FunctionType) visitExprOrOpArgNode(n.getArgs()[0], func);
				return unify(func.getRange(), expected, n);
			}

			case B_OPCODE_tail: { // Tail(s)
				FunctionType found = new FunctionType(IntType.getInstance(), new UntypedType());
				found = (FunctionType) visitExprOrOpArgNode(n.getArgs()[0], found);
				return unify(found, expected, n);
			}

			case B_OPCODE_subseq: { // SubSeq(s,m,n)
				TLAType found = new FunctionType(IntType.getInstance(), new UntypedType());
				found = visitExprOrOpArgNode(n.getArgs()[0], found);
				visitExprOrOpArgNode(n.getArgs()[1], IntType.getInstance());
				visitExprOrOpArgNode(n.getArgs()[2], IntType.getInstance());
				return unify(found, expected, n);
			}

			// TODO add BSeq to tla standard modules

			/*
			 * Standard Module TLA2B
			 */
			case B_OPCODE_min: // MinOfSet(S)
			case B_OPCODE_max: // MaxOfSet(S)
			case B_OPCODE_setprod: // SetProduct(S)
			case B_OPCODE_setsum: { // SetSummation(S)
				// TODO: do we need support for Reals here?
				TLAType intType = unify(IntType.getInstance(), expected, n);
				visitExprOrOpArgNode(n.getArgs()[0], new SetType(intType));
				return intType;
			}

			case B_OPCODE_permseq: { // PermutedSequences(S)
				SetType argType = (SetType) visitExprOrOpArgNode(n.getArgs()[0], new SetType(new UntypedType()));
				SetType found = new SetType(new FunctionType(IntType.getInstance(), argType.getSubType()));
				return unify(found, expected, n);
			}

			/*
			 * Standard Module TLA2B
			 */
			case B_OPCODE_pow1: { // POW1
				SetType set = new SetType(new UntypedType());
				set = (SetType) visitExprOrOpArgNode(n.getArgs()[0], set);
				SetType found = new SetType(set);
				return unify(found, expected, n);
			}

			/*
			 * Standard Module Relations
			 */
			case B_OPCODE_rel_inverse: { // POW1
				SetType set = new SetType(new TupleType(2));
				set = (SetType) visitExprOrOpArgNode(n.getArgs()[0], set);
				TupleType t = (TupleType) set.getSubType();
				List<TLAType> list = Arrays.asList(t.getTypes().get(1), t.getTypes().get(0));
				SetType found = new SetType(new TupleType(list));
				return unify(found, expected, n);
			}

			/*
			 * TLA+ Built-Ins, but not in tlc.tool.BuiltInOPs
			 */
			case B_OPCODE_bool: // BOOLEAN
				return unify(new SetType(BoolType.getInstance()), expected, n);

			case B_OPCODE_string: // STRING
				return unify(new SetType(StringType.getInstance()), expected, n);

			case B_OPCODE_true:
			case B_OPCODE_false:
			case B_OPCODE_assert:
				return unify(BoolType.getInstance(), expected, n);

			default: {
				throw new NotImplementedException(n.getOperator().getName().toString());
			}
		}
	}

	/*
	 * Utility methods
	 */
	private static boolean hasGlobalTyping(SemanticNode node) {
		SymbolNode symbol = null;
		if (node instanceof SymbolNode) {
			symbol = (SymbolNode) node;
		} else if (node instanceof OpApplNode) {
			symbol = ((OpApplNode) node).getOperator();
		}

		return symbol != null && (symbol.getKind() == ConstantDeclKind || symbol.getKind() == VariableDeclKind);
	}

	private void setLocalTypeAndFollowers(SemanticNode node, TLAType type) {
		setLocalType(node, type);
		if (type instanceof AbstractHasFollowers) {
			((AbstractHasFollowers) type).addFollower(node);
		}
	}

	public static void updateTypeAndFollowers(SemanticNode node, TLAType oldType, TLAType newType) {
		if (getType(node, TYPE_ID) == oldType) {
			setType(node, newType, TYPE_ID);
			if (newType instanceof AbstractHasFollowers) {
				((AbstractHasFollowers) newType).addFollower(node);
			}
		}
		if (getType(node, TEMP_TYPE_ID) == oldType) {
			setType(node, newType, TEMP_TYPE_ID);
			if (newType instanceof AbstractHasFollowers) {
				((AbstractHasFollowers) newType).addFollower(node);
			}
		}
	}

	private static void setType(SemanticNode node, TLAType type, int paramId) {
		node.setToolObject(paramId, type);
	}

	private void setLocalType(SemanticNode node, TLAType type) {
		if (type instanceof IDefaultableType) {
			this.possibleUnfinishedTypes.put(new WeakReference<>((IDefaultableType) type), null);
		}
		if (paramId != TYPE_ID && hasGlobalTyping(node)) {
			setType(node, type, TYPE_ID);
		} else {
			setType(node, type, paramId);
		}
	}

	public static void setType(SemanticNode node, TLAType type) {
		setType(node, type, TYPE_ID);
	}

	private static TLAType getType(SemanticNode node, int paramId) {
		return (TLAType) node.getToolObject(paramId);
	}

	private TLAType getLocalType(SemanticNode node) {
		if (paramId != TYPE_ID && hasGlobalTyping(node)) {
			return getType(node, TYPE_ID);
		}
		return getType(node, paramId);
	}

	public static TLAType getType(SemanticNode node) {
		return getType(node, TYPE_ID);
	}

	private static TLAType unify(TLAType toUnify, TLAType expected, String opMsg, SemanticNode n) throws TypeErrorException {
		TLAType found = toUnify;
		DebugUtils.printDebugMsg("Unify " + found + " and " + expected + " at '" + opMsg + "' (" + n.getLocation() + ")");
		try {
			found = found.unify(expected);
		} catch (UnificationException e) {
			throw new TypeErrorException(String.format("Expected '%s', found '%s' at %s,%n%s",
					expected, found, "'" + opMsg + "'", n.getLocation()));
		}
		return found;
	}

	private static TLAType unify(TLAType toUnify, TLAType expected, OpApplNode n) throws TypeErrorException {
		return unify(toUnify, expected, n.getOperator().getName().toString(), n);
	}

	private TLAType unifyAndSetLocalTypeWithFollowers(TLAType toUnify, TLAType expected, String opMsg, SemanticNode n) throws TypeErrorException {
		TLAType found = unify(toUnify, expected, opMsg, n);
		setLocalTypeAndFollowers(n, found);
		return found;
	}

	private TLAType unifyAndSetLocalType(TLAType toUnify, TLAType expected, String opMsg, SemanticNode n) throws TypeErrorException {
		TLAType found = unify(toUnify, expected, opMsg, n);
		setLocalType(n, found);
		return found;
	}
}
