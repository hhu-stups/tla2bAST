package de.tla2b.analysis;

import de.tla2b.config.ConfigfileEvaluator;
import de.tla2b.config.TLCValueNode;
import de.tla2b.exceptions.*;
import de.tla2b.global.BBuildIns;
import de.tla2b.global.BBuiltInOPs;
import de.tla2b.global.TranslationGlobals;
import de.tla2b.types.*;
import tla2sany.semantic.*;
import tlc2.tool.BuiltInOPs;

import java.util.*;
import java.util.Map.Entry;

public class TypeChecker extends BuiltInOPs implements BBuildIns, TranslationGlobals {

	private static final int TEMP_TYPE_ID = 6;
	private int paramId;

	private List<ExprNode> inits;
	private ExprNode nextExpr;
	private final Set<OpDefNode> usedDefinitions;
	private final Set<OpDefNode> bDefinitions;

	private final List<SymbolNode> symbolNodeList = new ArrayList<>();
	private final List<SemanticNode> tupleNodeList = new ArrayList<>();

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
		this.paramId = TYPE_ID;
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
		this.paramId = TYPE_ID;
	}

	public void start() throws TLA2BException {
		for (OpDeclNode con : moduleNode.getConstantDecls()) {
			if (constantAssignments != null && constantAssignments.containsKey(con)) {
				setType(con, constantAssignments.get(con).getType());
			} else {
				// if constant already has a type: keep type; otherwise add an untyped type
				if (con.getToolObject(TYPE_ID) == null)
					setType(con, new UntypedType());
			}
		}

		for (OpDeclNode var : moduleNode.getVariableDecls()) {
			// if variable already has a type: keep type; otherwise add an untyped type
			if (var.getToolObject(TYPE_ID) == null)
				setType(var, new UntypedType());
		}

		evalDefinitions(moduleNode.getOpDefs());

		if (conEval != null) {
			for (Entry<OpDeclNode, OpDefNode> entry : conEval.getConstantOverrides().entrySet()) {
				OpDeclNode con = entry.getKey();
				if (!bConstList.contains(con))
					continue;

				TLAType defType = (TLAType) entry.getValue().getToolObject(TYPE_ID);
				TLAType conType = (TLAType) con.getToolObject(TYPE_ID);
				try {
					setType(con, defType.unify(conType));
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

	private void checkIfAllIdentifiersHaveAType() throws TypeErrorException {
		// check if a variable has no type
		for (OpDeclNode var : moduleNode.getVariableDecls()) {
			TLAType varType = getType(var);
			if (varType.isUntyped()) {
				throw new TypeErrorException(
					"The type of the variable '" + var.getName() + "' can not be inferred: " + varType);
			}
		}

		// check if a constant has no type, only constants which will appear in
		// the resulting B Machine are considered
		for (OpDeclNode con : moduleNode.getConstantDecls()) {
			if (bConstList == null || bConstList.contains(con)) {
				TLAType conType = getType(con);
				if (conType.isUntyped()) {
					throw new TypeErrorException(
						"The type of constant " + con.getName() + " is still untyped: " + conType);
				}
			}
		}

		for (SymbolNode symbol : symbolNodeList) {
			TLAType type = getType(symbol);
			if (type.isUntyped()) {
				throw new TypeErrorException("Symbol '" + symbol.getName() + "' has no type.\n" + symbol.getLocation());
			}
		}

		for (SemanticNode tuple : tupleNodeList) {
			TLAType type = getType(tuple);
			if (type instanceof TupleOrFunction) {
				((TupleOrFunction) type).getFinalType();
			}
			// TODO: does this do anything?
		}
	}

	private void evalDefinitions(OpDefNode[] opDefs) throws TLA2BException {
		for (OpDefNode def : opDefs) {
			// Definition in this module
			String moduleName1 = def.getOriginallyDefinedInModuleNode().getName().toString();
			String moduleName2 = def.getSource().getOriginallyDefinedInModuleNode().getName().toString();

			if (STANDARD_MODULES.contains(moduleName1) || STANDARD_MODULES.contains(moduleName2)) {
				continue;
			}
			if (usedDefinitions.contains(def) || bDefinitions.contains(def))
				visitOpDefNode(def);
		}
	}

	public void visitOpDefNode(OpDefNode def) throws TLA2BException {
		for (FormalParamNode p : def.getParams()) {
			if (p.getArity() > 0) {
				throw new TLA2BFrontEndException(String.format("TLA2B do not support 2nd-order operators: '%s'%n %s ",
					def.getName(), def.getLocation()));
			}
			setType(p, new UntypedType(), paramId);
		}
		UntypedType u = new UntypedType();
		// TODO: check this
		// def.setToolObject(TYPE_ID, u);
		// u.addFollower(def);
		setType(def, visitExprNode(def.getBody(), u));
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
				try {
					return valueNode.getType().unify(expected);
				} catch (UnificationException e) {
					throw new TypeErrorException(
						String.format("Expected %s, found %s at '%s'(assigned in the configuration file),%n%s ",
							expected, valueNode.getType(), valueNode.getValue(), exprNode.getLocation()));
				}
			}

			case OpApplKind:
				return visitOpApplNode((OpApplNode) exprNode, expected);

			case NumeralKind:
				try {
					return IntType.getInstance().unify(expected);
				} catch (UnificationException e) {
					throw new TypeErrorException(String.format("Expected %s, found INTEGER at '%s',%n%s ", expected,
						((NumeralNode) exprNode).val(), exprNode.getLocation()));
				}
			case DecimalKind: {
				try {
					return RealType.getInstance().unify(expected);
				} catch (UnificationException e) {
					throw new TypeErrorException(String.format("Expected %s, found REAL at '%s',%n%s ", expected,
						exprNode, exprNode.getLocation()));
				}
			}
			case StringKind: {
				try {
					return StringType.getInstance().unify(expected);
				} catch (UnificationException e) {
					throw new TypeErrorException(String.format("Expected %s, found STRING at '%s',%n%s ", expected,
						((StringNode) exprNode).getRep(), exprNode.getLocation()));
				}
			}
			case AtNodeKind: { // @
				AtNode a = (AtNode) exprNode;
				OpApplNode pair2 = a.getExceptComponentRef();
				ExprOrOpArgNode rightside = pair2.getArgs()[1];
				TLAType type = (TLAType) rightside.getToolObject(TYPE_ID);
				try {
					TLAType res = type.unify(expected);
					setType(exprNode, res);
					return res;
				} catch (UnificationException e) {
					throw new TypeErrorException(
						String.format("Expected %s, found %s at '@',%n%s ", expected, type, exprNode.getLocation()));
				}
			}

			case LetInKind: {
				LetInNode l = (LetInNode) exprNode;
				for (int i = 0; i < l.getLets().length; i++) {
					visitOpDefNode(l.getLets()[i]);
				}
				return visitExprNode(l.getBody(), expected);
			}

			case SubstInKind: {
				throw new RuntimeException("SubstInKind should never occur after InstanceTransformation");
			}
		}
		throw new NotImplementedException(exprNode.toString(2));
	}

	private TLAType visitOpApplNode(OpApplNode n, TLAType expected) throws TLA2BException {

		switch (n.getOperator().getKind()) {
			case ConstantDeclKind: {
				OpDeclNode con = (OpDeclNode) n.getOperator();

				TLAType c = (TLAType) con.getToolObject(TYPE_ID);
				if (c == null) {
					throw new TypeErrorException(con.getName() + " has no type yet!");
				}
				try {
					TLAType result = expected.unify(c);
					con.setToolObject(TYPE_ID, result);
					return result;
				} catch (UnificationException e) {
					throw new TypeErrorException(String.format("Expected %s, found %s at constant '%s',%n%s", expected, c,
						con.getName(), n.getLocation())
					);
				}
			}

			case VariableDeclKind: {
				SymbolNode symbolNode = n.getOperator();
				String vName = symbolNode.getName().toString();
				TLAType v = (TLAType) symbolNode.getToolObject(TYPE_ID);
				if (v == null) {
					SymbolNode var = this.specAnalyser.getSymbolNodeByName(vName);
					if (var != null) {
						// symbolNode is variable of an expression, e.g. v + 1
						v = (TLAType) var.getToolObject(TYPE_ID);
					} else {
						throw new TypeErrorException(vName + " has no type yet!");
					}
				}
				try {
					TLAType result = expected.unify(v);
					symbolNode.setToolObject(TYPE_ID, result);
					return result;
				} catch (UnificationException e) {
					throw new TypeErrorException(String.format("Expected %s, found %s at variable '%s',%n%s", expected, v,
						vName, n.getLocation()));
				}
			}

			case BuiltInKind: {
				return evalBuiltInKind(n, expected);
			}

			case FormalParamKind: {
				SymbolNode symbolNode = n.getOperator();
				String pName = symbolNode.getName().toString();
				TLAType t = (TLAType) symbolNode.getToolObject(paramId);
				if (t == null) {
					t = (TLAType) symbolNode.getToolObject(TYPE_ID);
				}

				if (t == null) {
					t = new UntypedType(); // TODO is this correct?
					// throw new RuntimeException();
				}
				try {
					TLAType result = expected.unify(t);
					symbolNode.setToolObject(paramId, result);
					return result;
				} catch (UnificationException e) {
					throw new TypeErrorException(String.format("Expected %s, found %s at parameter '%s',%n%s", expected, t,
						pName, n.getLocation()));
				}
			}

			case UserDefinedOpKind: {
				OpDefNode def = (OpDefNode) n.getOperator();

				// Definition is a BBuilt-in definition
				String sourceModule = def.getSource().getOriginallyDefinedInModuleNode().getName().toString();
				if (BBuiltInOPs.contains(def.getName()) && STANDARD_MODULES.contains(sourceModule)) {
					return evalBBuiltIns(n, expected);
				}

				TLAType found = ((TLAType) def.getToolObject(TYPE_ID));
				if (found == null) {
					found = new UntypedType();
					// throw new RuntimeException(def.getName() +
					// " has no type yet!");
				}
				if (n.getArgs().length != 0) {
					found = found.cloneTLAType();
				}

				try {
					found = found.unify(expected);
				} catch (UnificationException e) {
					throw new TypeErrorException(String.format("Expected %s, found %s at definition '%s',%n%s", expected,
						found, def.getName(), n.getLocation()));
				}
				boolean untyped = false;
				FormalParamNode[] params = def.getParams();
				for (int i = 0; i < n.getArgs().length; i++) {
					// clone the parameter type, because the parameter type is not
					// set/changed at a definition call
					FormalParamNode p = params[i];
					TLAType pType = ((TLAType) p.getToolObject(TYPE_ID));
					if (pType == null) {
						pType = new UntypedType();
						// throw new RuntimeException("Parameter " + p.getName()
						// + " has no type yet!%n" + p.getLocation());
					}
					pType = pType.cloneTLAType();
					if (pType.isUntyped())
						untyped = true;

					pType = visitExprOrOpArgNode(n.getArgs()[i], pType); // unify
					// both
					// types
					// set types of the arguments of the definition call to the
					// parameters for reevaluation the def body
					p.setToolObject(TEMP_TYPE_ID, pType);
				}

				if (found.isUntyped() || untyped || !def.getInRecursive()) {
					// evaluate the body of the definition again
					paramId = TEMP_TYPE_ID;
					found = visitExprNode(def.getBody(), found);
					paramId = TYPE_ID;
				}

				n.setToolObject(TYPE_ID, found);

				return found;

			}

			default: {
				throw new NotImplementedException(n.getOperator().getName().toString());
			}
		}

	}

	private TLAType evalBuiltInKind(OpApplNode n, TLAType expected) throws TLA2BException {

		switch (getOpCode(n.getOperator().getName())) {

			/*
			 * equality and disequality: =, #, /=
			 */
			case OPCODE_eq: // =
			case OPCODE_noteq: // /=, #
			{
				try {
					BoolType.getInstance().unify(expected);
				} catch (UnificationException e) {
					throw new TypeErrorException(String.format("Expected %s, found BOOL at '%s',%n%s", expected,
						n.getOperator().getName(), n.getLocation()));
				}
				TLAType left = visitExprOrOpArgNode(n.getArgs()[0], new de.tla2b.types.UntypedType());
				visitExprOrOpArgNode(n.getArgs()[1], left);
				return BoolType.getInstance();
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
			case OPCODE_implies: // =>
			{
				try {
					BoolType.getInstance().unify(expected);
				} catch (UnificationException e) {
					throw new TypeErrorException(String.format("Expected %s, found BOOL at '%s',%n%s", expected,
						n.getOperator().getName(), n.getLocation()));
				}
				for (int i = 0; i < n.getArgs().length; i++) {
					visitExprOrOpArgNode(n.getArgs()[i], BoolType.getInstance());
				}
				return BoolType.getInstance();
			}

			/*
			 * Quantification: \A x \in S : P or \E x \in S : P
			 */
			case OPCODE_be: // \E x \in S : P
			case OPCODE_bf: // \A x \in S : P
			{
				try {
					BoolType.getInstance().unify(expected);
				} catch (UnificationException e) {
					throw new TypeErrorException(String.format("Expected %s, found BOOL at '%s',%n%s", expected,
						n.getOperator().getName(), n.getLocation()));
				}
				evalBoundedVariables(n);
				visitExprOrOpArgNode(n.getArgs()[0], BoolType.getInstance());
				return BoolType.getInstance();
			}

			/*
			 * Set Operators
			 */
			case OPCODE_se: // SetEnumeration {..}
			{
				SetType found = new SetType(new UntypedType());
				try {
					found = found.unify(expected);
				} catch (UnificationException e) {
					throw new TypeErrorException(
						String.format("Expected %s, found POW(_A) at set enumeration,%n%s", expected, n.getLocation()));
				}
				TLAType current = found.getSubType();
				for (int i = 0; i < n.getArgs().length; i++) {
					current = visitExprOrOpArgNode(n.getArgs()[i], current);
				}
				return found;
			}

			case OPCODE_in: // \in
			case OPCODE_notin: // \notin
			{
				if (!BoolType.getInstance().compare(expected)) {
					throw new TypeErrorException(String.format("Expected %s, found BOOL at '%s',%n%s", expected,
						n.getOperator().getName(), n.getLocation()));
				}
				TLAType element = visitExprOrOpArgNode(n.getArgs()[0], new UntypedType());
				visitExprOrOpArgNode(n.getArgs()[1], new SetType(element));

				return BoolType.getInstance();
			}

			case OPCODE_setdiff: // set difference
			case OPCODE_cup: // set union
			case OPCODE_cap: // set intersection
			{
				SetType found = new SetType(new UntypedType());
				try {
					found = found.unify(expected);
				} catch (UnificationException e) {
					throw new TypeErrorException(String.format("Expected %s, found POW(_A) at '%s',%n%s", expected,
						n.getOperator().getName(), n.getLocation()));
				}
				TLAType left = visitExprOrOpArgNode(n.getArgs()[0], found);
				TLAType right = visitExprOrOpArgNode(n.getArgs()[1], left);
				return right;
			}

			case OPCODE_subseteq: // \subseteq - subset or equal
			{
				try {
					BoolType.getInstance().unify(expected);
				} catch (UnificationException e) {
					throw new TypeErrorException(String.format("Expected %s, found BOOL at '%s',%n%s", expected,
						n.getOperator().getName(), n.getLocation()));
				}
				TLAType left = visitExprOrOpArgNode(n.getArgs()[0], new SetType(new UntypedType()));
				visitExprOrOpArgNode(n.getArgs()[1], left);
				return BoolType.getInstance();
			}

			/*
			 * Set Constructor
			 */
			case OPCODE_sso: // $SubsetOf Represents {x \in S : P}
			{

				TLAType domainType = evalBoundedVariables(n);
				SetType found = new SetType(domainType);
				try {
					found = found.unify(expected);
				} catch (UnificationException e) {
					throw new TypeErrorException(String.format("Expected %s, found %s at '%s',%n%s", expected, found,
						n.getOperator().getName(), n.getLocation()));
				}
				visitExprOrOpArgNode(n.getArgs()[0], BoolType.getInstance());
				return found;
			}

			case OPCODE_soa: // $SetOfAll Represents {e : p1 \in S, p2,p3 \in S2}
			{
				SetType found = new SetType(new UntypedType());
				try {
					found = found.unify(expected);
				} catch (UnificationException e) {
					throw new TypeErrorException(String.format("Expected %s, found POW(_A) at '%s',%n%s", expected,
						n.getOperator().getName(), n.getLocation()));
				}
				evalBoundedVariables(n);
				visitExprOrOpArgNode(n.getArgs()[0], found.getSubType());
				return found;
			}

			case OPCODE_subset: // SUBSET (conforms POW in B)
			{
				SetType found = new SetType(new UntypedType());
				try {
					found = found.unify(expected);
				} catch (UnificationException e) {
					throw new TypeErrorException(
						String.format("Expected %s, found POW(_A) at 'SUBSET',%n%s", expected, n.getLocation()));
				}
				visitExprOrOpArgNode(n.getArgs()[0], found.getSubType());
				return found;
			}

			case OPCODE_union: // Union - Union{{1},{2}}
			{
				SetType found = new SetType(new UntypedType());
				try {
					found = found.unify(expected);
				} catch (UnificationException e) {
					throw new TypeErrorException(
						String.format("Expected %s, found POW(_A) at 'SUBSET',%n%s", expected, n.getLocation()));
				}
				SetType setOfSet = (SetType) visitExprOrOpArgNode(n.getArgs()[0], new SetType(found));
				return setOfSet.getSubType();
			}

			/*
			 * Prime
			 */
			case OPCODE_prime: // prime
			{
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
				ArrayList<TLAType> list = new ArrayList<>();
				for (int i = 0; i < n.getArgs().length; i++) {
					list.add(visitExprOrOpArgNode(n.getArgs()[i], new UntypedType()));
				}
				TLAType found;
				if (list.isEmpty()) {
					found = new FunctionType(IntType.getInstance(), new UntypedType());
				} else if (list.size() == 1) {
					found = new FunctionType(IntType.getInstance(), list.get(0));
				} else {
					found = TupleOrFunction.createTupleOrFunctionType(list);
					// found = new TupleType(list);
				}
				try {
					found = found.unify(expected);
				} catch (UnificationException e) {
					throw new TypeErrorException(
						String.format("Expected %s, found %s at Tuple,%n%s", expected, found, n.getLocation()));
				}
				n.setToolObject(TYPE_ID, found);
				tupleNodeList.add(n);
				if (found instanceof AbstractHasFollowers) {
					((AbstractHasFollowers) found).addFollower(n);
				}
				return found;
			}

			/*
			 * Function constructors
			 */
			case OPCODE_rfs: // recursive function ( f[x\in Nat] == IF x = 0 THEN 1
				// ELSE f[n-1]
			{

				FormalParamNode recFunc = n.getUnbdedQuantSymbols()[0];
				symbolNodeList.add(recFunc);
				FunctionType recType = new FunctionType();
				recFunc.setToolObject(TYPE_ID, recType);
				recType.addFollower(recFunc);

				TLAType domainType = evalBoundedVariables(n);
				FunctionType found = new FunctionType(domainType, new UntypedType());
				visitExprOrOpArgNode(n.getArgs()[0], found.getRange());

				try {
					found = (FunctionType) found.unify(expected);
				} catch (UnificationException e) {
					throw new TypeErrorException("Expected '" + expected + "', found '" + found + "'.\n" + n.getLocation());
				}

				TLAType t = null;
				try {
					t = (TLAType) recFunc.getToolObject(TYPE_ID);
					found = (FunctionType) found.unify(t);
				} catch (UnificationException e) {
					throw new TypeErrorException("Expected '" + expected + "', found '" + t + "'.\n" + n.getLocation());
				}

				return found;
			}

			case OPCODE_nrfs: // succ[n \in Nat] == n + 1
			case OPCODE_fc: // [n \in Nat |-> n+1]
			{
				TLAType domainType = evalBoundedVariables(n);
				FunctionType found = new FunctionType(domainType, new UntypedType());
				visitExprOrOpArgNode(n.getArgs()[0], found.getRange());

				try {
					found = (FunctionType) found.unify(expected);
				} catch (UnificationException e) {
					throw new TypeErrorException("Expected '" + expected + "', found '" + found + "'.\n" + n.getLocation());
				}
				return found;
			}

			/*
			 * Function call
			 */
			case OPCODE_fa: // $FcnApply f[1]
			{
				TLAType domType;
				ExprOrOpArgNode dom = n.getArgs()[1];
				if (dom instanceof OpApplNode && ((OpApplNode) dom).getOperator().getName().toString().equals("$Tuple")) {
					ArrayList<TLAType> domList = new ArrayList<>();
					OpApplNode domOpAppl = (OpApplNode) dom;
					for (int i = 0; i < domOpAppl.getArgs().length; i++) {
						TLAType d = visitExprOrOpArgNode(domOpAppl.getArgs()[i], new UntypedType());
						domList.add(d);
					}

					if (domList.size() == 1) { // one-tuple
						domType = new FunctionType(IntType.getInstance(), domList.get(0));
						FunctionType func = new FunctionType(domType, expected);
						TLAType res = visitExprOrOpArgNode(n.getArgs()[0], func);
						return ((FunctionType) res).getRange();
					} else {
						domType = new TupleType(domList);
						FunctionType func = new FunctionType(domType, expected);
						TLAType res = visitExprOrOpArgNode(n.getArgs()[0], func);
						return ((FunctionType) res).getRange();
					}
				} else {
					ExprOrOpArgNode arg = n.getArgs()[1];
					if (arg instanceof NumeralNode) {
						NumeralNode num = (NumeralNode) arg;
						UntypedType u = new UntypedType();
						n.setToolObject(TYPE_ID, u);
						u.addFollower(n);
						TupleOrFunction tupleOrFunc = new TupleOrFunction(num.val(), u);

						TLAType res = visitExprOrOpArgNode(n.getArgs()[0], tupleOrFunc);
						n.getArgs()[0].setToolObject(TYPE_ID, res);
						tupleNodeList.add(n.getArgs()[0]);
						if (res instanceof AbstractHasFollowers) {
							((AbstractHasFollowers) res).addFollower(n.getArgs()[0]);
						}
						TLAType found = (TLAType) n.getToolObject(TYPE_ID);
						try {
							found = found.unify(expected);
						} catch (UnificationException e) {
							throw new TypeErrorException("Expected '" + expected + "', found '" + found + "'.\n"
								+ n.getArgs()[0].toString(2) + "\n" + n.getLocation());
						}
						return found;
					}
					domType = visitExprOrOpArgNode(n.getArgs()[1], new UntypedType());
				}
				FunctionType func = new FunctionType(domType, expected);
				TLAType res = visitExprOrOpArgNode(n.getArgs()[0], func);
				return ((FunctionType) res).getRange();

			}

			/*
			 * Domain of Function
			 */
			case OPCODE_domain: {

				FunctionType func = new FunctionType(new UntypedType(), new UntypedType());
				func = (FunctionType) visitExprOrOpArgNode(n.getArgs()[0], func);
				TLAType res;
				try {
					res = new SetType(func.getDomain()).unify(expected);
				} catch (UnificationException e) {
					throw new TypeErrorException(String.format("Expected '%s', found '%s' at 'DOMAIN(..)',%n%s", expected,
						func, n.getLocation()));
				}
				return res;
			}
			/*
			 * Set of Function
			 */
			case OPCODE_sof: // [ A -> B]
			{
				SetType A = (SetType) visitExprOrOpArgNode(n.getArgs()[0], new SetType(new UntypedType()));
				SetType B = (SetType) visitExprOrOpArgNode(n.getArgs()[1], new SetType(new UntypedType()));

				SetType found = new SetType(new FunctionType(A.getSubType(), B.getSubType()));
				try {
					found = found.unify(expected);
				} catch (UnificationException e) {
					throw new TypeErrorException(String.format("Expected '%s', found '%s' at Set of Function,%n%s",
						expected, found, n.getLocation()));
				}
				return found;
			}

			/*
			 * Except
			 */
			case OPCODE_exc: // $Except
			{
				return evalExcept(n, expected);
			}

			/*
			 * Cartesian Product: A \X B
			 */
			case OPCODE_cp: // $CartesianProd A \X B \X C as $CartesianProd(A, B, C)
			{
				ArrayList<TLAType> list = new ArrayList<>();
				for (int i = 0; i < n.getArgs().length; i++) {
					SetType t = (SetType) visitExprOrOpArgNode(n.getArgs()[i], new SetType(new UntypedType()));
					list.add(t.getSubType());
				}
				SetType found = new SetType(new TupleType(list));
				try {
					found = found.unify(expected);
				} catch (UnificationException e) {
					throw new TypeErrorException(String.format("Expected %s, found %s at Cartesian Product,%n%s", expected,
						found, n.getLocation()));
				}

				return found;
			}

			/*
			 * Records
			 */
			case OPCODE_sor: // $SetOfRcds [L1 : e1, L2 : e2]
			{
				StructType struct = new StructType();
				for (int i = 0; i < n.getArgs().length; i++) {
					OpApplNode pair = (OpApplNode) n.getArgs()[i];
					StringNode field = (StringNode) pair.getArgs()[0];
					SetType fieldType = (SetType) visitExprOrOpArgNode(pair.getArgs()[1], new SetType(new UntypedType()));
					struct.add(field.getRep().toString(), fieldType.getSubType());
				}

				SetType found = new SetType(struct);
				try {
					found = found.unify(expected);
				} catch (UnificationException e) {
					throw new TypeErrorException(String.format("Expected %s, found %s at Set of Records,%n%s", expected,
						found, n.getLocation()));
				}
				n.setToolObject(TYPE_ID, found);
				found.addFollower(n);
				return found;
			}

			case OPCODE_rc: // [h_1 |-> 1, h_2 |-> 2]
			{
				StructType found = new StructType();
				for (int i = 0; i < n.getArgs().length; i++) {
					OpApplNode pair = (OpApplNode) n.getArgs()[i];
					StringNode field = (StringNode) pair.getArgs()[0];
					TLAType fieldType = visitExprOrOpArgNode(pair.getArgs()[1], new UntypedType());
					found.add(field.getRep().toString(), fieldType);
				}
				try {
					found = found.unify(expected);
				} catch (UnificationException e) {
					throw new TypeErrorException(
						String.format("Expected %s, found %s at Record,%n%s", expected, found, n.getLocation()));
				}
				n.setToolObject(TYPE_ID, found);
				found.addFollower(n);

				return found;

			}

			case OPCODE_rs: // $RcdSelect r.c
			{
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
				n.getArgs()[0].setToolObject(TYPE_ID, r);
				r.addFollower(n.getArgs()[0]);
				return r.getType(fieldName);
			}

			/*
			 * miscellaneous constructs
			 */
			case OPCODE_ite: // IF THEN ELSE
			{
				visitExprOrOpArgNode(n.getArgs()[0], BoolType.getInstance());
				TLAType then = visitExprOrOpArgNode(n.getArgs()[1], expected);
				TLAType eelse = visitExprOrOpArgNode(n.getArgs()[2], then);
				n.setToolObject(TYPE_ID, eelse);
				if (eelse instanceof AbstractHasFollowers) {
					((AbstractHasFollowers) eelse).addFollower(n);
				}
				return eelse;
			}

			case OPCODE_case: {
				/*
				 * CASE p1 -> e1 [] p2 -> e2 represented as $Case( $Pair(p1,
				 * e1),$Pair(p2, e2) ) and CASE p1 -> e1 [] p2 -> e2 [] OTHER -> e3
				 * represented as $Case( $Pair(p1, e1), $Pair(p2, e2), $Pair(null,
				 * e3))
				 */
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
					setType(param, paramType);
					list.add(paramType);
				}
				TLAType found;
				if (list.size() == 1) {
					found = list.get(0);
				} else {
					found = new TupleType(list);
				}
				try {
					found = found.unify(expected);
				} catch (UnificationException e) {
					throw new TypeErrorException(
						String.format("Expected %s, found %s at 'CHOOSE',%n%s", expected, found, n.getLocation()));
				}
				setType(n, found);
				visitExprOrOpArgNode(n.getArgs()[0], BoolType.getInstance());

				return getType(n);

			}

			case OPCODE_bc: { // CHOOSE x \in S: P
				TLAType found = evalBoundedVariables(n);
				try {
					found = found.unify(expected);
				} catch (UnificationException e) {
					throw new TypeErrorException(
						String.format("Expected %s, found %s at 'CHOOSE',%n%s", expected, found, n.getLocation()));
				}
				visitExprOrOpArgNode(n.getArgs()[0], BoolType.getInstance());
				return found;
			}

			case OPCODE_unchanged: {
				return BoolType.getInstance().unify(expected);
			}

			/*
			 * no TLA+ Built-ins
			 */
			case 0: {
				return evalBBuiltIns(n, expected);
			}
		}

		throw new NotImplementedException(
			"Not supported Operator: " + n.getOperator().getName() + "\n" + n.getLocation());
	}

	private TLAType evalBoundedVariables(OpApplNode n) throws TLA2BException {
		ArrayList<TLAType> domList = new ArrayList<>();
		FormalParamNode[][] params = n.getBdedQuantSymbolLists();
		ExprNode[] bounds = n.getBdedQuantBounds();
		for (int i = 0; i < bounds.length; i++) {
			SetType boundType = (SetType) visitExprNode(bounds[i], new SetType(new UntypedType()));
			TLAType subType = boundType.getSubType();

			if (n.isBdedQuantATuple()[i]) {
				if (params[i].length == 1) {
					FormalParamNode p = params[i][0];
					FunctionType expected = new FunctionType(IntType.getInstance(), new UntypedType());
					try {
						expected = (FunctionType) expected.unify(subType);
					} catch (UnificationException e) {
						throw new TypeErrorException(String.format("Expected %s, found %s at parameter %s,%n%s",
							expected, subType, p.getName().toString(), bounds[i].getLocation()));
					}
					domList.add(expected);
					symbolNodeList.add(p);
					p.setToolObject(TYPE_ID, expected.getRange());
					if (expected.getRange() instanceof AbstractHasFollowers) {
						((AbstractHasFollowers) expected.getRange()).addFollower(p);
					}
				} else {
					TupleType tuple = new TupleType(params[i].length);
					try {
						tuple = (TupleType) tuple.unify(subType);
					} catch (UnificationException e) {
						throw new TypeErrorException(String.format("Expected %s, found %s at tuple,%n%s", tuple,
							subType, bounds[i].getLocation()));
					}
					domList.add(tuple);
					for (int j = 0; j < params[i].length; j++) {
						FormalParamNode p = params[i][j];
						symbolNodeList.add(p);
						TLAType paramType = tuple.getTypes().get(j);
						p.setToolObject(TYPE_ID, paramType);
						if (paramType instanceof AbstractHasFollowers) {
							((AbstractHasFollowers) paramType).addFollower(p);
						}
					}

				}

			} else {
				// is not a tuple: all parameter have the same type
				for (int j = 0; j < params[i].length; j++) {
					domList.add(subType);
					FormalParamNode p = params[i][j];
					symbolNodeList.add(p);
					p.setToolObject(TYPE_ID, subType);
					if (subType instanceof AbstractHasFollowers) {
						((AbstractHasFollowers) subType).addFollower(p);
					}
				}
			}
		}

		TLAType domType;
		if (domList.size() == 1) {
			domType = domList.get(0);
		} else {
			domType = new TupleType(domList);
		}
		return domType;
	}

	private TLAType evalExcept(OpApplNode n, TLAType expected) throws TLA2BException {
		TLAType t = visitExprOrOpArgNode(n.getArgs()[0], expected);
		n.setToolObject(TYPE_ID, t);
		if (t instanceof AbstractHasFollowers) {
			((AbstractHasFollowers) t).addFollower(n);
		}

		for (int i = 1; i < n.getArgs().length; i++) {
			OpApplNode pair = (OpApplNode) n.getArgs()[i];
			ExprOrOpArgNode leftside = pair.getArgs()[0];
			ExprOrOpArgNode rightside = pair.getArgs()[1];
			// stored for @ node
			UntypedType untyped = new UntypedType();
			rightside.setToolObject(TYPE_ID, untyped);
			untyped.addFollower(rightside);
			TLAType valueType = visitExprOrOpArgNode(rightside, untyped);

			OpApplNode seq = (OpApplNode) leftside;
			LinkedList<ExprOrOpArgNode> list = new LinkedList<>();
			Collections.addAll(list, seq.getArgs());
			ExprOrOpArgNode first = list.poll();

			if (first instanceof StringNode) {
				String field = ((StringNode) first).getRep().toString();
				TLAType res = evalType(list, valueType);
				StructOrFunctionType s = new StructOrFunctionType(field, res);
				try {
					t = t.unify(s);
				} catch (UnificationException e) {
					throw new TypeErrorException(
						String.format("Expected %s, found %s at 'EXCEPT',%n%s", t, s, pair.getLocation()));
				}

			} else {
				// Function
				ExprOrOpArgNode domExpr = first;
				TLAType domType;
				TLAType rangeType;
				if (domExpr instanceof OpApplNode
					&& ((OpApplNode) domExpr).getOperator().getName().toString().equals("$Tuple")) {
					ArrayList<TLAType> domList = new ArrayList<>();
					OpApplNode domOpAppl = (OpApplNode) domExpr;
					for (int j = 0; j < domOpAppl.getArgs().length; j++) {
						TLAType d = visitExprOrOpArgNode(domOpAppl.getArgs()[j], new UntypedType());
						domList.add(d);
					}
					domType = new TupleType(domList);
					domExpr.setToolObject(TYPE_ID, domType); // store type
				} else {
					domType = visitExprOrOpArgNode(domExpr, new UntypedType());
				}
				rangeType = evalType(list, valueType);
				FunctionType func = new FunctionType(domType, rangeType);
				try {
					t = t.unify(func);
				} catch (UnificationException e) {
					throw new TypeErrorException(
						String.format("Expected %s, found %s at 'EXCEPT',%n%s", t, func, pair.getLocation()));
				}
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
			StructOrFunctionType res = new StructOrFunctionType(name, evalType(list, valueType));
			return res;
		}
		TLAType t = visitExprOrOpArgNode(head, new UntypedType());
		FunctionType res = new FunctionType(t, evalType(list, valueType));
		return res;
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
				try {
					for (ExprOrOpArgNode arg : n.getArgs()) {
						visitExprOrOpArgNode(arg, IntType.getInstance());
					}
				} catch (TypeErrorException e) {
					for (ExprOrOpArgNode arg : n.getArgs()) {
						visitExprOrOpArgNode(arg, RealType.getInstance());
					}
				}
				return boolType;
			}

			// arithmetic operators: support both integers and reals
			// for UntypedTypes the default is integer; if this leads to a TypeErrorException real is tried instead
			case B_OPCODE_plus: // +
			case B_OPCODE_minus: // -
			case B_OPCODE_times: // *
			case B_OPCODE_div: // /
			case B_OPCODE_mod: // % modulo
			case B_OPCODE_exp: { // x hoch y, x^y
				TLAType type;
				try {
					IntType.getInstance().unify(expected); // throws UnificationException
					type = IntType.getInstance();
					for (ExprOrOpArgNode arg : n.getArgs()) {
						// throws TypeErrorException; check whether IntType is OK, else try the same with RealType
						visitExprOrOpArgNode(arg, type);
					}
				} catch (UnificationException | TypeErrorException e) {
					type = unify(RealType.getInstance(), expected, n);
					for (ExprOrOpArgNode arg : n.getArgs()) {
						// if TypeErrorException is thrown here, the type is incompatible and it is a real type error!
						visitExprOrOpArgNode(arg, type);
					}
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

			case B_OPCODE_uminus: { // -x
				TLAType type;
				try {
					IntType.getInstance().unify(expected); // throws UnificationException
					type = IntType.getInstance();
					// throws TypeErrorException; check whether IntType is OK, else try the same with RealType
					visitExprOrOpArgNode(n.getArgs()[0], type);
				} catch (UnificationException | TypeErrorException e) {
					type = unify(RealType.getInstance(), expected, n);
					// if TypeErrorException is thrown here, the type is incompatible and it is a real type error!
					visitExprOrOpArgNode(n.getArgs()[0], type);
				}
				return type;
			}

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
	private static void setTypeAndFollowers(SemanticNode node, TLAType type, int paramId) {
		setType(node, type, paramId);
		if (type instanceof AbstractHasFollowers) {
			((AbstractHasFollowers) type).addFollower(node);
		}
	}

	private static void setTypeAndFollowers(SemanticNode node, TLAType type) {
		setTypeAndFollowers(node, type, TYPE_ID);
	}

	private static void setType(SemanticNode node, TLAType type, int paramId) {
		node.setToolObject(paramId, type);
	}

	public static void setType(SemanticNode node, TLAType type) {
		setType(node, type, TYPE_ID);
	}

	private static TLAType getType(SemanticNode n, int paramId) {
		return (TLAType) n.getToolObject(paramId);
	}

	public static TLAType getType(SemanticNode n) {
		return getType(n, TYPE_ID);
	}

	private TLAType unify(TLAType toUnify, TLAType expected, String opMsg, SemanticNode n) throws TypeErrorException {
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

	private TLAType unify(TLAType toUnify, TLAType expected, OpApplNode n) throws TypeErrorException {
		return unify(toUnify, expected, n.getOperator().getName().toString(), n);
	}

	private TLAType unifyAndSetTypeWithFollowers(TLAType toUnify, TLAType expected, String opMsg, SemanticNode n) throws TypeErrorException {
		TLAType found = unify(toUnify, expected, opMsg, n);
		setTypeAndFollowers(n, found);
		return found;
	}

	private TLAType unifyAndSetType(TLAType toUnify, TLAType expected, String opMsg, SemanticNode n) throws TypeErrorException {
		TLAType found = unify(toUnify, expected, opMsg, n);
		setType(n, found);
		return found;
	}
}
