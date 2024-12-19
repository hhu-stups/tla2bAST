package de.tla2b.analysis;

import de.tla2b.config.ConfigfileEvaluator;
import de.tla2b.exceptions.ConfigFileErrorException;
import de.tla2b.exceptions.TLA2BFrontEndException;
import de.tla2b.exceptions.NotImplementedException;
import de.tla2b.exceptions.SemanticErrorException;
import de.tla2b.global.BBuiltInOPs;
import de.tla2b.global.TranslationGlobals;
import de.tla2b.translation.BDefinitionsFinder;
import de.tla2b.translation.OperationsFinder;
import de.tla2b.translation.UsedDefinitionsFinder;
import de.tla2b.util.DebugUtils;
import tla2sany.semantic.*;
import tlc2.tool.BuiltInOPs;
import tlc2.tool.ToolGlobals;

import java.util.*;

public class SpecAnalyser extends BuiltInOPs implements ASTConstants, ToolGlobals, TranslationGlobals {
	private OpDefNode spec;
	private OpDefNode init;
	private OpDefNode next;
	private List<OpDefNode> invariants = new ArrayList<>();

	private OpDefNode expressionOpdefNode;
	private final Hashtable<String, SymbolNode> namingHashTable = new Hashtable<>();

	private final ModuleNode moduleNode;
	private ExprNode nextExpr;

	private List<OpDeclNode> bConstants;
	// used to check if a b constant has arguments and is not overridden in the
	// configfile

	private List<BOperation> bOperations = new ArrayList<>();
	private final List<ExprNode> inits = new ArrayList<>();

	private Set<OpDefNode> bDefinitionsSet = new HashSet<>();
	// set of OpDefNodes which will appear in the resulting B Machine
	private Set<OpDefNode> usedDefinitions = new HashSet<>();
	// definitions which are used for the type inference algorithm
	private final Hashtable<OpDefNode, FormalParamNode[]> letParams = new Hashtable<>();
	// additional parameters of a let Operator, these parameters are from the
	// surrounding operator
	private final List<String> definitionMacros = new ArrayList<>();

	private final List<OpDefNode> recursiveFunctions = new ArrayList<>();

	private final List<RecursiveDefinition> recursiveDefinitions = new ArrayList<>();

	private ConfigfileEvaluator configFileEvaluator;

	private SpecAnalyser(ModuleNode m) {
		this.moduleNode = m;
		this.bConstants = new ArrayList<>();
	}

	public static SpecAnalyser createSpecAnalyser(ModuleNode m, ConfigfileEvaluator conEval) {
		SpecAnalyser specAnalyser = new SpecAnalyser(m);
		specAnalyser.spec = conEval.getSpecNode();
		specAnalyser.init = conEval.getInitNode();
		specAnalyser.next = conEval.getNextNode();
		specAnalyser.invariants = conEval.getInvariants();
		specAnalyser.bConstants = conEval.getbConstantList();
		specAnalyser.configFileEvaluator = conEval;

		return specAnalyser;
	}

	public static SpecAnalyser createSpecAnalyserForTlaExpression(ModuleNode m) {
		SpecAnalyser specAnalyser = new SpecAnalyser(m);

		specAnalyser.expressionOpdefNode = m.getOpDefs()[m.getOpDefs().length - 1];
		specAnalyser.usedDefinitions.add(specAnalyser.expressionOpdefNode);
		specAnalyser.bDefinitionsSet.add(specAnalyser.expressionOpdefNode);
		return specAnalyser;
	}

	public static SpecAnalyser createSpecAnalyser(ModuleNode m) {
		SpecAnalyser specAnalyser = new SpecAnalyser(m);
		Hashtable<String, OpDefNode> definitions = new Hashtable<>();
		for (int i = 0; i < m.getOpDefs().length; i++) {
			definitions.put(m.getOpDefs()[i].getName().toString(), m.getOpDefs()[i]);
		}

		if (definitions.containsKey("Spec")) {
			specAnalyser.spec = definitions.get("Spec");
			ClausefDetected("Spec", "INITIALISATION+OPERATIONS");
		} else if (definitions.containsKey("SPECIFICATION")) {
			specAnalyser.spec = definitions.get("SPECIFICATION");
			ClausefDetected("SPECIFICATION", "INITIALISATION+OPERATIONS");
		} else if (definitions.containsKey("SPEC")) {
			specAnalyser.spec = definitions.get("SPEC");
			ClausefDetected("SPEC", "INITIALISATION+OPERATIONS");
		}

		if (definitions.containsKey("Init")) {
			specAnalyser.init = definitions.get("Init");
			ClausefDetected("Init", "INITIALISATION");
		} else if (definitions.containsKey("INIT")) {
			specAnalyser.init = definitions.get("INIT");
			ClausefDetected("INIT", "INITIALISATION");
		} else if (definitions.containsKey("Initialisation")) {
			specAnalyser.init = definitions.get("Initialisation");
			ClausefDetected("Initialisation", "INITIALISATION");
		} else if (definitions.containsKey("INITIALISATION")) {
			specAnalyser.init = definitions.get("INITIALISATION");
			ClausefDetected("INITIALISATION", "INITIALISATION");
		}

		if (definitions.containsKey("Next")) {
			specAnalyser.next = definitions.get("Next");
			ClausefDetected("Next", "OPERATIONS");
		} else if (definitions.containsKey("NEXT")) {
			specAnalyser.next = definitions.get("NEXT");
			ClausefDetected("NEXT", "OPERATIONS");
		}

		if (definitions.containsKey("Inv")) {
			specAnalyser.invariants.add(definitions.get("Inv"));
			ClausefDetected("Inv", "INVARIANTS");
		} else if (definitions.containsKey("INVARIANTS")) {
			specAnalyser.invariants.add(definitions.get("INVARIANTS"));
			ClausefDetected("INVARIANTS", "INVARIANTS");
		} else if (definitions.containsKey("INVARIANT")) {
			specAnalyser.invariants.add(definitions.get("INVARIANT"));
			ClausefDetected("INVARIANT", "INVARIANTS");
		} else if (definitions.containsKey("INV")) {
			specAnalyser.invariants.add(definitions.get("INV"));
			ClausefDetected("INV", "INVARIANTS");
		} else if (definitions.containsKey("Invariant")) {
			specAnalyser.invariants.add(definitions.get("Invariant"));
			ClausefDetected("Invariant", "INVARIANTS");
		} else if (definitions.containsKey("Invariants")) {
			specAnalyser.invariants.add(definitions.get("Invariants"));
			ClausefDetected("Invariants", "INVARIANTS");
		} else if (definitions.containsKey("TypeInv")) {
			specAnalyser.invariants.add(definitions.get("TypeInv"));
			ClausefDetected("TypeInv", "INVARIANTS");
		} else if (definitions.containsKey("TypeOK")) {
			specAnalyser.invariants.add(definitions.get("TypeOK"));
			ClausefDetected("TypeOK", "INVARIANTS");
		} else if (definitions.containsKey("IndInv")) {
			specAnalyser.invariants.add(definitions.get("IndInv"));
			ClausefDetected("IndInv", "INVARIANTS");
		} else {
			System.out.println("No default Invariant detected");
		}
		// TODO are constant in the right order

		specAnalyser.bConstants.addAll(Arrays.asList(m.getConstantDecls()));

		return specAnalyser;
	}

	public static void ClausefDetected(String Name, String Clause) {
		DebugUtils.printMsg("Detected TLA+ Default Definition " + Name + " for Clause: " + Clause);
	}

	public void start()
		throws SemanticErrorException, TLA2BFrontEndException, ConfigFileErrorException, NotImplementedException {

		if (spec != null) {
			evalSpec();
		} else {
			evalInit();
			evalNext();
		}

		for (OpDefNode inv : new ArrayList<>(invariants)) {
			try {
				OpApplNode opApplNode = (OpApplNode) inv.getBody();

				OpDefNode opDefNode = (OpDefNode) opApplNode.getOperator();

				if (opDefNode.getKind() == UserDefinedOpKind && !BBuiltInOPs.contains(opDefNode.getName())) {
					int i = invariants.indexOf(inv);
					invariants.set(i, opDefNode);
					DebugUtils.printDebugMsg("Adding invariant " + i);
				}
			} catch (ClassCastException e) {
			}
		}

		DebugUtils.printDebugMsg("Detecting OPERATIONS from disjunctions");
		bOperations = new OperationsFinder(this).getBOperations();

		DebugUtils.printDebugMsg("Finding used definitions");
		UsedDefinitionsFinder definitionFinder = new UsedDefinitionsFinder(this);
		this.usedDefinitions = definitionFinder.getUsedDefinitions();

		BDefinitionsFinder bDefinitionFinder = new BDefinitionsFinder(this);
		this.bDefinitionsSet = bDefinitionFinder.getBDefinitionsSet();
		// usedDefinitions.addAll(bDefinitionsSet);

		DebugUtils.printDebugMsg("Computing variable declarations");
		// test whether there is an init predicate if there is a variable
		if (moduleNode.getVariableDecls().length > 0 && inits == null) {
			throw new SemanticErrorException("No initial predicate is defined.");
		}

		// check if there is B constant with arguments.
		for (OpDeclNode con : bConstants) {
			if (con.getArity() > 0) {
				throw new ConfigFileErrorException(
					String.format("Constant '%s' must be overridden in the configuration file.", con.getName()));
			}
		}
		findRecursiveConstructs();

		for (OpDeclNode var : moduleNode.getVariableDecls()) {
			namingHashTable.put(var.getName().toString(), var);
		}
		DebugUtils.printMsg("Number of variables detected: " + moduleNode.getVariableDecls().length);
		for (OpDeclNode con : moduleNode.getConstantDecls()) {
			namingHashTable.put(con.getName().toString(), con);
		}
		DebugUtils.printMsg("Number of constants detected: " + moduleNode.getConstantDecls().length);
		for (OpDefNode def : usedDefinitions) {
			namingHashTable.put(def.getName().toString(), def);
		}

	}

	private void evalInit() {
		if (init != null) {
			DebugUtils.printMsg("Using TLA+ Init definition to determine B INITIALISATION");
			inits.add(init.getBody());
		}
	}

	private void evalNext() {
		if (next != null) {
			DebugUtils.printMsg("Using TLA+ Next definition to determine B OPERATIONS");
			this.nextExpr = next.getBody();
		}
	}

	public void evalSpec() throws SemanticErrorException {
		if (spec != null) {
			DebugUtils.printMsg("Using TLA+ Spec to determine B INITIALISATION and OPERATIONS");
			processConfigSpec(spec.getBody());
		}

	}

	private void processConfigSpec(ExprNode exprNode) throws SemanticErrorException {
		if (exprNode instanceof OpApplNode) {
			OpApplNode opApp = (OpApplNode) exprNode;
			ExprOrOpArgNode[] args = opApp.getArgs();
			if (args.length == 0) {
				SymbolNode opNode = opApp.getOperator();
				if (opNode instanceof OpDefNode) {
					OpDefNode def = (OpDefNode) opNode;
					ExprNode body = def.getBody();
					body.levelCheck(1);
					if (body.getLevel() == 1) {
						inits.add(exprNode);
					} else {
						processConfigSpec(body);
					}
					return;
				}
				throw new SemanticErrorException("Can not handle specification conjunction.");
			}

			int opcode = BuiltInOPs.getOpCode(opApp.getOperator().getName());
			if (opcode == OPCODE_cl || opcode == OPCODE_land) {
				for (ExprOrOpArgNode arg : args) {
					this.processConfigSpec((ExprNode) arg);
				}
				return;
			}

			if (opcode == OPCODE_box) {
				SemanticNode boxArg = args[0];
				if ((boxArg instanceof OpApplNode)
					&& BuiltInOPs.getOpCode(((OpApplNode) boxArg).getOperator().getName()) == OPCODE_sa) {
					this.nextExpr = (ExprNode) ((OpApplNode) boxArg).getArgs()[0];
					return;
				}
			}
		}
		if (exprNode.getLevel() <= 1) {
			// init
			inits.add(exprNode);
		} else if (exprNode.getLevel() == 3) {
			// temporal

		} else {
			throw new SemanticErrorException("Can not handle specification conjunction.");
		}

	}

	private void findRecursiveConstructs() throws NotImplementedException {
		Set<OpDefNode> set = new HashSet<>(usedDefinitions);
		for (OpDefNode def : set) {
			if (def.getInRecursive()) {
				throw new NotImplementedException("Recursive definitions are currently not supported: " + def.getName()
					+ "\n" + def.getLocation());
				// bDefinitionsSet.remove(def);
				// RecursiveDefinition rd = new RecursiveDefinition(def);
				// recursiveDefinitions.add(rd);
			} else if (def.getBody() instanceof OpApplNode) {
				OpApplNode o = (OpApplNode) def.getBody();
				if (getOpCode(o.getOperator().getName()) == OPCODE_rfs) {// recursive Function
					bDefinitionsSet.remove(def);
					recursiveFunctions.add(def);
				}
			}
		}
	}

	public List<BOperation> getBOperations() {
		return this.bOperations;
	}

	public List<ExprNode> getInits() {
		return this.inits;
	}

	public ExprNode getNext() {
		return this.nextExpr;
	}

	public Set<OpDefNode> getBDefinitions() {
		return bDefinitionsSet;
	}

	public Hashtable<OpDefNode, FormalParamNode[]> getLetParams() {
		return new Hashtable<>(letParams);
	}

	public List<String> getDefinitionMacros() {
		return definitionMacros;
	}

	public Set<OpDefNode> getUsedDefinitions() {
		return usedDefinitions;
	}

	public List<OpDefNode> getRecursiveFunctions() {
		return recursiveFunctions;
	}

	public List<RecursiveDefinition> getRecursiveDefinitions() {
		return recursiveDefinitions;
	}

	public ModuleNode getModuleNode() {
		return this.moduleNode;
	}

	public ConfigfileEvaluator getConfigFileEvaluator() {
		return configFileEvaluator;
	}

	public List<OpDefNode> getInvariants() {
		return invariants;
	}

	public OpDefNode getInitDef() {
		return init;
	}

	public OpDefNode getExpressionOpdefNode() {
		return expressionOpdefNode;
	}

	public SymbolNode getSymbolNodeByName(String name) {
		return namingHashTable.get(name);
	}

}
