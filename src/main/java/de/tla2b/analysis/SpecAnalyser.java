package de.tla2b.analysis;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.Hashtable;
import java.util.Set;

import de.tla2b.config.ConfigfileEvaluator;
import de.tla2b.exceptions.ConfigFileErrorException;
import de.tla2b.exceptions.FrontEndException;
import de.tla2b.exceptions.NotImplementedException;
import de.tla2b.exceptions.SemanticErrorException;
import de.tla2b.global.BBuiltInOPs;
import de.tla2b.global.TranslationGlobals;
import de.tla2b.translation.BDefinitionsFinder;
import de.tla2b.translation.OperationsFinder;
import de.tla2b.translation.UsedDefinitionsFinder;
import tla2sany.semantic.ASTConstants;
import tla2sany.semantic.ExprNode;
import tla2sany.semantic.ExprOrOpArgNode;
import tla2sany.semantic.FormalParamNode;
import tla2sany.semantic.ModuleNode;
import tla2sany.semantic.OpApplNode;
import tla2sany.semantic.OpDeclNode;
import tla2sany.semantic.OpDefNode;
import tla2sany.semantic.SemanticNode;
import tla2sany.semantic.SymbolNode;
import tlc2.tool.BuiltInOPs;
import tlc2.tool.ToolGlobals;

public class SpecAnalyser extends BuiltInOPs implements ASTConstants, ToolGlobals, TranslationGlobals {
	private OpDefNode spec;
	private OpDefNode init;
	private OpDefNode next;
	private ArrayList<OpDefNode> invariants = new ArrayList<>();

	private OpDefNode expressionOpdefNode;
	private Hashtable<String, SymbolNode> namingHashTable = new Hashtable<>();

	private final ModuleNode moduleNode;
	private ExprNode nextExpr;

	private ArrayList<OpDeclNode> bConstants;
	// used to check if a b constant has arguments and is not overriden in the
	// configfile

	private ArrayList<BOperation> bOperations = new ArrayList<BOperation>();
	private ArrayList<ExprNode> inits = new ArrayList<ExprNode>();

	private Set<OpDefNode> bDefinitionsSet = new HashSet<OpDefNode>();
	// set of OpDefNodes which will appear in the resulting B Machine
	private Set<OpDefNode> usedDefinitions = new HashSet<OpDefNode>();
	// definitions which are used for the type inference algorithm
	private Hashtable<OpDefNode, FormalParamNode[]> letParams = new Hashtable<>();
	// additional parameters of an let Operator, these parameters are from the
	// surrounding operator
	private ArrayList<String> definitionMacros = new ArrayList<>();

	private ArrayList<OpDefNode> recursiveFunctions = new ArrayList<>();

	private ArrayList<RecursiveDefinition> recursiveDefinitions = new ArrayList<>();

	private ConfigfileEvaluator configFileEvaluator;

	private SpecAnalyser(ModuleNode m) {
		this.moduleNode = m;
		this.bConstants = new ArrayList<OpDeclNode>();
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
		Hashtable<String, OpDefNode> definitions = new Hashtable<String, OpDefNode>();
		for (int i = 0; i < m.getOpDefs().length; i++) {
			definitions.put(m.getOpDefs()[i].getName().toString(), m.getOpDefs()[i]);
		}
		
		if (definitions.containsKey("Spec")) {
			specAnalyser.spec = definitions.get("Spec");
		} else if (definitions.containsKey("SPEC")) {
			specAnalyser.spec = definitions.get("SPEC");
		}
		
		if (definitions.containsKey("Init")) {
			specAnalyser.init = definitions.get("Init");
		} else if (definitions.containsKey("INIT")) {
			specAnalyser.init = definitions.get("INIT");
		} else if (definitions.containsKey("Initialisation")) {
			specAnalyser.init = definitions.get("Initialisation");
		}
		
		if (definitions.containsKey("Next")) {
			specAnalyser.next = definitions.get("Next");
		} else if (definitions.containsKey("NEXT")) {
			specAnalyser.next = definitions.get("NEXT");
		}
		
		if (definitions.containsKey("Inv")) {
			specAnalyser.invariants.add(definitions.get("Inv"));
		} else if (definitions.containsKey("INV")) {
			specAnalyser.invariants.add(definitions.get("INV"));
		} else if (definitions.containsKey("Invariant")) {
			specAnalyser.invariants.add(definitions.get("Invariant"));
		} else if (definitions.containsKey("Invariants")) {
			specAnalyser.invariants.add(definitions.get("Invariants"));
		}
		// TODO are constant in the right order

		specAnalyser.bConstants.addAll(Arrays.asList(m.getConstantDecls()));

		return specAnalyser;
	}

	public void start()
			throws SemanticErrorException, FrontEndException, ConfigFileErrorException, NotImplementedException {

		if (spec != null) {
			evalSpec();
		} else {
			evalInit();
			evalNext();
		}

		for (OpDefNode inv : new ArrayList<OpDefNode>(invariants)) {
			try {
				OpApplNode opApplNode = (OpApplNode) inv.getBody();

				OpDefNode opDefNode = (OpDefNode) opApplNode.getOperator();

				if (opDefNode.getKind() == UserDefinedOpKind && !BBuiltInOPs.contains(opDefNode.getName())) {
					int i = invariants.indexOf(inv);
					invariants.set(i, opDefNode);
				}
			} catch (ClassCastException e) {
			}
		}

		OperationsFinder operationsFinder = new OperationsFinder(this);
		bOperations = operationsFinder.getBOperations();

		UsedDefinitionsFinder definitionFinder = new UsedDefinitionsFinder(this);
		this.usedDefinitions = definitionFinder.getUsedDefinitions();

		BDefinitionsFinder bDefinitionFinder = new BDefinitionsFinder(this);
		this.bDefinitionsSet = bDefinitionFinder.getBDefinitionsSet();
		// usedDefinitions.addAll(bDefinitionsSet);

		// test whether there is a init predicate if there is a variable
		if (moduleNode.getVariableDecls().length > 0 && inits == null) {
			throw new SemanticErrorException("No initial predicate is defined.");
		}

		// check if there is B constant with arguments.
		for (int i = 0; i < bConstants.size(); i++) {
			OpDeclNode con = bConstants.get(i);
			if (con.getArity() > 0) {
				throw new ConfigFileErrorException(
						String.format("Constant '%s' must be overriden in the configuration file.", con.getName()));
			}
		}
		findRecursiveConstructs();

		for (OpDeclNode var : moduleNode.getVariableDecls()) {
			namingHashTable.put(var.getName().toString(), var);
		}
		for (OpDeclNode con : moduleNode.getConstantDecls()) {
			namingHashTable.put(con.getName().toString(), con);
		}
		for (OpDefNode def : usedDefinitions) {
			namingHashTable.put(def.getName().toString(), def);
		}

	}

	private void evalInit() {
		if (init != null) {
			inits.add(init.getBody());
		}
	}

	private void evalNext() throws FrontEndException {
		if (next != null) {
			this.nextExpr = next.getBody();
		}
	}

	public void evalSpec() throws SemanticErrorException, FrontEndException {
		if (spec != null) {
			processConfigSpec(spec.getBody());
		}

	}

	private void processConfigSpec(ExprNode exprNode) throws SemanticErrorException, FrontEndException {

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
				for (int i = 0; i < args.length; i++) {
					this.processConfigSpec((ExprNode) args[i]);
				}
				return;
			}

			if (opcode == OPCODE_box) {
				SemanticNode boxArg = args[0];
				if ((boxArg instanceof OpApplNode)
						&& BuiltInOPs.getOpCode(((OpApplNode) boxArg).getOperator().getName()) == OPCODE_sa) {
					ExprNode next = (ExprNode) ((OpApplNode) boxArg).getArgs()[0];
					this.nextExpr = next;
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
		Set<OpDefNode> set = new HashSet<OpDefNode>(usedDefinitions);
		for (OpDefNode def : set) {
			if (def.getInRecursive()) {
				throw new NotImplementedException("Recursive definitions are currently not supported: " + def.getName()
						+ "\n" + def.getLocation());
				// bDefinitionsSet.remove(def);
				// RecursiveDefinition rd = new RecursiveDefinition(def);
				// recursiveDefinitions.add(rd);
			} else if (def.getBody() instanceof OpApplNode) {
				OpApplNode o = (OpApplNode) def.getBody();
				switch (getOpCode(o.getOperator().getName())) {
				case OPCODE_rfs: { // recursive Function
					bDefinitionsSet.remove(def);
					recursiveFunctions.add(def);
				}
				}
			}
		}
	}

	public ArrayList<BOperation> getBOperations() {
		return this.bOperations;
	}

	public ArrayList<ExprNode> getInits() {
		return this.inits;
	}

	public ExprNode getNext() {
		return this.nextExpr;
	}

	public Set<OpDefNode> getBDefinitions() {
		return bDefinitionsSet;
	}

	public Hashtable<OpDefNode, FormalParamNode[]> getLetParams() {
		return new Hashtable<OpDefNode, FormalParamNode[]>(letParams);
	}

	public ArrayList<String> getDefinitionMacros() {
		return definitionMacros;
	}

	public Set<OpDefNode> getUsedDefinitions() {
		return usedDefinitions;
	}

	public ArrayList<OpDefNode> getRecursiveFunctions() {
		return recursiveFunctions;
	}

	public ArrayList<RecursiveDefinition> getRecursiveDefinitions() {
		return recursiveDefinitions;
	}

	public ModuleNode getModuleNode() {
		return this.moduleNode;
	}

	public ConfigfileEvaluator getConfigFileEvaluator() {
		return configFileEvaluator;
	}

	public ArrayList<OpDefNode> getInvariants() {
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
