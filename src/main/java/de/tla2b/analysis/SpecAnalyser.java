package de.tla2b.analysis;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Stream;

import de.tla2b.config.ConfigfileEvaluator;
import de.tla2b.exceptions.ConfigFileErrorException;
import de.tla2b.exceptions.NotImplementedException;
import de.tla2b.exceptions.SemanticErrorException;
import de.tla2b.global.BBuiltInOPs;
import de.tla2b.translation.BDefinitionsFinder;
import de.tla2b.translation.OperationsFinder;
import de.tla2b.translation.UsedDefinitionsFinder;
import de.tla2b.util.DebugUtils;
import de.tla2b.util.TlaUtils;

import tla2sany.semantic.*;

import tlc2.tool.BuiltInOPs;

public class SpecAnalyser extends BuiltInOPs {
	private OpDefNode spec;
	private OpDefNode init;
	private OpDefNode next;
	private List<OpDefNode> invariants = new ArrayList<>();
	private List<OpDeclNode> bConstants = new ArrayList<>();
	// used to check if a b constant has arguments and is not overridden in the configfile

	private OpDefNode expressionOpdefNode;
	private final Map<String, SymbolNode> namingMap = new HashMap<>();

	private final ModuleNode moduleNode;
	private ExprNode nextExpr;

	private List<BOperation> bOperations = new ArrayList<>();
	private final List<ExprNode> inits = new ArrayList<>();

	private Set<OpDefNode> bDefinitionsSet = new HashSet<>();
	// set of OpDefNodes which will appear in the resulting B Machine
	private Set<OpDefNode> usedDefinitions = new HashSet<>();
	// definitions which are used for the type inference algorithm
	private final Map<OpDefNode, FormalParamNode[]> letParams = new HashMap<>();
	// additional parameters of a let Operator, these parameters are from the surrounding operator
	private final List<String> definitionMacros = new ArrayList<>();

	private final List<OpDefNode> recursiveFunctions = new ArrayList<>();
	private final List<RecursiveDefinition> recursiveDefinitions = new ArrayList<>();

	private ConfigfileEvaluator configFileEvaluator;

	private SpecAnalyser(ModuleNode m) {
		this.moduleNode = m;
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
		Map<String, OpDefNode> definitions = TlaUtils.getOpDefsMap(m.getOpDefs());
		SpecAnalyser specAnalyser = new SpecAnalyser(m);

		specAnalyser.spec = detectClause(Stream.of("Spec", "SPECIFICATION", "SPEC"),
				definitions, "INITIALISATION+OPERATIONS");
		specAnalyser.init = detectClause(Stream.of("Init", "INIT", "Initialisation", "INITIALISATION"),
				definitions, "INITIALISATION");
		specAnalyser.next = detectClause(Stream.of("Next", "NEXT"), definitions, "OPERATIONS");
		OpDefNode invariant = detectClause(Stream.of("Inv", "INVARIANTS", "INVARIANT", "INV", "Invariant",
						"Invariants", "TypeInv", "TypeOK", "IndInv"),
				definitions, "INVARIANTS");

		if (invariant != null) {
			specAnalyser.invariants.add(invariant);
		} else {
			DebugUtils.printMsg("No default Invariant detected");
		}

		// TODO are constant in the right order
		specAnalyser.bConstants = Arrays.asList(m.getConstantDecls());
		return specAnalyser;
	}

	private static OpDefNode detectClause(Stream<String> keywords, Map<String, OpDefNode> definitions, String bClause) {
		return keywords.filter(definitions::containsKey)
				.findFirst()
				.map(keyword -> {
					DebugUtils.printMsg("Detected TLA+ Default Definition " + keyword + " for Clause: " + bClause);
					return definitions.get(keyword);
				})
				.orElse(null);
	}

	public void start() throws SemanticErrorException, ConfigFileErrorException, NotImplementedException {
		evalSpec();

		invariants.replaceAll(inv -> {
			try {
				// resolve nested definitions in invariants, e.g. Inv == Inv2
				// only Inv2 will appear in the translated B machine
				// not simplified if the topmost operator of the definition is a built-in operator
				OpApplNode opApplNode = (OpApplNode) inv.getBody();
				OpDefNode opDefNode = (OpDefNode) opApplNode.getOperator(); // nested definition

				if (opDefNode.getKind() == UserDefinedOpKind && !BBuiltInOPs.contains(opDefNode.getName())) {
					DebugUtils.printDebugMsg("replacing invariant definition " + inv.getName() + " by its inner definition " + opDefNode.getName());
					return opDefNode;
				}
			} catch (ClassCastException ignored) {
				// should not happen; otherwise no problem: invariant is already registered
			}
			return inv;
		});

		DebugUtils.printDebugMsg("Detecting OPERATIONS from disjunctions");
		bOperations = new OperationsFinder(this).getBOperations();

		DebugUtils.printDebugMsg("Finding used definitions");
		this.usedDefinitions = new UsedDefinitionsFinder(this).getUsedDefinitions();
		this.bDefinitionsSet = new BDefinitionsFinder(this).getBDefinitionsSet();
		// usedDefinitions.addAll(bDefinitionsSet);

		DebugUtils.printDebugMsg("Computing variable declarations");
		// test whether there is an init predicate if there is a variable
		if (moduleNode.getVariableDecls().length > 0 && inits.isEmpty()) {
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

		namingMap.putAll(TlaUtils.getDeclarationsMap(moduleNode.getVariableDecls()));
		DebugUtils.printMsg("Number of variables detected: " + moduleNode.getVariableDecls().length);

		namingMap.putAll(TlaUtils.getDeclarationsMap(moduleNode.getConstantDecls()));
		DebugUtils.printMsg("Number of constants detected: " + moduleNode.getConstantDecls().length);

		namingMap.putAll(TlaUtils.getOpDefsMap(usedDefinitions.toArray(new OpDefNode[0])));
	}

	private void evalSpec() throws SemanticErrorException {
		if (spec != null) {
			DebugUtils.printMsg("Using TLA+ Spec to determine B INITIALISATION and OPERATIONS");
			processConfigSpec(spec.getBody());
		} else {
			if (init != null) {
				DebugUtils.printMsg("Using TLA+ Init definition to determine B INITIALISATION");
				inits.add(init.getBody());
			}
			if (next != null) {
				DebugUtils.printMsg("Using TLA+ Next definition to determine B OPERATIONS");
				nextExpr = next.getBody();
			}
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
				// TODO: implement
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

	public Map<OpDefNode, FormalParamNode[]> getLetParams() {
		return new HashMap<>(letParams);
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
		return namingMap.get(name);
	}

}
