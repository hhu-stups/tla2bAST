package de.tla2b.analysis;

import de.tla2b.global.BBuiltInOPs;
import de.tla2b.global.TranslationGlobals;
import tla2sany.semantic.*;
import tlc2.tool.BuiltInOPs;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

public class SymbolRenamer extends BuiltInOPs implements TranslationGlobals {

	private final static Set<String> KEYWORDS = new HashSet<>();

	static {
		KEYWORDS.add("seq");
		KEYWORDS.add("left");
		KEYWORDS.add("right");
		KEYWORDS.add("max");
		KEYWORDS.add("min");
		KEYWORDS.add("succ");
		KEYWORDS.add("pred");
		KEYWORDS.add("dom");
		KEYWORDS.add("ran");
		KEYWORDS.add("fnc");
		KEYWORDS.add("rel");
		KEYWORDS.add("id");
		KEYWORDS.add("card");
		KEYWORDS.add("POW");
		KEYWORDS.add("POW1");
		KEYWORDS.add("FIN");
		KEYWORDS.add("FIN1");
		KEYWORDS.add("size");
		KEYWORDS.add("rev");
		KEYWORDS.add("first");
		KEYWORDS.add("last");
		KEYWORDS.add("front");
		KEYWORDS.add("tail");
		KEYWORDS.add("conc");
		KEYWORDS.add("struct");
		KEYWORDS.add("rec");
		KEYWORDS.add("tree");
		KEYWORDS.add("btree");
		KEYWORDS.add("skip");
		KEYWORDS.add("ANY");
		KEYWORDS.add("WHERE");
		KEYWORDS.add("END");
		KEYWORDS.add("BE");
		KEYWORDS.add("VAR");
		KEYWORDS.add("ASSERT");
		KEYWORDS.add("CHOICE");
		KEYWORDS.add("OR");
		KEYWORDS.add("SELECT");
		KEYWORDS.add("EITHER");
		KEYWORDS.add("WHEN");
		KEYWORDS.add("BEGIN");
		KEYWORDS.add("MACHINE");
		KEYWORDS.add("REFINEMENT");
		KEYWORDS.add("IMPLEMENTATION");
		KEYWORDS.add("SETS");
		KEYWORDS.add("CONSTRAINTS");
		KEYWORDS.add("MODEL");
		KEYWORDS.add("SYSTEM");
		KEYWORDS.add("EVENTS");
		KEYWORDS.add("OPERATIONS");
	}

	private final static Map<String, String> INFIX_OPERATOR = new HashMap<>();

	static {
		INFIX_OPERATOR.put("!!", "exclamationmark2");
		INFIX_OPERATOR.put("??", "questionmark2");
		INFIX_OPERATOR.put("&", "ampersand1");
		INFIX_OPERATOR.put("&&", "ampersand2");
		INFIX_OPERATOR.put("@@", "at2");
		INFIX_OPERATOR.put("++", "plus2");
		INFIX_OPERATOR.put("--", "minus2");
		INFIX_OPERATOR.put("^", "circumflex1");
		INFIX_OPERATOR.put("^^", "circumflex2");
		INFIX_OPERATOR.put("##", "hash2");
		INFIX_OPERATOR.put("%%", "percent2");
		INFIX_OPERATOR.put("$", "dollar1");
		INFIX_OPERATOR.put("$$", "dollar2");
		INFIX_OPERATOR.put("|", "pipe1");
		INFIX_OPERATOR.put("||", "pipe2");
		INFIX_OPERATOR.put("//", "slash2");
		INFIX_OPERATOR.put("**", "mult2");
		INFIX_OPERATOR.put("...", "dot3");
	}

	private final static Map<String, String> BBUILTIN_OPERATOR = new HashMap<>();

	static {
		BBUILTIN_OPERATOR.put("+", "plus");
		BBUILTIN_OPERATOR.put("-", "minus");
		BBUILTIN_OPERATOR.put("*", "mult");
		BBUILTIN_OPERATOR.put("^", "power");
		BBUILTIN_OPERATOR.put("<", "lt");
		BBUILTIN_OPERATOR.put(">", "gt");
		BBUILTIN_OPERATOR.put("\\leq", "leq");
		BBUILTIN_OPERATOR.put("\\geq", "geq");
		BBUILTIN_OPERATOR.put("%", "modulo");
		BBUILTIN_OPERATOR.put("\\div", "div");
		BBUILTIN_OPERATOR.put("/", "realdiv");
		BBUILTIN_OPERATOR.put("..", "dot2");
	}

	private final ModuleNode moduleNode;
	private final Set<OpDefNode> usedDefinitions;

	private final Set<String> globalNames = new HashSet<>();
	private final Map<OpDefNode, Set<String>> usedNamesTable = new HashMap<>();

	private SymbolRenamer(ModuleNode moduleNode, SpecAnalyser specAnalyser) {
		this.moduleNode = moduleNode;
		this.usedDefinitions = specAnalyser.getUsedDefinitions();
	}

	private SymbolRenamer(ModuleNode moduleNode) {
		this.moduleNode = moduleNode;
		this.usedDefinitions = new HashSet<>();
		OpDefNode[] defs = moduleNode.getOpDefs();
		this.usedDefinitions.add(defs[defs.length - 1]);
	}

	public static void run(ModuleNode moduleNode, SpecAnalyser specAnalyser) {
		new SymbolRenamer(moduleNode, specAnalyser).start();
	}

	public static void run(ModuleNode moduleNode) {
		new SymbolRenamer(moduleNode).start();
	}

	private void start() {
		// Variables
		for (OpDeclNode node : moduleNode.getVariableDecls()) {
			String newName = incName(node.getName().toString());
			globalNames.add(newName);
			node.setToolObject(NEW_NAME, newName);
		}

		// constants
		for(OpDeclNode node : moduleNode.getConstantDecls()) {
			String newName = incName(node.getName().toString());
			globalNames.add(newName);
			node.setToolObject(NEW_NAME, newName);
		}

		for(OpDefNode node : moduleNode.getOpDefs()) {
			String newName = getOperatorName(node);
			globalNames.add(newName);
			node.setToolObject(NEW_NAME, newName);
			usedNamesTable.put(node, new HashSet<>());
		}

		for(AssumeNode node : moduleNode.getAssumptions()) {
			visitNode(node.getAssume(), new HashSet<>());
		}

		for (int i = moduleNode.getOpDefs().length - 1; i >= 0; i--) {
			OpDefNode def = moduleNode.getOpDefs()[i];
			Set<String> usedNames = usedNamesTable.get(def);
			for (FormalParamNode node : def.getParams()) {
				node.setToolObject(NEW_NAME, incName(node.getName().toString()));
				//Parameter of different definitions calling each other can have the same name
				//usedNames.add(newParamName);
			}
			visitNode(def.getBody(), usedNames);
		}

	}

	private void visitNode(SemanticNode n, Set<String> usedNames) {
		// System.out.println(n.toString(1)+ " "+ n.getKind());

		switch (n.getKind()) {
			case LetInKind: {
				LetInNode letInNode = (LetInNode) n;
				OpDefNode[] defs = letInNode.getLets();

				// Initialize all local definitions (get a new name, get an empty list)
				for (OpDefNode def : defs) {
					String newName = getOperatorName(def);
					globalNames.add(newName);
					def.setToolObject(NEW_NAME, newName);
					usedNamesTable.put(def, new HashSet<>(usedNames));
				}

				// first visit the IN expression
				visitNode(letInNode.getBody(), usedNames);

				// visit the definition itself
				for (int i = defs.length - 1; i >= 0; i--) {
					OpDefNode def = defs[i];
					Set<String> usedNamesOfDef = usedNamesTable.get(def);
					for (FormalParamNode node : def.getParams()) {
						node.setToolObject(NEW_NAME, incName(node.getName().toString()));
						//usedNamesOfDef.add(newParamName);
					}
					visitNode(def.getBody(), usedNamesOfDef);
				}
				return;
			}

			case OpApplKind: {
				OpApplNode opApplNode = (OpApplNode) n;
				switch (opApplNode.getOperator().getKind()) {
					case BuiltInKind: {
						visitBuiltinNode(opApplNode, usedNames);
						return;
					}

					case UserDefinedOpKind: {
						OpDefNode def = (OpDefNode) opApplNode.getOperator();
						if (BBuiltInOPs.contains(def.getName())) {
							break;
						}
						Set<String> set = usedNamesTable.get(def);
						if (set != null) {
							usedNamesTable.get(def).addAll(usedNames);
						}

						for (SemanticNode node : n.getChildren()) {
							visitNode(node, usedNames);
						}
						return;
					}
				}

				for (ExprOrOpArgNode node : opApplNode.getArgs()) {
					visitNode(node, usedNames);
				}
				return;
			}
		}

		if (n.getChildren() != null) {
			for (SemanticNode node : n.getChildren()) {
				visitNode(node, usedNames);
			}
		}
	}

	private void visitBuiltinNode(OpApplNode opApplNode, Set<String> usedNames) {

		switch (getOpCode(opApplNode.getOperator().getName())) {

			case OPCODE_nrfs:
			case OPCODE_fc: // Represents [x \in S |-> e]
			case OPCODE_bc: // CHOOSE x \in S: P
			case OPCODE_soa: // $SetOfAll Represents {e : p1 \in S, p2,p3 \in S2}
			case OPCODE_sso: // $SubsetOf Represents {x \in S : P}
			case OPCODE_bf: // \A x \in S : P
			case OPCODE_be: // \E x \in S : P
			{
				FormalParamNode[][] params = opApplNode.getBdedQuantSymbolLists();
				Set<String> newUsedNames = new HashSet<>(usedNames);
				for (FormalParamNode[] formalParamNodes : params) {
					for (FormalParamNode param : formalParamNodes) {
						String newName = incName(param.getName().toString(), usedNames);
						param.setToolObject(NEW_NAME, newName);
						newUsedNames.add(newName);
					}
				}
				for (ExprNode node : opApplNode.getBdedQuantBounds()) {
					visitNode(node, usedNames);
				}

				visitNode(opApplNode.getArgs()[0], newUsedNames);
				return;
			}

			default:
				for (ExprOrOpArgNode node : opApplNode.getArgs()) {
					if (node != null) {
						visitNode(node, usedNames);
					}
				}
		}
	}

	private String getOperatorName(OpDefNode def) {
		String newName = def.getName().toString();

		if (BBUILTIN_OPERATOR.containsKey(newName)) {
			// a B built-in operator is defined outside a standard module
			if (!STANDARD_MODULES.contains(def.getSource().getOriginallyDefinedInModuleNode().getName().toString())) {
				return incName(BBUILTIN_OPERATOR.get(newName));
			}
		}

		// replace invalid infix operator names
		for (String e : INFIX_OPERATOR.keySet()) {
			if (newName.contains(e)) {
				newName = newName.replace(e, INFIX_OPERATOR.get(e));
			}
		}

		// replace exclamation marks
		if (newName.contains("!")) {
			newName = newName.replace('!', '_');
		}

		// replace slashes
		if (newName.contains("\\")) {
			newName = newName.replace("\\", "");
		}

		return incName(newName);
	}

	private Boolean existingName(String name) {
		return globalNames.contains(name) || KEYWORDS.contains(name);
	}

	private String incName(String name) {
		String res = name;
		for (int i = 1; existingName(res); i++) {
			res = name + "_" + i;
		}
		return res;
	}

	private String incName(String name, Set<String> tempSet) {
		String res = name;
		for (int i = 1; existingName(res) || tempSet.contains(res); i++) {
			res = name + "_" + i;
		}
		return res;
	}
}
