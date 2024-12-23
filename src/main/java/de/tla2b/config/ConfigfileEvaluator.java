package de.tla2b.config;

import de.tla2b.exceptions.ConfigFileErrorException;
import de.tla2b.exceptions.UnificationException;
import de.tla2b.types.*;
import de.tla2b.util.TlaUtils;
import de.tla2b.util.DebugUtils;
import tla2sany.semantic.*;
import tlc2.tool.impl.ModelConfig;
import tlc2.util.Vect;
import tlc2.value.impl.IntValue;
import tlc2.value.impl.ModelValue;
import tlc2.value.impl.SetEnumValue;
import tlc2.value.impl.Value;

import java.util.*;

/**
 * This class evaluates the configfile and collects all necessary information of
 * the configfile. All used identifier in the configfile are checked to be valid
 * in the context of the module
 */
public class ConfigfileEvaluator {

	private final ModelConfig configAst;
	private final ModuleNode moduleNode;
	private final Map<String, OpDefNode> definitions; // map of all definitions in module
	private final Map<String, OpDeclNode> constants; // map of all constants in the module

	private final OpDefNode specNode; // SPECIFICATION node, may be null
	private final OpDefNode nextNode; // NEXT node, may be null
	private final OpDefNode initNode; // INIT node, may be null
	private final List<OpDefNode> invariantNodeList = new ArrayList<>();
	private final List<String> enumeratedSet = new ArrayList<>();
	private final Map<String, EnumType> enumeratedTypes = new LinkedHashMap<>();
	private final Map<OpDeclNode, ValueObj> constantAssignments = new HashMap<>();
	// k = 1, the ValueObj describes the right side of the assignment and contains its type
	private final Map<OpDefNode, ValueObj> operatorAssignments = new HashMap<>(); // def = 1

	private final List<OpDefNode> operatorModelvalues = new ArrayList<>();

	private final List<OpDeclNode> bConstantList = new ArrayList<>();
	// List of constants in the resulting B machine. This list does not contain
	// a TLA+ constant if the constant is substituted by a modelvalue with the
	// same name (the constant name is moved to an enumerated set) or if the
	// constants has arguments and is overridden by an operator
	private final Map<OpDefNode, OpDefNode> operatorOverrides = new HashMap<>();
	// This map contains mappings for operators which are overridden in the
	// configuration file
	private final Map<OpDeclNode, OpDefNode> constantOverrides = new HashMap<>();
	// This map contains mappings for constants which are overridden in the
	// configuration file. All constants with arguments have to be overridden in
	// the configuration file.

	public ConfigfileEvaluator(ModelConfig configAst, ModuleNode moduleNode) throws ConfigFileErrorException {
		this.configAst = configAst;
		this.moduleNode = moduleNode;
		this.definitions = TlaUtils.getOpDefsMap(moduleNode.getOpDefs());
		this.constants = TlaUtils.getConstantsMap(moduleNode.getConstantDecls());
		this.bConstantList.addAll(constants.values());

		this.nextNode = evalPredicate(configAst.getNext(), "next state"); // check if NEXT declaration is a valid definition
		this.initNode = evalPredicate(configAst.getInit(), "initialisation"); // check if INIT declaration is a valid definition
		this.specNode = evalPredicate(configAst.getSpec(), "specification"); // check if SPECIFICATION declaration is a valid definition

		if (moduleNode.getVariableDecls().length > 0 && this.initNode == null && this.specNode == null) {
			throw new ConfigFileErrorException("The module contains variables."
					+ " Hence there must be either a SPECIFICATION or INIT declaration.");
		}

		evalInvariants(); // check if INVARIANT declarations are valid definitions
		evalConstantOrDefOverrides();
		evalConstantOrOperatorAssignments();
		evalModConOrDefAssignments();
		evalModConOrDefOverrides();
	}

	private OpDefNode evalPredicate(String predicate, String description) throws ConfigFileErrorException {
		if (!predicate.isEmpty()) {
			if (!definitions.containsKey(predicate)) {
				throw new ConfigFileErrorException("Invalid declaration of the " + description + " predicate."
						+ " Module does not contain the definition '" + predicate + "'");
			}
			return definitions.get(predicate);
		}
		return null;
	}

	private void evalInvariants() throws ConfigFileErrorException {
		Vect<?> v = configAst.getInvariants();
		for (int i = 0; i < v.capacity(); i++) {
			if (v.elementAt(i) != null) {
				String inv = (String) v.elementAt(i);
				if (!definitions.containsKey(inv)) {
					throw new ConfigFileErrorException("Invalid invariant declaration. Module does not contain definition '" + inv + "'");
				}
				invariantNodeList.add(definitions.get(inv));
			}
		}
	}

	/**
	 * Represents an override statement in the configuration file: k &lt;- def
	 */
	private void evalConstantOrDefOverrides() throws ConfigFileErrorException {
		for (Map.Entry<String, String> entry : configAst.getOverrides().entrySet()) {
			String left = entry.getKey();
			String right = entry.getValue();

			OpDefNode rightDefNode = definitions.get(right);
			if (rightDefNode == null) {
				throw new ConfigFileErrorException("Invalid substitution for " + left
						+ ".\n Module does not contain definition " + right + ".");
			}

			if (constants.containsKey(left)) {
				// a constant is overridden by an operator
				OpDeclNode conNode = constants.get(left);
				if (conNode.getArity() != rightDefNode.getArity()) {
					throw new ConfigFileErrorException(
						String.format(
							"Invalid substitution for %s.%n Constant %s has %s arguments while %s has %s arguments.",
							left, left, conNode.getArity(), right,
							rightDefNode.getArity()));
				}
				if (conNode.getArity() > 0) {
					bConstantList.remove(conNode); // Why?
					// to not get error message Constant 'Leader' must be overridden in the configuration file.
					// but we get other problem
				}
				DebugUtils.printMsg("Putting Constant into CONSTANT OverrideTable " + conNode.getName() + "/" + conNode.getArity());
				constantOverrides.put(conNode, rightDefNode);
			} else if (definitions.containsKey(left)) {
				// an operator is overridden by another operator
				OpDefNode defNode = definitions.get(left);
				if (defNode.getArity() != rightDefNode.getArity()) {
					throw new ConfigFileErrorException(
						String.format(
							"Invalid substitution for %s.%n Operator %s has %s arguments while %s has %s arguments.",
							left, left, defNode.getArity(), right,
							rightDefNode.getArity()));
				}

				DebugUtils.printMsg("Putting Definition into OPERATOR OverrideTable " + defNode.getName() + "/" + defNode.getArity());
				operatorOverrides.put(defNode, rightDefNode);
			} else {
				// every constant in the configuration file must appear in the TLA+ module
				throw new ConfigFileErrorException("Module does not contain the symbol: " + left);
			}
		}
	}

	private void evalConstantOrOperatorAssignments() throws ConfigFileErrorException {
		Vect<?> configCons = configAst.getConstants();
		// iterate over all constant or operator assignments in the config file
		// k = 1 or def = 1
		for (int i = 0; i < configCons.size(); i++) {
			Vect<?> symbol = (Vect<?>) configCons.elementAt(i);
			String symbolName = symbol.elementAt(0).toString();
			Value symbolValue = (Value) symbol.elementAt(symbol.size() - 1);
			TLAType symbolType = conGetType(symbol.elementAt(symbol.size() - 1));
			if (constants.containsKey(symbolName)) {
				OpDeclNode c = constants.get(symbolName);

				ValueObj valueObj = new ValueObj(symbolValue, symbolType);
				constantAssignments.put(c, valueObj);
				// if conValue is a model value and the name of the value is the
				// same as the name of constants, then the constant declaration
				// in the resulting B machine disappears
				if (symbolType instanceof EnumType && symbolName.equals(symbolValue.toString())) {
					bConstantList.remove(c);
				}
			} else if (definitions.containsKey(symbolName)) {
				OpDefNode def = definitions.get(symbolName);
				ValueObj valueObj = new ValueObj(symbolValue, symbolType);
				operatorAssignments.put(def, valueObj);

				if (symbolType instanceof SetType && ((SetType) symbolType).getSubType() instanceof EnumType) {
					operatorModelvalues.add(def);
				} else if ((symbolType instanceof EnumType)) {
					operatorModelvalues.add(def);
				}
			} else {
				// every constant or operator in the configuration file must appear in the TLA+ module
				throw new ConfigFileErrorException("Module does not contain the symbol: " + symbolName);
			}
		}
	}

	private void evalModConOrDefAssignments() throws ConfigFileErrorException {
		// val = [Counter] 7
		@SuppressWarnings("unchecked")
		Hashtable<String, Vect<?>> configCons = configAst.getModConstants();
		Enumeration<String> moduleNames = configCons.keys();
		while (moduleNames.hasMoreElements()) {
			String moduleName = moduleNames.nextElement();
			ModuleNode mNode = searchModule(moduleName);
			Vect<?> assignments = configCons.get(moduleName);
			for (int i = 0; i < assignments.size(); i++) {
				Vect<?> assigment = (Vect<?>) assignments.elementAt(i);
				OpDefOrDeclNode opDefOrDeclNode = searchDefinitionOrConstant(mNode, (String) assigment.elementAt(0));
				String symbolName = opDefOrDeclNode.getName().toString();
				Value symbolValue = (Value) assigment.elementAt(1);
				TLAType symbolType = conGetType(assigment.elementAt(1));
				// System.out.println(symbolName + " " + symbolValue+ " " +
				// symbolType);
				if (opDefOrDeclNode instanceof OpDeclNode) {
					// TODO test whether c is a extended constant
					// Instanced constants have to overridden in the instance
					// statement
					OpDeclNode c = (OpDeclNode) opDefOrDeclNode;
					ValueObj valueObj = new ValueObj(symbolValue, symbolType);
					constantAssignments.put(c, valueObj);
					// if conValue is a model value and the name of value is the
					// same as the name of constants, then the constant
					// declaration in the resulting B machine disappears
					if (symbolName.equals(symbolValue.toString())) {
						bConstantList.remove(c);
					}
				} else {
					OpDefNode def = (OpDefNode) opDefOrDeclNode;
					ValueObj valueObj = new ValueObj(symbolValue, symbolType);
					operatorAssignments.put(def, valueObj);

					if (symbolType instanceof SetType) {
						if (((SetType) symbolType).getSubType() instanceof EnumType) {
							operatorModelvalues.add(def);
						}
					} else if ((symbolType instanceof EnumType)) {
						operatorModelvalues.add(def);
					}
				}
			}
		}
	}

	private void evalModConOrDefOverrides() throws ConfigFileErrorException {
		// foo <- [Counter] bar or k <- [Counter] bar
		@SuppressWarnings("unchecked")
		Hashtable<String, Hashtable<String, String>> configCons = configAst.getModOverrides();
		Enumeration<String> moduleNames = configCons.keys();
		while (moduleNames.hasMoreElements()) {
			String moduleName = moduleNames.nextElement();
			ModuleNode mNode = searchModule(moduleName);
			Hashtable<String, String> o = configCons.get(moduleName);

			for (Map.Entry<String, String> entry : o.entrySet()) {
				String left = entry.getKey();
				String right = entry.getValue();

				OpDefNode rightDefNode = definitions.get(right);
				if (rightDefNode == null) {
					throw new ConfigFileErrorException(
						"Invalid substitution for " + left
							+ ".\n Module does not contain definition "
							+ right + ".");
				}
				OpDefOrDeclNode opDefOrDeclNode = searchDefinitionOrConstant(mNode, left);

				if (opDefOrDeclNode instanceof OpDefNode) {
					// an operator is overridden by another operator
					OpDefNode defNode = (OpDefNode) opDefOrDeclNode;
					if (defNode.getArity() != rightDefNode.getArity()) {
						throw new ConfigFileErrorException(
							String.format(
								"Invalid substitution for %s.%n Operator %s has %s arguments while %s has %s arguments.",
								left, left, defNode.getArity(), right,
								rightDefNode.getArity()));
					}
					operatorOverrides.put(defNode, rightDefNode);
				} else {
					InstanceNode[] instanceNodes = moduleNode.getInstances();
					for (int i = 0; i < instanceNodes.length; i++) {
						// if (instanceNodes[i].getModule().getName().toString()
						// .equals(moduleName)) {
						// /*
						// * A constant overridden in an instanced module make
						// * no sense. Such a constant will be overridden by
						// * the instance statement
						// */
						// throw new ConfigFileErrorException(
						// String.format(
						// "Invalid substitution for constant '%s' of module '%s'.%n A Constant of an instanced module can not be overridden.",
						// left, mNode.getName().toString()));
						// }
					}
					// a constant is overridden by an operator
					OpDeclNode conNode = (OpDeclNode) opDefOrDeclNode;
					if (conNode.getArity() != rightDefNode.getArity()) {
						throw new ConfigFileErrorException(
							String.format(
								"Invalid substitution for %s.%n Constant %s has %s arguments while %s has %s arguments.",
								left, left, conNode.getArity(), right,
								rightDefNode.getArity()));
					}
					bConstantList.remove(conNode);
					constantOverrides.put(conNode, rightDefNode);
				}
			}
		}
	}

	public ModuleNode searchModule(String moduleName) throws ConfigFileErrorException {
		/*
		 * Search module in extended modules
		 */
		HashSet<ModuleNode> extendedModules = moduleNode.getExtendedModuleSet();
		for (ModuleNode m : extendedModules) {
			if (m.getName().toString().equals(moduleName)) {
				return m;
			}
		}

		/*
		 * search module in instanced modules
		 */
		OpDefNode[] defs = moduleNode.getOpDefs();
		for (int j = defs.length - 1; j > 0; j--) {
			OpDefNode def = null;
			OpDefNode source = defs[j];
			while (def != source) {
				def = source;
				source = def.getSource();
				ModuleNode m = def.getOriginallyDefinedInModuleNode();
				if (m.getName().toString().equals(moduleName)) {
					return m;
				}
			}
		}
		throw new ConfigFileErrorException(String.format("Module '%s' is not included in the specification.", moduleName));
	}

	public OpDefOrDeclNode searchDefinitionOrConstant(ModuleNode n, String defOrConName) throws ConfigFileErrorException {
		for (OpDefNode opDef : n.getOpDefs()) {
			if (opDef.getName().toString().equals(defOrConName))
				return opDef;
		}
		for (OpDeclNode opDecl : n.getConstantDecls()) {
			if (opDecl.getName().toString().equals(defOrConName))
				return opDecl;
		}
		throw new ConfigFileErrorException("Module does not contain the symbol: " + defOrConName);
	}

	private TLAType conGetType(Object o) throws ConfigFileErrorException {
		if (o instanceof IntValue) {
			// IntValue iv = (IntValue) o;
			return IntType.getInstance();
		} else if (o.getClass().getName().equals("tlc2.value.impl.SetEnumValue")) {
			SetEnumValue set = (SetEnumValue) o;
			SetType t = new SetType(new UntypedType());
			if (set.isEmpty()) {
				throw new ConfigFileErrorException("empty set is not permitted!");
			}
			TLAType elemType;

			if (set.elems.elementAt(0).getClass().getName().equals("tlc2.value.impl.ModelValue")) {
				EnumType e = new EnumType(new ArrayList<>());
				for (int i = 0; i < set.size(); i++) {
					if (set.elems.elementAt(i).getClass().getName().equals("tlc2.value.impl.ModelValue")) {
						String mv = set.elems.elementAt(i).toString();
						if (!enumeratedSet.contains(mv)) {
							enumeratedSet.add(mv);
							e.modelvalues.add(mv);
						} else {
							e.modelvalues.add(mv);
							EnumType e2 = enumeratedTypes.get(mv);
							try {
								e = e2.unify(e2);
							} catch (UnificationException exception) {
							}
						}

					} else {
						throw new ConfigFileErrorException("Elements of the set must have the same type: " + o);
					}
				}
				for (String s : e.modelvalues) {
					enumeratedTypes.put(s, e);
				}
				elemType = e;
			} else {
				elemType = conGetType(set.elems.elementAt(0));
				for (int i = 1; i < set.size(); i++) {
					elemType = conGetType(set.elems.elementAt(i));
					// all Elements have the same Type?
					if (!t.getSubType().compare(elemType)) {
						throw new ConfigFileErrorException("Elements of the set must have the same type: " + o);
					}
				}
			}
			t.setSubType(elemType);
			return t;

		} else if (o.getClass().getName().equals("tlc2.value.impl.ModelValue")) {
			String mv = ((ModelValue) o).toString();
			if (!enumeratedSet.contains(mv)) {
				enumeratedSet.add(mv);
				EnumType e = new EnumType(Collections.singletonList(mv));
				enumeratedTypes.put(mv, e);
				return e;
			} else {
				return enumeratedTypes.get(mv);
			}

		} else if (o.getClass().getName().equals("tlc2.value.impl.StringValue")) {
			return StringType.getInstance();
		} else if (o.getClass().getName().equals("tlc2.value.impl.BoolValue")) {
			return BoolType.getInstance();
		} else {
			throw new ConfigFileErrorException("Unknown ConstantType: " + o + " " + o.getClass());
		}
	}

	public OpDefNode getSpecNode() {
		return specNode;
	}

	public OpDefNode getNextNode() {
		return nextNode;
	}

	public OpDefNode getInitNode() {
		return initNode;
	}

	public Map<OpDeclNode, OpDefNode> getConstantOverrides() {
		return constantOverrides;
	}

	public List<OpDefNode> getInvariants() {
		return this.invariantNodeList;
	}

	public Map<OpDeclNode, ValueObj> getConstantAssignments() {
		return this.constantAssignments;
	}

	public Map<OpDefNode, ValueObj> getOperatorAssignments() {
		return this.operatorAssignments;
	}

	public List<OpDeclNode> getbConstantList() {
		return bConstantList;
	}

	public Map<OpDefNode, OpDefNode> getOperatorOverrides() {
		return operatorOverrides;
	}

	public List<String> getEnumerationSet() {
		return this.enumeratedSet;
	}

	public List<OpDefNode> getOperatorModelvalues() {
		return this.operatorModelvalues;
	}
}
