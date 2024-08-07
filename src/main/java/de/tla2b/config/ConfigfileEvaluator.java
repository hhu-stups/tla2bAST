package de.tla2b.config;

import de.tla2b.exceptions.ConfigFileErrorException;
import de.tla2b.exceptions.UnificationException;
import de.tla2b.types.*;
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

	private ModelConfig configAst;
	private ModuleNode moduleNode;
	private Hashtable<String, OpDefNode> definitions;
	// Hashtable of all definitions in module
	private Hashtable<String, OpDeclNode> constants;
	// Hashtable of all constants in the module

	private OpDefNode specNode; // SPECIFICATION node, may be null
	private OpDefNode nextNode; // NEXT node, may be null
	private OpDefNode initNode; // INIT node, may be null
	private final ArrayList<OpDefNode> invariantNodeList = new ArrayList<>();
	private ArrayList<String> enumeratedSet;
	private LinkedHashMap<String, EnumType> enumeratedTypes;
	public Hashtable<OpDeclNode, ValueObj> constantAssignments;
	// k = 1, the ValueObj describes the right side of the assignment and
	// contains it type
	public Hashtable<OpDefNode, ValueObj> operatorAssignments;
	// def = 1

	private ArrayList<OpDefNode> operatorModelvalues;

	private final ArrayList<OpDeclNode> bConstantList = new ArrayList<>();
	// List of constants in the resulting B machine. This list does not contain
	// a TLA+ constant if the constant is substituted by a modelvalue with the
	// same name (the constant name is moved to an enumerated set) or if the
	// constants has arguments and is overridden by an operator
	public Hashtable<OpDefNode, OpDefNode> operatorOverrideTable;
	// This table contains mappings for operators which are overridden in the
	// configuration file
	public Hashtable<OpDeclNode, OpDefNode> constantOverrideTable;

	// This table contains mappings for constants which are overridden in the
	// configuration file. All constants with arguments have to be overridden in
	// the configuration file.

	public ConfigfileEvaluator(ModelConfig configAst, ModuleNode moduleNode) {
		this.configAst = configAst;
		this.moduleNode = moduleNode;

		definitions = new Hashtable<>();
		OpDefNode[] defs = moduleNode.getOpDefs();
		for (OpDefNode def : defs) {
			definitions.put(def.getName().toString(), def);
		}

		constants = new Hashtable<>();
		OpDeclNode[] cons = moduleNode.getConstantDecls();
		for (OpDeclNode con : cons) {
			constants.put(con.getName().toString(), con);
			bConstantList.add(con);
		}

		initialize();
	}

	public ConfigfileEvaluator() {
		initialize();
	}

	private void initialize() {
		this.constantOverrideTable = new Hashtable<>();
		this.operatorOverrideTable = new Hashtable<>();

		this.constantAssignments = new Hashtable<>();
		this.operatorAssignments = new Hashtable<>();
		this.operatorModelvalues = new ArrayList<>();

		this.enumeratedSet = new ArrayList<>();
		this.enumeratedTypes = new LinkedHashMap<>();
	}

	public void start() throws ConfigFileErrorException {
		evalNext(); // check if NEXT declaration is a valid definition
		evalInit(); // check if INIT declaration is a valid definition
		evalSpec(); // check if SPECIFICATION declaration is a valid definition

		if (moduleNode.getVariableDecls().length > 0 && this.initNode == null
			&& this.specNode == null) {
			throw new ConfigFileErrorException(
				"The module contains variables."
					+ " Hence there must be either a SPECIFICATION or INIT declaration.");
		}

		evalInvariants();
		// check if INVARIANT declarations are valid definitions

		evalConstantOrDefOverrides();

		evalConstantOrOperatorAssignments();

		evalModConOrDefAssignments();

		evalModConOrDefOverrides();

	}


	private void evalNext() throws ConfigFileErrorException {
		String next = configAst.getNext();
		if (!next.isEmpty()) {
			if (definitions.containsKey(next)) {
				this.nextNode = definitions.get(next);
			} else {
				throw new ConfigFileErrorException(
					"Invalid declaration of the next state predicate."
						+ " Module does not contain the definition '"
						+ next + "'");
			}
		} else
			next = null;

	}

	private void evalInit() throws ConfigFileErrorException {
		String init = configAst.getInit();
		if (!init.isEmpty()) {
			if (definitions.containsKey(init)) {
				this.initNode = definitions.get(init);
			} else {
				throw new ConfigFileErrorException(
					"Invalid declaration of the initialisation predicate."
						+ " Module does not contain the definition '"
						+ init + "'");
			}
		} else {
			init = null;
		}

	}

	private void evalSpec() throws ConfigFileErrorException {
		String spec = configAst.getSpec();
		if (!spec.isEmpty()) {
			if (definitions.containsKey(spec)) {
				this.specNode = definitions.get(spec);
			} else {
				throw new ConfigFileErrorException(
					"Invalid declaration of the specification predicate."
						+ "Module does not contain the definition '"
						+ spec + "'");
			}
		} else
			spec = null;
	}

	private void evalInvariants() throws ConfigFileErrorException {

		Vect v = configAst.getInvariants();
		if (v.capacity() != 0) {
			for (int i = 0; i < v.capacity(); i++) {
				if (v.elementAt(i) != null) {
					String inv = (String) v.elementAt(i);
					if (!definitions.containsKey(inv)) {
						throw new ConfigFileErrorException(
							"Invalid invariant declaration. Module does not contain definition '"
								+ inv + "'");
					}
					invariantNodeList.add(definitions.get(inv));
				}
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
				throw new ConfigFileErrorException("Invalid substitution for "
					+ left + ".\n Module does not contain definition "
					+ right + ".");
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
					bConstantList.remove(conNode);
				}
				constantOverrideTable.put(conNode, rightDefNode);
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

				operatorOverrideTable.put(defNode, rightDefNode);
			} else {
				// every constant in the configuration file must appear in the TLA+ module
				throw new ConfigFileErrorException(
					"Module does not contain the symbol: " + left);
			}
		}
	}

	private void evalConstantOrOperatorAssignments()
		throws ConfigFileErrorException {
		Vect configCons = configAst.getConstants();
		// iterate over all constant or operator assignments in the config file
		// k = 1 or def = 1
		for (int i = 0; i < configCons.size(); i++) {
			Vect symbol = (Vect) configCons.elementAt(i);
			String symbolName = symbol.elementAt(0).toString();
			Value symbolValue = (Value) symbol.elementAt(symbol.size() - 1);
			TLAType symbolType = conGetType(symbol.elementAt(symbol.size() - 1));
			if (constants.containsKey(symbolName)) {
				OpDeclNode c = constants.get(symbolName);

				ValueObj valueObj = new ValueObj(symbolValue, symbolType);
				constantAssignments.put(c, valueObj);
				/**
				 * if conValue is a model value and the name of the value is the
				 * same as the name of constants, then the constant declaration
				 * in the resulting B machine disappears
				 **/
				if (symbolType instanceof EnumType
					&& symbolName.equals(symbolValue.toString())) {
					bConstantList.remove(c);
				}
			} else if (definitions.containsKey(symbolName)) {
				OpDefNode def = definitions.get(symbolName);
				ValueObj valueObj = new ValueObj(symbolValue, symbolType);
				operatorAssignments.put(def, valueObj);

				if (symbolType instanceof SetType) {
					if (((SetType) symbolType).getSubType() instanceof EnumType) {
						operatorModelvalues.add(def);
					}
				} else if ((symbolType instanceof EnumType)) {
					operatorModelvalues.add(def);
				}

			} else {
				// every constant or operator in the configuration file must appear in the TLA+ module
				throw new ConfigFileErrorException(
					"Module does not contain the symbol: " + symbolName);
			}
		}

	}

	private void evalModConOrDefAssignments() throws ConfigFileErrorException {
		// val = [Counter] 7
		@SuppressWarnings("unchecked")
		Hashtable<String, Vect> configCons = configAst.getModConstants();
		Enumeration<String> moduleNames = configCons.keys();
		while (moduleNames.hasMoreElements()) {
			String moduleName = moduleNames.nextElement();
			ModuleNode mNode = searchModule(moduleName);
			Vect assignments = configCons.get(moduleName);
			for (int i = 0; i < assignments.size(); i++) {
				Vect assigment = (Vect) assignments.elementAt(i);
				OpDefOrDeclNode opDefOrDeclNode = searchDefinitionOrConstant(
					mNode, (String) assigment.elementAt(0));
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
					/**
					 * if conValue is a model value and the name of value is the
					 * same as the name of constants, then the constant
					 * declaration in the resulting B machine disappears
					 **/
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
		Hashtable<String, Hashtable<String, String>> configCons = configAst
			.getModOverrides();
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
				OpDefOrDeclNode opDefOrDeclNode = searchDefinitionOrConstant(
					mNode, left);

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
					operatorOverrideTable.put(defNode, rightDefNode);
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
					constantOverrideTable.put(conNode, rightDefNode);

				}
			}

		}
	}

	public ModuleNode searchModule(String moduleName)
		throws ConfigFileErrorException {
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
		throw new ConfigFileErrorException(
			String.format(
				"Module '%s' is not included in the specification.",
				moduleName));
	}

	public OpDefOrDeclNode searchDefinitionOrConstant(ModuleNode n,
	                                                  String defOrConName) throws ConfigFileErrorException {
		for (int i = 0; i < n.getOpDefs().length; i++) {
			if (n.getOpDefs()[i].getName().toString().equals(defOrConName)) {
				return n.getOpDefs()[i];
			}
		}
		for (int i = 0; i < n.getConstantDecls().length; i++) {
			if (n.getConstantDecls()[i].getName().toString()
				.equals(defOrConName)) {
				return n.getConstantDecls()[i];
			}
		}
		throw new ConfigFileErrorException(
			"Module does not contain the symbol: " + defOrConName);
	}

	private TLAType conGetType(Object o) throws ConfigFileErrorException {
		if (o instanceof IntValue) {

			// IntValue iv = (IntValue) o;
			return IntType.getInstance();
		} else if (o.getClass().getName().equals("tlc2.value.impl.SetEnumValue")) {
			SetEnumValue set = (SetEnumValue) o;
			SetType t = new SetType(new UntypedType());
			if (set.isEmpty()) {
				throw new ConfigFileErrorException(
					"empty set is not permitted!");
			}
			TLAType elemType;

			if (set.elems.elementAt(0).getClass().getName()
				.equals("tlc2.value.impl.ModelValue")) {
				EnumType e = new EnumType(new ArrayList<>());
				for (int i = 0; i < set.size(); i++) {
					if (set.elems.elementAt(i).getClass().getName()
						.equals("tlc2.value.impl.ModelValue")) {
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
						throw new ConfigFileErrorException(
							"Elements of the set must have the same type: "
								+ o);
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
						throw new ConfigFileErrorException(
							"Elements of the set must have the same type: "
								+ o);
					}
				}
			}
			t.setSubType(elemType);
			return t;

		} else if (o.getClass().getName().equals("tlc2.value.impl.ModelValue")) {
			ModelValue mv = (ModelValue) o;
			if (!enumeratedSet.contains(mv.toString())) {
				enumeratedSet.add(mv.toString());
				ArrayList<String> temp = new ArrayList<>();
				temp.add(mv.toString());
				EnumType e = new EnumType(temp);
				enumeratedTypes.put(mv.toString(), e);
				return e;
			} else {
				return enumeratedTypes.get(mv.toString());
			}

		} else if (o.getClass().getName().equals("tlc2.value.impl.StringValue")) {
			return StringType.getInstance();
		} else if (o.getClass().getName().equals("tlc2.value.impl.BoolValue")) {
			return BoolType.getInstance();
		} else {
			throw new ConfigFileErrorException("Unknown ConstantType: " + o
				+ " " + o.getClass());
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

	public Hashtable<OpDeclNode, OpDefNode> getConstantOverrideTable() {
		return constantOverrideTable;
	}

	public ArrayList<OpDefNode> getInvariants() {
		return this.invariantNodeList;
	}

	public Hashtable<OpDeclNode, ValueObj> getConstantAssignments() {
		return this.constantAssignments;
	}

	public Hashtable<OpDefNode, ValueObj> getOperatorAssignments() {
		return this.operatorAssignments;
	}

	public ArrayList<OpDeclNode> getbConstantList() {
		return bConstantList;
	}

	public Hashtable<OpDefNode, OpDefNode> getOperatorOverrideTable() {
		return operatorOverrideTable;
	}

	public ArrayList<String> getEnumerationSet() {
		return this.enumeratedSet;
	}

	public ArrayList<OpDefNode> getOperatorModelvalues() {
		return this.operatorModelvalues;
	}
}
