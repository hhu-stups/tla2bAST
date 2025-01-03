package de.tla2bAst;

import de.be4.classicalb.core.parser.node.Start;
import de.tla2b.analysis.SpecAnalyser;
import de.tla2b.analysis.SymbolRenamer;
import de.tla2b.analysis.TypeChecker;
import de.tla2b.exceptions.ExpressionTranslationException;
import de.tla2b.exceptions.TLA2BException;
import de.tla2b.exceptions.TLA2BFrontEndException;
import de.tla2b.global.BBuiltInOPs;
import de.tla2b.util.TlaUtils;
import tla2sany.drivers.FrontEndException;
import tla2sany.drivers.InitException;
import tla2sany.drivers.SANY;
import tla2sany.modanalyzer.ParseUnit;
import tla2sany.modanalyzer.SpecObj;
import tla2sany.parser.ParseException;
import tla2sany.semantic.FormalParamNode;
import tla2sany.semantic.ModuleNode;
import tla2sany.semantic.OpDeclNode;
import tla2sany.semantic.OpDefNode;
import tla2sany.semantic.SymbolNode;
import tla2sany.st.SyntaxTreeConstants;
import tla2sany.st.TreeNode;
import util.ToolIO;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.*;
import java.util.stream.Collectors;

public class ExpressionTranslator implements SyntaxTreeConstants {

	private final String tlaExpression;
	private final List<String> variables = new ArrayList<>();
	private final List<String> noVariables = new ArrayList<>();
	private final Map<String, FormalParamNode[]> definitions = new HashMap<>();
	private final Map<String, SymbolNode> namingMap = new HashMap<>();
	private ModuleNode moduleNode;
	private String expr;
	private Translator translator;

	/**
	 * @deprecated Internal use only. Use {@link #translate(String)} instead.
	 */
	@Deprecated
	public ExpressionTranslator(String tlaExpression) {
		this.tlaExpression = tlaExpression;
	}

	/**
	 * @deprecated Internal use only. Use {@link #translate(String, Translator)} instead.
	 */
	@Deprecated
	public ExpressionTranslator(String tlaExpression, Translator translator) {
		this.tlaExpression = tlaExpression;
		this.translator = translator;
		ModuleNode moduleContext = translator.getSpecAnalyser().getModuleNode(); // NOT this.moduleNode !
		// this is the module in whose context the expression is to be evaluated
		this.namingMap.putAll(TlaUtils.getDeclarationsMap(moduleContext.getVariableDecls()));
		this.namingMap.putAll(TlaUtils.getDeclarationsMap(moduleContext.getConstantDecls()));
		// we need all definitions of the context module, not only the translated ones
		this.namingMap.putAll(TlaUtils.getOpDefsMap(moduleContext.getOpDefs()));
	}

	/**
	 * @deprecated Internal use only. Use {@link #translate(String)} or {@link #translate(String,Translator)} instead.
	 */
	@Deprecated
	public void parse() {
		String dir = System.getProperty("java.io.tmpdir");
		ToolIO.setUserDir(dir);

		File tempFile;
		try {
			tempFile = File.createTempFile("Expression", ".tla");
		} catch (IOException e) {
			throw new ExpressionTranslationException("Can not create temporary file in directory '" + dir + "'");
		}

		String moduleName = tempFile.getName().substring(0,tempFile.getName().indexOf("."));
		String module = "----MODULE " + moduleName + " ----\n" + "Expression == " + tlaExpression + "\n====";

		try (FileWriter fw = new FileWriter(tempFile)) {
			fw.write(module);
		} catch (IOException e) {
			throw new ExpressionTranslationException("Can not write module to temporary file " + tempFile.getAbsolutePath());
		}

		SpecObj spec = parseModuleWithoutSemanticAnalyse(moduleName, module);
		evalVariables(spec, moduleName);

		StringBuilder sb = new StringBuilder();
		sb.append("----MODULE ").append(moduleName).append(" ----\n");
		sb.append("EXTENDS Naturals, Integers, Reals, Sequences, FiniteSets \n");
		if (!variables.isEmpty()) {
			sb.append("VARIABLES ");
			sb.append(String.join(", ", variables));
			sb.append("\n");
		}
		if (!definitions.isEmpty()) {
			// just add def with dummy tuple; node will be replaced later
			definitions.forEach((name, params) -> {
				List<String> paramNames = Arrays.stream(definitions.getOrDefault(name, new FormalParamNode[0]))
						.map(p -> p.getName().toString())
						.collect(Collectors.toList());
				sb.append(name);
				if (!paramNames.isEmpty()) {
					sb.append("(");
					sb.append(String.join(", ", paramNames));
					sb.append(")");
				}
				sb.append(" == <<");
				if (!paramNames.isEmpty()) {
					sb.append(String.join(", ", paramNames));
				}
				sb.append(">>\n");
			});
		}
		sb.append("Expression");
		sb.append(" == ");
		sb.append(tlaExpression);
		sb.append("\n====================");

		this.expr = sb.toString();
		try (FileWriter fw = new FileWriter(tempFile)) {
			fw.write(expr);
			tempFile.deleteOnExit();
		} catch (IOException e) {
			throw new ExpressionTranslationException(e.getMessage());
		}
		ToolIO.reset();

		this.moduleNode = null;
		try {
			moduleNode = parseModule(moduleName, sb.toString());
		} catch (TLA2BFrontEndException e) {
			throw new ExpressionTranslationException(e.getLocalizedMessage());
		}
	}

	/**
	 * translate a standalone TLA+ expression without any context
	 */
	public static Start translate(String tlaExpression) {
		ExpressionTranslator expressionTranslator = new ExpressionTranslator(tlaExpression);
		expressionTranslator.parse();
		return expressionTranslator.translate();
	}

	/**
	 * translate a TLA+ expression in the context of another module, given its translator
	 */
	public static Start translate(String tlaExpression, Translator translator) {
		ExpressionTranslator expressionTranslator = new ExpressionTranslator(tlaExpression, translator);
		expressionTranslator.parse();
		expressionTranslator.setTypesOfExistingNodes();
		return expressionTranslator.translate();
	}

	/**
	 * @deprecated Internal use only. Use {@link #translate(String)} or {@link #translate(String,Translator)} instead.
	 */
	@Deprecated
	public Start translate() {
		SpecAnalyser specAnalyser = SpecAnalyser.createSpecAnalyserForTlaExpression(moduleNode);
		TypeChecker tc = new TypeChecker(moduleNode, specAnalyser);
		try {
			tc.start();
		} catch (TLA2BException e) {
			String message = "****TypeError****\n" + e.getLocalizedMessage() + "\n" + expr + "\n";
			throw new ExpressionTranslationException(message);
		}
		SymbolRenamer.run(moduleNode, specAnalyser);
		return new BAstCreator(moduleNode, specAnalyser).getStartNode();
	}

	@Deprecated
	public Start translateIncludingModel() {
		setTypesOfExistingNodes();
		return translate();
	}

	@Deprecated
	public Start translateWithoutModel() {
		return translate();
	}

	private ModuleNode parseModule(String moduleName, String module) throws TLA2BFrontEndException {
		SpecObj spec = new SpecObj(moduleName, null);
		try {
			SANY.frontEndMain(spec, moduleName, ToolIO.out);
		} catch (FrontEndException e) {
			// Error in Frontend, should never happen
			throw new TLA2BFrontEndException("Frontend error! This should never happen.", spec);
		}

		if (spec.parseErrors.isFailure()) {
			String message = module + "\n\n" + spec.parseErrors + allMessagesToString(ToolIO.getAllMessages());
			throw new TLA2BFrontEndException(message, spec);
		}

		if (spec.semanticErrors.isFailure()) {
			String message = module + "\n\n" + spec.semanticErrors + allMessagesToString(ToolIO.getAllMessages());
			throw new TLA2BFrontEndException(message, spec);
		}

		// RootModule
		ModuleNode n = spec.getExternalModuleTable().rootModule;
		if (spec.getInitErrors().isFailure()) {
			System.err.println(spec.getInitErrors());
			throw new TLA2BFrontEndException(allMessagesToString(ToolIO.getAllMessages()), spec);
		}

		if (n == null) { // Parse Error
			// System.out.println("Rootmodule null");
			throw new TLA2BFrontEndException(allMessagesToString(ToolIO.getAllMessages()), spec);
		}
		return n;
	}

	private SpecObj parseModuleWithoutSemanticAnalyse(String moduleFileName, String module) {
		SpecObj spec = new SpecObj(moduleFileName, null);
		try {
			SANY.frontEndInitialize(spec, ToolIO.err);
			SANY.frontEndParse(spec, ToolIO.err);
		} catch (InitException | ParseException e) {
			throw new ExpressionTranslationException(e.getLocalizedMessage());
		}

		if (spec.parseErrors.isFailure()) {
			throw new ExpressionTranslationException(module + "\n\n" + allMessagesToString(ToolIO.getAllMessages()));
		}
		return spec;
	}

	private void evalVariables(SpecObj spec, String moduleName) {
		ParseUnit p = spec.parseUnitContext.get(moduleName);
		TreeNode n_module = p.getParseTree();
		TreeNode n_body = n_module.heirs()[2];
		TreeNode n_operatorDefinition = n_body.heirs()[0];
		TreeNode expr = n_operatorDefinition.heirs()[2];
		searchVarInSyntaxTree(expr);

		// this code seems to assume that there is no variable clash between outer and nested variables
		// I guess the parser will then generate "Multiply-defined symbol ..." errors
		for (String noVariable : noVariables) {
			variables.remove(noVariable);
		}
	}

	private final static Set<String> KEYWORDS = new HashSet<>();

	static {
		KEYWORDS.add("BOOLEAN");
		KEYWORDS.add("TRUE");
		KEYWORDS.add("FALSE");
		KEYWORDS.add("Nat");
		KEYWORDS.add("Int");
		KEYWORDS.add("Real");
		KEYWORDS.add("Infinity");
		KEYWORDS.add("Cardinality");
		KEYWORDS.add("IsFiniteSet");
		KEYWORDS.add("Append");
		KEYWORDS.add("Head");
		KEYWORDS.add("Tail");
		KEYWORDS.add("Len");
		KEYWORDS.add("Seq");
		KEYWORDS.add("SubSeq");
		KEYWORDS.add("SelectSeq");
		KEYWORDS.add("MinOfSet");
		KEYWORDS.add("MaxOfSet");
		KEYWORDS.add("SetProduct");
		KEYWORDS.add("SetSummation");
		KEYWORDS.add("PermutedSequences");
		KEYWORDS.add("@");
	}

	/**
	 * collect variables and definitions from syntax tree
	 */
	private void searchVarInSyntaxTree(TreeNode treeNode) {
		// System.out.println(treeNode.getKind() + " " + treeNode.getImage());
		switch (treeNode.getKind()) {
			case N_GeneralId: {
				String con = treeNode.heirs()[1].getImage();
				if (!variables.contains(con) && !KEYWORDS.contains(con)) {
					SymbolNode existingNode = namingMap.get(con);
					if (existingNode instanceof OpDefNode) {
						// if the identifier corresponds to an existing def, add as def, otherwise as variable
						definitions.put(con, ((OpDefNode) existingNode).getParams());
					} else {
						variables.add(con);
					}
				}
				break;
			}
			case N_IdentLHS: { // left side of a definition
				TreeNode[] children = treeNode.heirs();
				noVariables.add(children[0].getImage());
				break;
			}
			case N_IdentDecl: { // parameter of a LET definition
				// e.g. x in LET foo(x) == e
				noVariables.add(treeNode.heirs()[0].getImage());
				break;
			}
			case N_FunctionDefinition: {
				// the first child is the function name
				noVariables.add(treeNode.heirs()[0].getImage());
				break;
			}
			case N_UnboundQuant: { // TODO: check: is this an unbounded quantifier with infinite domain or a quantifier that does not hide the quantified variables?
				TreeNode[] children = treeNode.heirs();
				//for (int i = 1; i < children.length - 2; i = i + 2) {
					// System.out.println("N_UnboundQuant: "+children[i].getImage());
				//}
				searchVarInSyntaxTree(treeNode.heirs()[children.length - 1]);
				break;
			}
			case N_UnboundOrBoundChoose: { // not sure the format is the same as N_QuantBound
				TreeNode[] children = treeNode.heirs();
				for (int i = 1; i < children.length - 2; i = i + 2) {
					String boundedVar = children[i].getImage();
					// typically children[i+1] is N_MaybeBound
					if (!noVariables.contains(boundedVar)) {
						noVariables.add(boundedVar);
						//System.out.println("CHOOSE quantified variable: " + boundedVar);
					}
				}
				searchVarInSyntaxTree(treeNode.heirs()[children.length - 1]);
				break;
			}
			case N_QuantBound: {
				TreeNode[] children = treeNode.heirs();
				for (int i = 0; i < children.length - 2; i = i + 2) {
					String boundedVar = children[i].getImage();
					if (!noVariables.contains(boundedVar)) {
						noVariables.add(boundedVar);
						// System.out.println("N_QuantBound: locally quantified variable" + boundedVar);
					}
				}
				searchVarInSyntaxTree(treeNode.heirs()[children.length - 1]);
				break;
			}
			case N_SubsetOf: { // { x \in S : e }
				TreeNode[] children = treeNode.heirs();
				String boundedVar = children[1].getImage(); // x
				if (!noVariables.contains(boundedVar)) {
					noVariables.add(boundedVar);
				}
				searchVarInSyntaxTree(treeNode.heirs()[3]); // S
				searchVarInSyntaxTree(treeNode.heirs()[5]); // e
				break;
			}
		}

		for (TreeNode heir : treeNode.heirs()) {
			searchVarInSyntaxTree(heir);
		}
	}

	private void setTypesOfExistingNodes() {
		if (translator != null) {
			for (OpDeclNode node : moduleNode.getConstantDecls())
				setTypeExistingDeclNode(node);
			for (OpDeclNode node : moduleNode.getVariableDecls())
				setTypeExistingDeclNode(node);
			for (OpDefNode node : moduleNode.getOpDefs()) {
				SymbolNode fromSpec = namingMap.get(node.getName().toString());
				if (fromSpec != null) { // a definition with the same name exists in module context
					// check if def in translated B definitions
					if (translator.getSpecAnalyser().getBDefinitions().contains((OpDefNode) fromSpec)) {
						// replace body of dummy definition with body of the real definition
						node.setBody(((OpDefNode) fromSpec).getBody());
						// not sure if we should also replace defNode in Context:
						// nCtx.addSymbolToContext(node.getName(), fromSpec);
						// this should be redundant and not necessary:
						// TypeChecker.setType(node, TypeChecker.getType(fromSpec));
					} else if (!BBuiltInOPs.isBBuiltInOp(node)) {
						// throw error if def is not included in translation and not a built-in definition
						throw new ExpressionTranslationException("Evaluation error:\n"
								+ "Definition '" + fromSpec.getName() + "' is not included in the B translation.\n");
					}
				}
			}
		}
	}

	private void setTypeExistingDeclNode(OpDeclNode node) {
		SymbolNode fromSpec = namingMap.get(node.getName().toString());
		if (fromSpec != null) { // a constant or variable declaration with the same name exists in module context
			// replace all decl nodes by the known decl from the real module
			// nCtx.addSymbolToContext(node.getName(), fromSpec);
			// set the type of the declaration in the dummy module (CONSTANTS/VARIABLES section)
			TypeChecker.setType(node, TypeChecker.getType(fromSpec));
		}
	}

	public static String allMessagesToString(String[] allMessages) {
		return Translator.allMessagesToString(allMessages);
	}
}
