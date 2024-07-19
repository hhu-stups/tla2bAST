package de.tla2bAst;

import de.be4.classicalb.core.parser.node.Start;
import de.tla2b.analysis.SpecAnalyser;
import de.tla2b.analysis.SymbolRenamer;
import de.tla2b.analysis.TypeChecker;
import de.tla2b.exceptions.ExpressionTranslationException;
import de.tla2b.exceptions.TLA2BException;
import tla2sany.drivers.FrontEndException;
import tla2sany.drivers.InitException;
import tla2sany.drivers.SANY;
import tla2sany.modanalyzer.ParseUnit;
import tla2sany.modanalyzer.SpecObj;
import tla2sany.parser.ParseException;
import tla2sany.semantic.ModuleNode;
import tla2sany.st.SyntaxTreeConstants;
import tla2sany.st.TreeNode;
import util.ToolIO;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.Set;

public class ExpressionTranslator implements SyntaxTreeConstants {

	private final String tlaExpression;
	private final ArrayList<String> variables = new ArrayList<>();
	private final ArrayList<String> noVariables = new ArrayList<>();
	private Start expressionStart;
	private ModuleNode moduleNode;
	private String expr;
	private Translator translator;

	public Start getBExpressionParseUnit() {
		return expressionStart;
	}

	public ExpressionTranslator(String tlaExpression) {
		this.tlaExpression = tlaExpression;
	}

	public ExpressionTranslator(String tlaExpression, Translator translator) {
		this.tlaExpression = tlaExpression;
		this.translator = translator;
	}

	public void parse() {
		String dir = System.getProperty("java.io.tmpdir");
		ToolIO.setUserDir(dir);

		File tempFile;
		String moduleName;
		String module;
		try {
			tempFile = File.createTempFile("Testing", ".tla");

			moduleName = tempFile.getName().substring(0,
				tempFile.getName().indexOf("."));

			module = "----MODULE " + moduleName + " ----\n" + "Expression == "
				+ tlaExpression + "\n====";

			FileWriter fw = new FileWriter(tempFile);
			fw.write(module);
			fw.close();
		} catch (IOException e) {
			throw new ExpressionTranslationException(
				"Can not create temporary file in directory '" + dir + "'");
		}

		SpecObj spec = parseModuleWithoutSemanticAnalyse(moduleName, module);
		evalVariables(spec, moduleName);

		StringBuilder sb = new StringBuilder();
		sb.append("----MODULE ").append(moduleName).append(" ----\n");
		sb.append("EXTENDS Naturals, Integers, Reals, Sequences, FiniteSets \n");
		if (!variables.isEmpty()) {
			sb.append("VARIABLES ");
			for (int i = 0; i < variables.size(); i++) {
				if (i != 0) {
					sb.append(", ");
				}
				sb.append(variables.get(i));
			}
			sb.append("\n");
		}
		sb.append("Expression");
		sb.append(" == ");
		sb.append(tlaExpression);
		sb.append("\n====================");

		try {
			FileWriter fw = new FileWriter(tempFile);
			fw.write(sb.toString());
			fw.close();
			tempFile.deleteOnExit();
		} catch (IOException e) {
			throw new ExpressionTranslationException(e.getMessage());
		}
		ToolIO.reset();

		this.expr = sb.toString();

		this.moduleNode = null;
		try {
			moduleNode = parseModule(moduleName, sb.toString());
		} catch (de.tla2b.exceptions.FrontEndException e) {
			throw new ExpressionTranslationException(e.getLocalizedMessage());
		}
	}

	public Start translateIncludingModel() throws TLA2BException {
		SpecAnalyser specAnalyser = SpecAnalyser
			.createSpecAnalyserForTlaExpression(moduleNode);
		TypeChecker tc = translator.getTypeChecker();
		tc.visitOpDefNode(specAnalyser.getExpressionOpdefNode());

		SymbolRenamer symRenamer = new SymbolRenamer(moduleNode, specAnalyser);
		symRenamer.start();
		BAstCreator bASTCreator = new BAstCreator(moduleNode, specAnalyser);

		this.expressionStart = bASTCreator.expressionStart;
		return this.expressionStart;
	}

	public Start translate() {
		SpecAnalyser specAnalyser = SpecAnalyser
			.createSpecAnalyserForTlaExpression(moduleNode);
		TypeChecker tc = new TypeChecker(moduleNode, specAnalyser);
		try {
			tc.start();
		} catch (TLA2BException e) {
			String message = "****TypeError****\n" + e.getLocalizedMessage()
				+ "\n" + expr + "\n";
			throw new ExpressionTranslationException(message);
		}
		SymbolRenamer symRenamer = new SymbolRenamer(moduleNode, specAnalyser);
		symRenamer.start();
		BAstCreator bASTCreator = new BAstCreator(moduleNode, specAnalyser);

		this.expressionStart = bASTCreator.expressionStart;
		return this.expressionStart;
	}

	public static ModuleNode parseModule(String moduleName, String module)
		throws de.tla2b.exceptions.FrontEndException {
		SpecObj spec = new SpecObj(moduleName, null);
		try {
			SANY.frontEndMain(spec, moduleName, ToolIO.out);
		} catch (FrontEndException e) {
			// Error in Frontend, should never happen
			throw new de.tla2b.exceptions.FrontEndException(
				"Frontend error! This should never happen.", spec);
		}

		if (spec.parseErrors.isFailure()) {
			String message = module + "\n\n" + spec.parseErrors;
			message += allMessagesToString(ToolIO.getAllMessages());
			throw new de.tla2b.exceptions.FrontEndException(message, spec);
		}

		if (spec.semanticErrors.isFailure()) {
			String message = module + "\n\n" + spec.semanticErrors;
			message += allMessagesToString(ToolIO.getAllMessages());
			throw new de.tla2b.exceptions.FrontEndException(message, spec);
		}

		// RootModule
		ModuleNode n = spec.getExternalModuleTable().rootModule;
		if (spec.getInitErrors().isFailure()) {
			System.err.println(spec.getInitErrors());
			throw new de.tla2b.exceptions.FrontEndException(

				allMessagesToString(ToolIO.getAllMessages()), spec);
		}

		if (n == null) { // Parse Error
			// System.out.println("Rootmodule null");
			throw new de.tla2b.exceptions.FrontEndException(
				allMessagesToString(ToolIO.getAllMessages()), spec);
		}
		return n;
	}

	private SpecObj parseModuleWithoutSemanticAnalyse(String moduleFileName,
	                                                  String module) {
		SpecObj spec = new SpecObj(moduleFileName, null);

		try {
			SANY.frontEndInitialize(spec, ToolIO.out);
			SANY.frontEndParse(spec, ToolIO.out);

		} catch (InitException | ParseException e1) {
			System.out.println(e1);
		}

		if (spec.parseErrors.isFailure()) {
			String message = module + "\n\n";
			message += allMessagesToString(ToolIO.getAllMessages());
			throw new ExpressionTranslationException(message);
		}
		return spec;
	}

	private void evalVariables(SpecObj spec, String moduleName) {
		ParseUnit p = spec.parseUnitContext.get(moduleName);
		TreeNode n_module = p.getParseTree();
		TreeNode n_body = n_module.heirs()[2];
		TreeNode n_operatorDefintion = n_body.heirs()[0];
		TreeNode expr = n_operatorDefintion.heirs()[2];
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
	 *
	 */
	private void searchVarInSyntaxTree(TreeNode treeNode) {
		// System.out.println(treeNode.getKind() + " " + treeNode.getImage());
		switch (treeNode.getKind()) {
			case N_GeneralId: {
				String con = treeNode.heirs()[1].getImage();
				if (!variables.contains(con) && !KEYWORDS.contains(con)) {
					variables.add(con);
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
			case
				N_UnboundQuant: { // TODO: check: is this an unbounded quantifier with infinite domain or a quantifier that does not hide the quantified variables?
				TreeNode[] children = treeNode.heirs();
				for (int i = 1; i < children.length - 2; i = i + 2) {
					// System.out.println("N_UnboundQuant: "+children[i].getImage());
				}
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

		for (int i = 0; i < treeNode.heirs().length; i++) {
			searchVarInSyntaxTree(treeNode.heirs()[i]);
		}
	}

	public static String allMessagesToString(String[] allMessages) {
		return Translator.allMessagesToString(allMessages);
	}
}
