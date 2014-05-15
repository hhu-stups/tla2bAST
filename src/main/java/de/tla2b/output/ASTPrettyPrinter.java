package de.tla2b.output;

import java.util.ArrayList;
import java.util.Hashtable;
import java.util.Iterator;
import java.util.List;

import de.be4.classicalb.core.parser.analysis.ExtendedDFAdapter;
import de.be4.classicalb.core.parser.node.AAbstractMachineParseUnit;
import de.be4.classicalb.core.parser.node.AAnySubstitution;
import de.be4.classicalb.core.parser.node.ABecomesSuchSubstitution;
import de.be4.classicalb.core.parser.node.AConstantsMachineClause;
import de.be4.classicalb.core.parser.node.ADefinitionExpression;
import de.be4.classicalb.core.parser.node.ADefinitionPredicate;
import de.be4.classicalb.core.parser.node.AExpressionDefinitionDefinition;
import de.be4.classicalb.core.parser.node.AIdentifierExpression;
import de.be4.classicalb.core.parser.node.ALambdaExpression;
import de.be4.classicalb.core.parser.node.AOperation;
import de.be4.classicalb.core.parser.node.AOperationsMachineClause;
import de.be4.classicalb.core.parser.node.APredicateDefinitionDefinition;
import de.be4.classicalb.core.parser.node.ASelectSubstitution;
import de.be4.classicalb.core.parser.node.Node;
import de.be4.classicalb.core.parser.node.PExpression;
import de.be4.classicalb.core.parser.node.PMachineClause;
import de.be4.classicalb.core.parser.node.POperation;
import de.be4.classicalb.core.parser.node.PSubstitution;
import de.be4.classicalb.core.parser.node.Start;
import de.be4.classicalb.core.parser.node.TIdentifierLiteral;
import de.be4.classicalb.core.parser.node.Token;

public class ASTPrettyPrinter extends ExtendedDFAdapter {
	private final StringBuilder builder = new StringBuilder();
	private final StringBuilder sb = new StringBuilder();
	private Renamer renamer;

	private static final int no = 0;
	private static final int left = 1;
	private static final int right = 2;
	public static final int max = 500;

	private final static Hashtable<String, NodeInfo> infoTable = new Hashtable<String, NodeInfo>();

	public ASTPrettyPrinter(Renamer renamer) {
		this.renamer = renamer;
	}

	public ASTPrettyPrinter() {
	}

	private static void putInfixOperator(String nodeName, String symbol,
			int precedence, int a) {
		infoTable.put(nodeName, new NodeInfo(null, null, null, null, " "
				+ symbol + " ", null, precedence, a));
	}

	private static void putPrefixOperator(String nodeName, String symbol,
			int precedence, int a) {
		infoTable.put(nodeName, new NodeInfo(symbol, null, null, null, null,
				null, precedence, a));
	}

	private static void putInfixOperatorWithoutSpaces(String nodeName,
			String symbol, int precedence, int a) {
		infoTable.put(nodeName, new NodeInfo(null, null, null, null, symbol,
				null, precedence, a));
	}

	private static void putPreEnd(String nodeName, String pre, String end) {
		infoTable.put(nodeName, new NodeInfo(pre, null, null, null, null, end,
				null, null));
	}

	private static void putClause(String nodeName, String pre, String end) {
		infoTable.put(nodeName, new NodeInfo(pre + "\n", null, null, null,
				null, end, null, null));
	}

	private static void putSymbol(String nodeName, String symbol) {
		infoTable.put(nodeName, new NodeInfo(symbol, null, null, null, null,
				null, null, null));
	}

	private static void put(String nodeName, String pre, String beginList,
			String betweenListElements, String endList, String betweenChildren,
			String end) {
		infoTable
				.put(nodeName, new NodeInfo(pre, beginList,
						betweenListElements, endList, betweenChildren, end,
						null, null));
	}

	private static void putDeclarationClause(String nodeName,
			String clauseName, String betweenListElements) {
		NodeInfo info = new NodeInfo();
		info.setPre(clauseName + " ");
		info.setBetweenListElements(betweenListElements + " ");
		info.setEnd("\n");
		infoTable.put(nodeName, info);
	}

	static {

		putDeclarationClause("ASetsMachineClause", "SETS", ";");
		putDeclarationClause("AAbstractConstantsMachineClause",
				"ABSTRACT_CONSTANTS", ",");
		putDeclarationClause("AConstantsMachineClause",
				"CONSTANTS", ",");
		putDeclarationClause("AVariablesMachineClause", "VARIABLES", ",");

		put("AEnumeratedSetSet", null, null, ", ", null, " = {", "}");
		// AEnumeratedSetSet e;e.g
		putClause("ADefinitionsMachineClause", "DEFINITIONS", "");
		putClause("APropertiesMachineClause", "PROPERTIES", "\n");
		putClause("AInvariantMachineClause", "INVARIANT", "\n");
		putClause("AInitialisationMachineClause", "INITIALISATION", "\n");
		putClause("AOperationsMachineClause", "OPERATIONS", "\n");

		// infix operators
		putInfixOperator("AImplicationPredicate", "=>", 30, left);
		putInfixOperator("AEquivalencePredicate", "<=>", 30, left);

		putInfixOperator("AConjunctPredicate", "&", 40, left);
		putInfixOperator("ADisjunctPredicate", "or", 40, left);

		putInfixOperator("ALessPredicate", "<", 50, left);
		putInfixOperator("AGreaterPredicate", ">", 50, left);
		putInfixOperator("ALessEqualPredicate", "<=", 50, left);
		putInfixOperator("AGreaterEqualPredicate", ">=", 50, left);

		putInfixOperator("AEqualPredicate", "=", 50, left);
		putInfixOperator("ANotEqualPredicate", "/=", 50, left);

		putInfixOperator("AMemberPredicate", ":", 60, left);
		putInfixOperator("ANotMemberPredicate", "/:", 60, left);

		putInfixOperator("ASubsetPredicate", "<:", 60, left); // <: subseteq

		putInfixOperator("APartialFunctionExpression", "+->", 125, left);
		putInfixOperator("ATotalFunctionExpression", "-->", 125, left);

		putInfixOperator("AOverwriteExpression", "<+", 160, left);
		putInfixOperator("AUnionExpression", "\\/", 160, left);
		putInfixOperator("AIntersectionExpression", "/\\", 160, left);

		putInfixOperator("AInsertTailExpression", "<-", 160, left);
		putInfixOperator("AConcatExpression", "^", 160, left);

		putInfixOperator("ARestrictFrontExpression", "/|\\", 160, left);
		putInfixOperator("ARestrictTailExpression", "\\|/", 160, left);

		putInfixOperator("AIntervalExpression", "..", 170, left);

		putInfixOperator("AAddExpression", "+", 180, left);
		putInfixOperator("AMinusOrSetSubtractExpression", "-", 180, left);
		
		putInfixOperator("ACartesianProductExpression", "*", 190, left);
		putInfixOperator("AMultOrCartExpression", "*", 190, left);
		putInfixOperator("ADivExpression", "/", 190, left);

		putInfixOperator("APowerOfExpression", "**", 200, right);

		putPrefixOperator("AUnaryMinusExpression", "-", 210, no);

		putInfixOperatorWithoutSpaces("ARecordFieldExpression", "'", 250, left);

		infoTable.put("AFunctionExpression", new NodeInfo(null, "(", ", ", ")",
				null, null, 300, no));

		// single symbols
		putSymbol("AIntegerSetExpression", "INTEGER");
		putSymbol("AIntSetExpression", "INT");
		putSymbol("ANaturalSetExpression", "NATURAL");
		putSymbol("ANatural1SetExpression", "NATURAL1");
		putSymbol("ANatSetExpression", "NAT");
		putSymbol("ANat1SetExpression", "NAT1");
		putSymbol("ABooleanTrueExpression", "TRUE");
		putSymbol("ABooleanFalseExpression", "FALSE");
		putSymbol("AEmptySetExpression", "{}");
		putSymbol("ABoolSetExpression", "BOOL");
		putSymbol("AStringSetExpression", "STRING");
		putSymbol("ASkipSubstitution", "skip");

		putPreEnd("APowSubsetExpression", "POW(", ")");
		putPreEnd("AConvertBoolExpression", "bool(", ")");
		putPreEnd("ADomainExpression", "dom(", ")");
		putPreEnd("ANegationPredicate", "not(", ")");
		putPreEnd("ASizeExpression", "size(", ")");
		putPreEnd("ASeqExpression", "seq(", ")");
		putPreEnd("ASeq1Expression", "seq1(", ")");
		putPreEnd("AGeneralUnionExpression", "union(", ")");
		putPreEnd("AStringExpression", "\"", "\"");
		putPreEnd("AFinSubsetExpression", "FIN(", ")");
		putPreEnd("ACardExpression", "card(", ")");
		putPreEnd("AFirstExpression", "first(", ")");
		putPreEnd("ATailExpression", "tail(", ")");
		putPreEnd("AEmptySequenceExpression", "[", "]");

		putPreEnd("ABlockSubstitution", "BEGIN ", " END");
		// TODO other substitutions

		put("ASetExtensionExpression", null, "{", ", ", "}", null, null);
		put("AStructExpression", "struct", "(", ", ", ")", null, null);
		put("ARecExpression", "rec", "(", ", ", ")", null, null);
		put("ARecEntry", null, null, null, null, ":", null);

		put("ACoupleExpression", null, "(", ",", ")", null, null);
		put("ASequenceExtensionExpression", null, "[", ",", "]", null, null);

		put("AForallPredicate", "!", "(", ",", ")", ".(", ")");
		put("AExistsPredicate", "#", "(", ",", ")", ".(", ")");

		put("AAssignSubstitution", null, null, ",", null, " := ", null);

		put("AComprehensionSetExpression", "{", "", ",", "", " | ", "}");

	}

	@Override
	public void caseAIdentifierExpression(final AIdentifierExpression node) {
		if (renamer != null) {
			sb.append(renamer.getNewName(node));
		} else

		{
			final List<TIdentifierLiteral> copy = new ArrayList<TIdentifierLiteral>(
					node.getIdentifier());
			for (final Iterator<TIdentifierLiteral> iterator = copy.iterator(); iterator
					.hasNext();) {
				final TIdentifierLiteral e = iterator.next();
				e.apply(this);
			}
		}
	}

	@Override
	public String toString() {
		return builder.toString();
	}

	private NodeInfo getInfo(final Node node) {
		final String nodeName = node.getClass().getSimpleName();
		if (infoTable.containsKey(nodeName)) {
			return infoTable.get(nodeName);
		} else {
			return new NodeInfo();
		}
	}

	@Override
	public void defaultIn(final Node node) {
		super.defaultIn(node);
		if (makeBrackets(node)) {
			sb.append("(");
		}
		sb.append(getInfo(node).pre);
		builder.append(node.getClass().getSimpleName());
		builder.append("(");
	}

	private boolean makeBrackets(Node node) {
		NodeInfo infoNode = getInfo(node);
		Node parent = node.parent();
		if (parent == null) {
			return false;
		}
		NodeInfo infoParent = getInfo(parent);
		if (infoNode.precedence == max || infoParent.precedence == max)
			return false;

		if (infoParent.precedence >= infoNode.precedence) {
			return true;
		}

		return false;
	}

	@Override
	public void caseTIdentifierLiteral(TIdentifierLiteral node) {
		if (renamer != null) {
			sb.append(renamer.getNewName(node));
		} else {
			sb.append(node.getText());
		}

	}

	@Override
	public void defaultCase(final Node node) {
		super.defaultCase(node);
		if (node instanceof Token) {
			builder.append(((Token) node).getText());

			sb.append(((Token) node).getText());
		} else {
			builder.append(node.toString());
			sb.append(node.toString());
		}

	}

	@Override
	public void defaultOut(final Node node) {
		super.defaultOut(node);
		builder.append(")");
		sb.append(getInfo(node).end);
		if (makeBrackets(node)) {
			sb.append(")");
		}
	}

	@Override
	public void beginList(final Node parent) {
		builder.append('[');
		sb.append(getInfo(parent).beginList);
	}

	@Override
	public void betweenListElements(final Node parent) {
		builder.append(',');
		sb.append(getInfo(parent).betweenListElements);
	}

	@Override
	public void endList(final Node parent) {
		builder.append(']');
		sb.append(getInfo(parent).endList);
	}

	@Override
	public void betweenChildren(final Node parent) {
		builder.append(',');
		sb.append(getInfo(parent).betweenChildren);
	}

	@Override
	public void caseStart(final Start node) {
		inStart(node);
		node.getPParseUnit().apply(this);
		node.getEOF().apply(this);
		outStart(node);
	}

	public static String getIdentifierAsString(
			final List<TIdentifierLiteral> idElements) {
		final String string;
		if (idElements.size() == 1) {
			// faster version for the simple case
			string = idElements.get(0).getText();
		} else {
			final StringBuilder idName = new StringBuilder();

			boolean first = true;
			for (final TIdentifierLiteral e : idElements) {
				if (first) {
					first = false;
				} else {
					idName.append('.');
				}
				idName.append(e.getText());
			}
			string = idName.toString();
		}
		return string.trim();
	}

	public String getResultString() {
		return sb.toString();
	}

	public StringBuilder getResultAsStringbuilder() {
		return sb;
	}

	@Override
	public void caseAAbstractMachineParseUnit(AAbstractMachineParseUnit node) {
		sb.append("MACHINE ");
		if (node.getVariant() != null) {
			node.getVariant().apply(this);
		}
		if (node.getHeader() != null) {
			node.getHeader().apply(this);
		}
		sb.append("\n");
		List<PMachineClause> copy = new ArrayList<PMachineClause>(
				node.getMachineClauses());
		for (PMachineClause e : copy) {
			e.apply(this);
		}
		sb.append("END");
	}

	@Override
	public void caseAOperationsMachineClause(final AOperationsMachineClause node) {
		sb.append("OPERATIONS\n");
		final List<POperation> copy = new ArrayList<POperation>(
				node.getOperations());
		for (final Iterator<POperation> iterator = copy.iterator(); iterator
				.hasNext();) {
			final POperation e = iterator.next();
			e.apply(this);
			if (iterator.hasNext()) {
				sb.append(";\n");
			}
			sb.append("\n");
		}
	}

	@Override
	public void caseAOperation(AOperation node) {
		sb.append(" ");
		List<PExpression> output = new ArrayList<PExpression>(
				node.getReturnValues());
		if (output.size() > 0) {
			for (final Iterator<PExpression> iterator = output.iterator(); iterator
					.hasNext();) {
				final PExpression e = iterator.next();
				e.apply(this);
				if (iterator.hasNext()) {
					sb.append(", ");
				}
			}
			sb.append("<-- ");
		}
		List<TIdentifierLiteral> copy = new ArrayList<TIdentifierLiteral>(
				node.getOpName());
		for (TIdentifierLiteral e : copy) {
			e.apply(this);
		}
		List<PExpression> parameters = new ArrayList<PExpression>(
				node.getParameters());
		if (parameters.size() > 0) {
			sb.append("(");
			for (final Iterator<PExpression> iterator = parameters.iterator(); iterator
					.hasNext();) {
				final PExpression e = iterator.next();
				e.apply(this);

				if (iterator.hasNext()) {
					sb.append(", ");
				}
			}
			sb.append(")");
		}
		sb.append(" = ");
		node.getOperationBody().apply(this);
	}

	@Override
	public void caseABecomesSuchSubstitution(final ABecomesSuchSubstitution node) {
		final List<PExpression> copy = new ArrayList<PExpression>(
				node.getIdentifiers());
		for (final Iterator<PExpression> iterator = copy.iterator(); iterator
				.hasNext();) {
			final PExpression e = iterator.next();
			e.apply(this);
			if (iterator.hasNext()) {
				sb.append(", ");
			}
		}
		sb.append(":(");
		node.getPredicate().apply(this);
		sb.append(")");
	}

	public void caseAAnySubstitution(final AAnySubstitution node) {
		sb.append("ANY ");
		final List<PExpression> copy = new ArrayList<PExpression>(
				node.getIdentifiers());
		beginList(node);
		for (final Iterator<PExpression> iterator = copy.iterator(); iterator
				.hasNext();) {
			final PExpression e = iterator.next();
			e.apply(this);
			if (iterator.hasNext()) {
				sb.append(", ");
			}
		}
		endList(node);
		sb.append(" WHERE ");
		node.getWhere().apply(this);
		sb.append(" THEN ");
		node.getThen().apply(this);
		sb.append(" END");
	}

	@Override
	public void caseASelectSubstitution(final ASelectSubstitution node) {
		sb.append("SELECT ");
		node.getCondition().apply(this);
		sb.append(" THEN ");
		betweenChildren(node);
		node.getThen().apply(this);
		{
			final List<PSubstitution> copy = new ArrayList<PSubstitution>(
					node.getWhenSubstitutions());
			beginList(node);
			for (final Iterator<PSubstitution> iterator = copy.iterator(); iterator
					.hasNext();) {
				final PSubstitution e = iterator.next();
				e.apply(this);

				if (iterator.hasNext()) {
					betweenListElements(node);
				}
			}
			endList(node);
		}
		betweenChildren(node);
		if (node.getElse() != null) {
			node.getElse().apply(this);
		}
		sb.append(" END");
	}

	@Override
	public void caseAPredicateDefinitionDefinition(
			APredicateDefinitionDefinition node) {
		sb.append(" ");
		node.getName().apply(this);
		List<PExpression> copy = new ArrayList<PExpression>(
				node.getParameters());
		if (copy.size() > 0) {
			sb.append("(");
			for (final Iterator<PExpression> iterator = copy.iterator(); iterator
					.hasNext();) {
				final PExpression e = iterator.next();
				e.apply(this);
				if (iterator.hasNext()) {
					sb.append(", ");
				}
			}
			sb.append(")");
		}
		sb.append(" == ");
		node.getRhs().apply(this);
		sb.append(";\n");
	}

	@Override
	public void caseADefinitionPredicate(final ADefinitionPredicate node) {
		node.getDefLiteral().apply(this);
		final List<PExpression> copy = new ArrayList<PExpression>(
				node.getParameters());
		if (copy.size() > 0) {
			sb.append("(");
			for (final Iterator<PExpression> iterator = copy.iterator(); iterator
					.hasNext();) {
				final PExpression e = iterator.next();
				e.apply(this);
				if (iterator.hasNext()) {
					sb.append(", ");
				}
			}
			sb.append(")");
		}
	}

	@Override
	public void caseAExpressionDefinitionDefinition(
			final AExpressionDefinitionDefinition node) {
		sb.append(" ");
		node.getName().apply(this);
		List<PExpression> copy = new ArrayList<PExpression>(
				node.getParameters());
		if (copy.size() > 0) {
			sb.append("(");
			for (final Iterator<PExpression> iterator = copy.iterator(); iterator
					.hasNext();) {
				final PExpression e = iterator.next();
				e.apply(this);
				if (iterator.hasNext()) {
					sb.append(", ");
				}
			}
			sb.append(")");
		}
		sb.append(" == ");
		node.getRhs().apply(this);
		sb.append(";\n");
	}

	@Override
	public void caseADefinitionExpression(final ADefinitionExpression node) {
		node.getDefLiteral().apply(this);
		final List<PExpression> copy = new ArrayList<PExpression>(
				node.getParameters());
		if (copy.size() > 0) {
			sb.append("(");
			for (final Iterator<PExpression> iterator = copy.iterator(); iterator
					.hasNext();) {
				final PExpression e = iterator.next();
				e.apply(this);
				if (iterator.hasNext()) {
					sb.append(", ");
				}
			}
			sb.append(")");
		}
	}

	@Override
	public void caseALambdaExpression(final ALambdaExpression node) {
		final List<PExpression> copy = new ArrayList<PExpression>(
				node.getIdentifiers());
		sb.append("%(");
		for (final Iterator<PExpression> iterator = copy.iterator(); iterator
				.hasNext();) {
			final PExpression e = iterator.next();
			e.apply(this);

			if (iterator.hasNext()) {
				sb.append(", ");
			}
		}
		sb.append(").(");
		node.getPredicate().apply(this);
		sb.append(" | ");
		node.getExpression().apply(this);
		sb.append(")");
	}

}

class NodeInfo {
	String pre = "";
	String beginList = "";
	String betweenListElements = "";
	String endList = "";
	String betweenChildren = "";
	String end = "";
	Integer precedence = ASTPrettyPrinter.max;
	Integer associative = 0;

	public String getPre() {
		return pre;
	}

	public void setPre(String pre) {
		this.pre = pre;
	}

	public String getBeginList() {
		return beginList;
	}

	public void setBeginList(String beginList) {
		this.beginList = beginList;
	}

	public String getBetweenListElements() {
		return betweenListElements;
	}

	public void setBetweenListElements(String betweenListElements) {
		this.betweenListElements = betweenListElements;
	}

	public String getEndList() {
		return endList;
	}

	public void setEndList(String endList) {
		this.endList = endList;
	}

	public String getBetweenChildren() {
		return betweenChildren;
	}

	public void setBetweenChildren(String betweenChildren) {
		this.betweenChildren = betweenChildren;
	}

	public String getEnd() {
		return end;
	}

	public void setEnd(String end) {
		this.end = end;
	}

	public Integer getPrecedence() {
		return precedence;
	}

	public void setPrecedence(Integer precedence) {
		this.precedence = precedence;
	}

	public Integer getAssociative() {
		return associative;
	}

	public void setAssociative(Integer associative) {
		this.associative = associative;
	}

	public NodeInfo() {

	}

	public NodeInfo(String pre, String beginList, String betweenListElements,
			String endList, String betweenChildren, String end,
			Integer precedence, Integer associative) {
		if (pre != null)
			this.pre = pre;
		if (beginList != null)
			this.beginList = beginList;
		if (betweenListElements != null)
			this.betweenListElements = betweenListElements;
		if (endList != null)
			this.endList = endList;
		if (betweenChildren != null)
			this.betweenChildren = betweenChildren;
		if (end != null)
			this.end = end;
		if (precedence != null)
			this.precedence = precedence;
		if (associative != null)
			this.associative = associative;
	}

}