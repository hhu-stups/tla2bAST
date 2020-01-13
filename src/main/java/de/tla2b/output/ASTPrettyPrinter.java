package de.tla2b.output;

import java.util.ArrayList;
import java.util.Hashtable;
import java.util.Iterator;
import java.util.List;

import de.be4.classicalb.core.parser.node.*;
import de.tla2b.util.ExtendedDFAdapter;

public class ASTPrettyPrinter extends ExtendedDFAdapter {
	private final StringBuilder sb = new StringBuilder();
	private Renamer renamer;
	private final Indentation indentation;

	private static final int no = 0;
	private static final int left = 1;
	private static final int right = 2;
	private static final String NEWLINE = "\n";
	public final static String SPACE = " ";
	protected static final int MAX_PRECEDENCE = 500;

	private final static Hashtable<String, PrettyPrintNode> ppNodeTable = new Hashtable<String, PrettyPrintNode>();

	public ASTPrettyPrinter(Start start, Renamer renamer) {
		this.renamer = renamer;
		this.indentation = new Indentation(start);
	}

	public ASTPrettyPrinter(Start start) {
		this.indentation = new Indentation(start);
	}

	static {
		putDeclarationClause(ASetsMachineClause.class, "SETS", ";");
		putDeclarationClause(AAbstractConstantsMachineClause.class,
				"ABSTRACT_CONSTANTS", ",");
		putDeclarationClause(AConstantsMachineClause.class, "CONSTANTS", ",");
		putDeclarationClause(AVariablesMachineClause.class, "VARIABLES", ",");
		put(AEnumeratedSetSet.class,
				new PrettyPrintNode().setBetweenChildren(" = {")
						.setBetweenListElements(", ").setEnd("}"));

		put(ADefinitionsMachineClause.class,
				new PrettyPrintNode().setBegin("DEFINITIONS\n")
						.setBetweenListElements(NEWLINE).setEnd(NEWLINE));
		putClause(APropertiesMachineClause.class, "PROPERTIES", "\n");
		put(AAssertionsMachineClause.class,
				new PrettyPrintNode().setBegin("ASSERTIONS\n")
						.setBetweenListElements(";" + NEWLINE).setEnd(NEWLINE));
		putClause(AInvariantMachineClause.class, "INVARIANT", "\n");
		putClause(AInitialisationMachineClause.class, "INITIALISATION", "\n");
		putClause(AOperationsMachineClause.class, "OPERATIONS", "\n");

		// infix operators
		putInfixOperator(AImplicationPredicate.class, "=>", 30, left);
		putInfixOperator(AEquivalencePredicate.class, "<=>", 30, left);
		putInfixOperator(AConjunctPredicate.class, "&", 40, left);
		putInfixOperator(ADisjunctPredicate.class, "or", 40, left);
		putInfixOperator(ALessPredicate.class, "<", 50, left);
		putInfixOperator(AGreaterPredicate.class, ">", 50, left);
		putInfixOperator(ALessEqualPredicate.class, "<=", 50, left);
		putInfixOperator(AGreaterEqualPredicate.class, ">=", 50, left);
		putInfixOperator(AEqualPredicate.class, "=", 50, left);
		putInfixOperator(ANotEqualPredicate.class, "/=", 50, left);
		putInfixOperator(AMemberPredicate.class, ":", 60, left);
		putInfixOperator(ANotMemberPredicate.class, "/:", 60, left);
		putInfixOperator(ASubsetPredicate.class, "<:", 60, left); // <: subseteq
		putInfixOperator(APartialFunctionExpression.class, "+->", 125, left);
		putInfixOperator(ATotalFunctionExpression.class, "-->", 125, left);
		putInfixOperator(AOverwriteExpression.class, "<+", 160, left);
		putInfixOperator(AUnionExpression.class, "\\/", 160, left);
		putInfixOperator(AIntersectionExpression.class, "/\\", 160, left);
		putInfixOperator(AInsertTailExpression.class, "<-", 160, left);
		putInfixOperator(AConcatExpression.class, "^", 160, left);
		putInfixOperator(ARestrictFrontExpression.class, "/|\\", 160, left);
		putInfixOperator(ARestrictTailExpression.class, "\\|/", 160, left);
		putInfixOperator(AIntervalExpression.class, "..", 170, left);
		putInfixOperator(AAddExpression.class, "+", 180, left);
		putInfixOperator(AMinusOrSetSubtractExpression.class, "-", 180, left);
		putInfixOperator(ACartesianProductExpression.class, "*", 190, left);
		putInfixOperator(AMultOrCartExpression.class, "*", 190, left);
		putInfixOperator(ADivExpression.class, "/", 190, left);
		putInfixOperator(APowerOfExpression.class, "**", 200, right);

		putPrefixOperator(AUnaryMinusExpression.class, "-", 210, no);

		putInfixOperatorWithoutSpaces(ARecordFieldExpression.class, "'", 250,
				left);

		put(AFunctionExpression.class, new PrettyPrintNode().setBeginList("(")
				.setBetweenListElements(",").setEndList(")").setPrecedence(300)
				.setAssociative(no));

		// single symbols
		putSymbol(AIntegerSetExpression.class, "INTEGER");
		putSymbol(AIntSetExpression.class, "INT");
		putSymbol(ANaturalSetExpression.class, "NATURAL");
		putSymbol(ANatural1SetExpression.class, "NATURAL1");
		putSymbol(ANatSetExpression.class, "NAT");
		putSymbol(ANat1SetExpression.class, "NAT1");
		putSymbol(ABooleanTrueExpression.class, "TRUE");
		putSymbol(ABooleanFalseExpression.class, "FALSE");
		putSymbol(AEmptySetExpression.class, "{}");
		putSymbol(ABoolSetExpression.class, "BOOL");
		putSymbol(AStringSetExpression.class, "STRING");
		putSymbol(ASkipSubstitution.class, "skip");

		putOperator(APowSubsetExpression.class, "POW");
		putOperator(AConvertBoolExpression.class, "bool");
		putOperator(ADomainExpression.class, "dom");
		putOperator(ANegationPredicate.class, "not");
		putOperator(ASizeExpression.class, "size");
		putOperator(ASeqExpression.class, "seq");
		putOperator(ASeq1Expression.class, "seq1");
		putOperator(AGeneralUnionExpression.class, "union");
		putOperator(AFinSubsetExpression.class, "FIN");
		putOperator(ACardExpression.class, "card");
		putOperator(AFirstExpression.class, "first");
		putOperator(ATailExpression.class, "tail");
		putOperator(AFirstProjectionExpression.class, "prj1");
		putOperator(ASecondProjectionExpression.class, "prj2");

		putBeginEnd(AStringExpression.class, "\"", "\"");
		putBeginEnd(AEmptySequenceExpression.class, "[", "]");
		putBeginEnd(ABlockSubstitution.class, "BEGIN ", " END");
		putBeginEnd(ASequenceExtensionExpression.class, "[ ", "]");

		// TODO other substitutions

		put(ASetExtensionExpression.class,
				new PrettyPrintNode().setBeginList("{")
						.setBetweenListElements(",").setEndList("}"));

		put(AStructExpression.class, new PrettyPrintNode().setBegin("struct")
				.setBeginList("(").setBetweenListElements(",").setEndList(")"));
		put(ARecExpression.class, new PrettyPrintNode().setBegin("rec")
				.setBeginList("(").setBetweenListElements(",").setEndList(")"));
		put(ARecEntry.class, new PrettyPrintNode().setBetweenChildren(":"));

		put(ACoupleExpression.class, new PrettyPrintNode().setBeginList("(")
				.setBetweenListElements("|->").setEndList(")"));
		put(ASequenceExtensionExpression.class, new PrettyPrintNode()
				.setBeginList("[").setBetweenListElements(",").setEndList("]"));

		put(AForallPredicate.class, new PrettyPrintNode().setBegin("!")
				.setBeginList("(").setBetweenListElements(",").setEndList(")")
				.setBetweenChildren(".(").setEnd(")"));
		put(AExistsPredicate.class, new PrettyPrintNode().setBegin("#")
				.setBeginList("(").setBetweenListElements(",").setEndList(")")
				.setBetweenChildren(".(").setEnd(")"));

		put(AAssignSubstitution.class, new PrettyPrintNode()
				.setBetweenListElements(",").setBetweenChildren(" := "));

		put(AComprehensionSetExpression.class,
				new PrettyPrintNode().setBegin("{").setBetweenListElements(",")
						.setBetweenChildren("|").setEnd("}"));
		
		// MyMap = Collections.unmodifiableMap(tmpMap);
	}

	private static void putInfixOperator(Class<?> clazz, String symbol,
			int precedence, int a) {
		ppNodeTable.put(clazz.getSimpleName(),
				new PrettyPrintNode()
						.setBetweenChildren(SPACE + symbol + SPACE)
						.setPrecedence(precedence).setAssociative(a));
	}

	private static void putPrefixOperator(Class<?> clazz, String symbol,
			int precedence, int a) {
		ppNodeTable.put(clazz.getSimpleName(), new PrettyPrintNode(symbol,
				null, null, null, null, null, precedence, a));
	}

	private static void putInfixOperatorWithoutSpaces(Class<?> clazz,
			String symbol, int precedence, int a) {
		ppNodeTable.put(clazz.getSimpleName(), new PrettyPrintNode(null, null,
				null, null, symbol, null, precedence, a));
	}

	private static void putBeginEnd(Class<?> clazz, String begin, String end) {
		ppNodeTable.put(clazz.getSimpleName(),
				new PrettyPrintNode().setBegin(begin).setBetweenChildren(",")
						.setEnd(end));
	}

	private static void putOperator(Class<?> clazz, String pre) {
		ppNodeTable.put(clazz.getSimpleName(), new PrettyPrintNode(pre + "(",
				null, null, null, ",", ")", null, null));
	}

	private static void putSymbol(Class<?> clazz, String symbol) {
		ppNodeTable.put(clazz.getSimpleName(), new PrettyPrintNode(symbol,
				null, null, null, null, null, null, null));
	}

	private static void putClause(Class<?> clazz, String pre, String end) {
		ppNodeTable.put(clazz.getSimpleName(), new PrettyPrintNode(pre + "\n",
				null, null, null, null, end, null, null));
	}

	private static void putDeclarationClause(Class<?> clazz, String clauseName,
			String betweenListElements) {
		PrettyPrintNode ppNode = new PrettyPrintNode()
				.setBegin(clauseName + NEWLINE)
				.setBetweenListElements(betweenListElements + NEWLINE)
				.setEnd(NEWLINE);
		ppNodeTable.put(clazz.getSimpleName(), ppNode);

	}

	private static void put(Class<?> clazz, PrettyPrintNode nodeInfo) {
		String className = clazz.getSimpleName();
		ppNodeTable.put(className, nodeInfo);
	}

	@Override
	public void caseAIdentifierExpression(final AIdentifierExpression node) {
		inAIdentifierExpression(node);
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
		outAIdentifierExpression(node);
	}

	@Override
	public String toString() {
		return sb.toString();
	}

	private PrettyPrintNode getPrettyPrintNode(final Node node) {
		final String nodeName = node.getClass().getSimpleName();
		if (ppNodeTable.containsKey(nodeName)) {
			return ppNodeTable.get(nodeName);
		} else {
			return new PrettyPrintNode();
		}
	}

	@Override
	public void defaultIn(final Node node) {
		if (indentation.isIndentedNode(node)) {
			sb.append(indentation.getIndent(node));
		}
		if (needsBrackets(node)) {
			sb.append("(");
		}
		sb.append(getPrettyPrintNode(node).getBegin());
	}

	@Override
	public void defaultCase(final Node node) {
		super.defaultCase(node);
		if (node instanceof Token) {
			sb.append(((Token) node).getText());
		} else {
			sb.append(node.toString());
		}

	}

	@Override
	public void defaultOut(final Node node) {
		sb.append(getPrettyPrintNode(node).getEnd());
		if (needsBrackets(node)) {
			sb.append(")");
		}
		if (indentation.isNewline(node)) {
			sb.append(NEWLINE);
		}
	}

	private boolean needsBrackets(Node node) {
		PrettyPrintNode ppNodeNode = getPrettyPrintNode(node);
		Node parent = node.parent();
		if (parent == null) {
			return false;
		}
		PrettyPrintNode ppNodeParrent = getPrettyPrintNode(parent);
		if (ppNodeNode.getPrecedence() == MAX_PRECEDENCE
				|| ppNodeParrent.getPrecedence() == MAX_PRECEDENCE)
			return false;

		if (ppNodeParrent.getPrecedence() > ppNodeNode.getPrecedence()) {
			return true;
		}

		if (ppNodeParrent.getPrecedence() == ppNodeNode.getPrecedence()) {
			// in some cases, this produces a different AST
			if (node.getClass() == parent.getClass()) {
				return false;
			} else {
				return true;
			}

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

	public void beginList(final Node parent) {
		sb.append(getPrettyPrintNode(parent).getBeginList());
	}

	@Override
	public void betweenListElements(final Node node) {
		sb.append(getPrettyPrintNode(node).getBetweenListElements());
	}

	@Override
	public void endList(final Node parent) {
		sb.append(getPrettyPrintNode(parent).getEndList());
	}

	@Override
	public void betweenChildren(final Node node) {
		if (indentation.printNewLineInTheMiddle(node)) {
			sb.append(NEWLINE);
			sb.append(indentation.getIndent(node));
			sb.append(getPrettyPrintNode(node).getBetweenChildren().trim());
			sb.append(SPACE);
		} else {
			sb.append(getPrettyPrintNode(node).getBetweenChildren());
		}
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
	public void caseAQuantifiedUnionExpression(
			final AQuantifiedUnionExpression node) {
		inAQuantifiedUnionExpression(node);
		sb.append("UNION(");
		{
			final List<PExpression> copy = new ArrayList<PExpression>(
					node.getIdentifiers());
			beginList(node);
			for (final Iterator<PExpression> iterator = copy.iterator(); iterator
					.hasNext();) {
				final PExpression e = iterator.next();
				e.apply(this);

				if (iterator.hasNext()) {
					betweenListElements(node);
					sb.append(",");
				}
			}
			endList(node);
		}
		sb.append(").(");
		betweenChildren(node);
		if (node.getPredicates() != null) {
			node.getPredicates().apply(this);
		}
		betweenChildren(node);
		sb.append(" | ");
		if (node.getExpression() != null) {
			node.getExpression().apply(this);
		}
		sb.append(")");
		outAQuantifiedUnionExpression(node);
	}

	@Override
	public void caseALabelPredicate(ALabelPredicate node) {
		inALabelPredicate(node);
		sb.append("/*@label ");
		if (node.getName() != null) {
			node.getName().apply(this);
		}
		sb.append(" */ ");

		if (node.getPredicate() != null) {
			node.getPredicate().apply(this);
		}
		outALabelPredicate(node);
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

	@Override
	public void caseAIfThenElseExpression(AIfThenElseExpression node) {
		sb.append("(%t_.( t_ = 0 & ");
		node.getCondition().apply(this);
		sb.append(" | ");
		node.getThen().apply(this);
		sb.append(")\\/%t_.( t_ = 0 & not(");
		node.getCondition().apply(this);
		sb.append(") | ");
		node.getElse().apply(this);
		sb.append(" ))(0)");
	}

	@Override
	public void caseAFlooredDivExpression(AFlooredDivExpression node) {
		node.getLeft().apply(this);
		sb.append(" \\div ");
		node.getRight().apply(this);
	}

	@Override
	public void caseAGeneralSumExpression(AGeneralSumExpression node) {
		List<PExpression> copy = new ArrayList<PExpression>(
				node.getIdentifiers());
		sb.append("SIGMA(");
		for (final Iterator<PExpression> iterator = copy.iterator(); iterator
				.hasNext();) {
			final PExpression e = iterator.next();
			e.apply(this);

			if (iterator.hasNext()) {
				sb.append(", ");
			}
		}
		sb.append(").(");
		node.getPredicates().apply(this);
		sb.append("|");
		node.getExpression().apply(this);
		sb.append(")");
	}

}

class PrettyPrintNode {
	private String begin = "";
	private String beginList = "";
	private String betweenListElements = "";
	private String endList = "";
	private String betweenChildren = "";
	private String end = "";
	private Integer precedence = ASTPrettyPrinter.MAX_PRECEDENCE;
	private Integer associative = 0;

	public String getBegin() {
		return begin;
	}

	public PrettyPrintNode setBegin(String begin) {
		this.begin = begin;
		return this;
	}

	public String getBeginList() {
		return beginList;
	}

	public PrettyPrintNode setBeginList(String beginList) {
		this.beginList = beginList;
		return this;
	}

	public String getBetweenListElements() {
		return betweenListElements;
	}

	public PrettyPrintNode setBetweenListElements(String betweenListElements) {
		this.betweenListElements = betweenListElements;
		return this;
	}

	public String getEndList() {
		return endList;
	}

	public PrettyPrintNode setEndList(String endList) {
		this.endList = endList;
		return this;
	}

	public String getBetweenChildren() {
		return betweenChildren;
	}

	public PrettyPrintNode setBetweenChildren(String betweenChildren) {
		this.betweenChildren = betweenChildren;
		return this;
	}

	public String getEnd() {
		return end;
	}

	public PrettyPrintNode setEnd(String end) {
		this.end = end;
		return this;
	}

	public Integer getPrecedence() {
		return precedence;
	}

	public PrettyPrintNode setPrecedence(Integer precedence) {
		this.precedence = precedence;
		return this;
	}

	public Integer getAssociative() {
		return associative;
	}

	public PrettyPrintNode setAssociative(Integer associative) {
		this.associative = associative;
		return this;
	}

	public PrettyPrintNode() {
	}

	public PrettyPrintNode(String begin, String beginList,
			String betweenListElements, String endList, String betweenChildren,
			String end, Integer precedence, Integer associative) {
		if (begin != null)
			this.begin = begin;
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
