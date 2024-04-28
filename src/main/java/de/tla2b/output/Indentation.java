package de.tla2b.output;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Hashtable;
import java.util.List;

import de.be4.classicalb.core.parser.analysis.DepthFirstAdapter;
import de.be4.classicalb.core.parser.node.AConjunctPredicate;
import de.be4.classicalb.core.parser.node.AConstantsMachineClause;
import de.be4.classicalb.core.parser.node.AExistsPredicate;
import de.be4.classicalb.core.parser.node.AForallPredicate;
import de.be4.classicalb.core.parser.node.AImplicationPredicate;
import de.be4.classicalb.core.parser.node.APredicateDefinitionDefinition;
import de.be4.classicalb.core.parser.node.APropertiesMachineClause;
import de.be4.classicalb.core.parser.node.ASetsMachineClause;
import de.be4.classicalb.core.parser.node.Node;
import de.be4.classicalb.core.parser.node.PExpression;
import de.be4.classicalb.core.parser.node.PSet;
import de.be4.classicalb.core.parser.node.Start;

public class Indentation extends DepthFirstAdapter {

	private final Hashtable<Node, Integer> indentation = new Hashtable<>();
	private final HashSet<Node> newlineMiddle = new HashSet<>();
	private final HashSet<Node> nodesWithNewlineAtTheEnd = new HashSet<>();
	private final HashSet<Node> indentedNodes = new HashSet<>();
	public final static String INDENT = "  ";
	public final static String SPACE = " ";

	public Indentation(Start start) {
		start.apply(this);
	}

	@Override
	public void defaultIn(final Node node) {
		if (node.parent() != null) {
			if (!indentation.containsKey(node)) {
				setIndentation(node, getIndentNumber(node.parent()));
			}
		}
	}

	private void addIndentedNode(final Node node) {
		indentedNodes.add(node);
	}

	private void addNewlineNode(final Node node) {
		newlineMiddle.add(node);
	}

	@Override
	public void caseASetsMachineClause(ASetsMachineClause node) {
		List<PSet> copy = new ArrayList<>(node.getSetDefinitions());
		for (PSet e : copy) {
			setIndentation(e, getIndentNumber(node) + 1);
			addIndentedNode(e);
			e.apply(this);
		}
	}

	@Override
	public void caseAConstantsMachineClause(AConstantsMachineClause node) {
		List<PExpression> copy = new ArrayList<>(
			node.getIdentifiers());
		for (PExpression e : copy) {
			setIndentation(e, getIndentNumber(node) + 1);
			addIndentedNode(e);
			e.apply(this);
		}
	}

	public void inAPropertiesMachineClause(APropertiesMachineClause node) {
		setIndentation(node.getPredicates(), getIndentNumber(node) + 1);
		addIndentedNode(node.getPredicates());
	}

	@Override
	public void inAConjunctPredicate(AConjunctPredicate node) {
		defaultIn(node);
		addNewlineNode(node);
	}

	@Override
	public void inAForallPredicate(AForallPredicate node) {
		defaultIn(node);
		setIndentation(node.getImplication(), getIndentNumber(node) + 2);
	}

	@Override
	public void inAExistsPredicate(AExistsPredicate node) {
		defaultIn(node);
		setIndentation(node.getPredicate(), getIndentNumber(node) + 2);
	}

	@Override
	public void inAImplicationPredicate(AImplicationPredicate node) {
		defaultIn(node);
		addNewlineNode(node);
	}

	public void inAPredicateDefinitionDefinition(
			APredicateDefinitionDefinition node) {
		indentation.put(node.getRhs(), 0);
	}

	public boolean printNewLineInTheMiddle(Node node) {
		return newlineMiddle.contains(node);
	}

	public void setIndentation(Node node, Integer i) {
		indentation.put(node, i);
	}

	public void setNewlineAtTheEnd(Node node) {
		nodesWithNewlineAtTheEnd.add(node);
	}

	public Integer getIndentNumber(Node node) {
		Integer res = indentation.get(node);
		if (res == null) {
			res = 0;
		}
		return res;
	}

	public StringBuilder getIndent(Node node) {
		StringBuilder sb = new StringBuilder();
		Integer i = indentation.get(node);

		if (i == null) {
			i = 0;
		}
		for (int j = 0; j < i; j++) {
			sb.append(INDENT);
		}
		return sb;
	}

	public boolean isNewline(Node node) {
		return nodesWithNewlineAtTheEnd.contains(node);
	}

	public static String getIdent() {
		return INDENT;
	}

	public boolean isIndentedNode(final Node node) {
		return indentedNodes.contains(node);
	}
}
