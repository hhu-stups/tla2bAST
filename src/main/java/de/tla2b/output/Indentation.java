package de.tla2b.output;

import java.util.HashSet;
import java.util.Hashtable;

import de.be4.classicalb.core.parser.analysis.DepthFirstAdapter;
import de.be4.classicalb.core.parser.node.AConjunctPredicate;
import de.be4.classicalb.core.parser.node.APredicateDefinitionDefinition;
import de.be4.classicalb.core.parser.node.APropertiesMachineClause;
import de.be4.classicalb.core.parser.node.Node;
import de.be4.classicalb.core.parser.node.Start;

public class Indentation extends DepthFirstAdapter {

	private Hashtable<Node, Integer> indentation = new Hashtable<Node, Integer>();
	private HashSet<Node> newlineMiddle = new HashSet<Node>();

	public Indentation(Start start) {
		start.apply(this);
	}

	public void inAPropertiesMachineClause(APropertiesMachineClause node) {
		indentation.put(node.getPredicates(), 0);
	}

	@Override
	public void inAConjunctPredicate(AConjunctPredicate node) {
		Integer indent = indentation.get(node);
		if (indent != null) {
			indentation.put(node.getLeft(), indent);
			indentation.put(node.getRight(), indent);

			newlineMiddle.add(node);

		}
	}

    public void inAPredicateDefinitionDefinition(APredicateDefinitionDefinition node)
    {
    	indentation.put(node.getRhs(), 0);
    }
	
	
	public boolean printNewLineInTheMiddle(Node node) {
		return newlineMiddle.contains(node);
	}

	public Integer getIndent(Node node) {
		Integer res = indentation.get(node);
		if (res == null) {
			res = 0;
		}
		return res;
	}
}
