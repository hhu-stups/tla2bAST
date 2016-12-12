package de.tla2b.output;

import java.util.HashSet;
import java.util.Hashtable;
import java.util.Set;

import de.be4.classicalb.core.parser.util.Utils;
import de.be4.classicalb.core.parser.analysis.DepthFirstAdapter;
import de.be4.classicalb.core.parser.node.AIdentifierExpression;
import de.be4.classicalb.core.parser.node.Node;
import de.be4.classicalb.core.parser.node.Start;
import de.be4.classicalb.core.parser.node.TIdentifierLiteral;

public class Renamer extends DepthFirstAdapter {

	private final java.util.Hashtable<Node, String> namesTables;
	private final Set<String> globalNames;

	public Renamer(Start start) {
		this.namesTables = new Hashtable<Node, String>();
		this.globalNames = new HashSet<String>();

		start.apply(this);
	}

	private final static Set<String> KEYWORDS = new HashSet<String>();
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
		KEYWORDS.add("MACHINE");
		KEYWORDS.add("EVENTS");
		KEYWORDS.add("OPERATIONS");
	}

	@Override
	public void caseAIdentifierExpression(AIdentifierExpression node) {
		String name = Utils.getIdentifierAsString(node.getIdentifier());
		String newName = incName(name, new HashSet<String>());
		namesTables.put(node, newName);
	}

	@Override
	public void caseTIdentifierLiteral(TIdentifierLiteral node){
		String name = node.getText();
		String newName = incName(name, new HashSet<String>());
		namesTables.put(node, newName);
	}
	
	private Boolean existingName(String name) {
		if (globalNames.contains(name) || KEYWORDS.contains(name)) {
			return true;
		} else
			return false;
	}

	private String incName(String name, Set<String> tempSet) {
		String res = name;
		for (int i = 1; existingName(res) || tempSet.contains(res); i++) {
			res = name + "_" + i;
		}
		return res;
	}

	public String getNewName(Node node) {
		return namesTables.get(node);
	}
}
