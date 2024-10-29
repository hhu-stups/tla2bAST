package de.tla2b.analysis;

import tla2sany.semantic.ModuleNode;
import tla2sany.semantic.OpDeclNode;
import tla2sany.semantic.OpDefNode;

import java.util.Arrays;
import java.util.Comparator;

public class SymbolSorter {

	public static void sort(ModuleNode moduleNode) {
		// sort constants
		sortDeclNodes(moduleNode.getConstantDecls());
		// sort variables
		sortDeclNodes(moduleNode.getVariableDecls());
		// sort definitions
		sortOpDefNodes(moduleNode.getOpDefs());
	}

	public static void sortDeclNodes(OpDeclNode[] opDeclNodes) {
		Arrays.sort(opDeclNodes, new OpDeclNodeComparator());
	}

	public static void sortOpDefNodes(OpDefNode[] opDefNodes) {
		Arrays.sort(opDefNodes, new OpDefNodeComparator());
	}
}

class OpDeclNodeComparator implements Comparator<OpDeclNode> {
	public int compare(OpDeclNode a, OpDeclNode b) {
		return Integer.compare(a.getUid(), b.getUid());
	}
}

class OpDefNodeComparator implements Comparator<OpDefNode> {
	public int compare(OpDefNode a, OpDefNode b) {
		if (a.getLocation().equals(b.getLocation())) {
			return Integer.compare(a.getSource().getUid(), b.getSource().getUid());
		}
		return Integer.compare(a.getUid(), b.getUid());
	}
}
