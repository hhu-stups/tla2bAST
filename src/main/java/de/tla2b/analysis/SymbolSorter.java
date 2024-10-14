package de.tla2b.analysis;

import tla2sany.semantic.ModuleNode;
import tla2sany.semantic.OpDeclNode;
import tla2sany.semantic.OpDefNode;

import java.util.Arrays;
import java.util.Comparator;
import java.util.HashMap;
import java.util.Map;

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

	public static Map<String, OpDefNode> getDefsMap(OpDefNode[] opDefNodes) {
		Map<String, OpDefNode> definitions = new HashMap<>();
		for (OpDefNode def : opDefNodes) {
			// Definition in this module
//			if (StandardModules.contains(def.getOriginallyDefinedInModuleNode()
//					.getName().toString())
//					|| StandardModules.contains(def.getSource()
//							.getOriginallyDefinedInModuleNode().getName()
//							.toString())) {
//				continue;
//			}
			definitions.put(def.getName().toString(), def);
		}
		return definitions;
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
