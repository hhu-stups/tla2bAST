package de.tla2b.util;

import tla2sany.semantic.OpDeclNode;
import tla2sany.semantic.OpDefNode;

import java.util.HashMap;
import java.util.Map;

public class TlaUtils {

	public static Map<String, OpDeclNode> getConstantsMap(OpDeclNode[] constantNodes) {
		Map<String, OpDeclNode> constants = new HashMap<>();
		for (OpDeclNode con : constantNodes) {
			constants.put(con.getName().toString(), con);
		}
		return constants;
	}

	public static Map<String, OpDefNode> getOpDefsMap(OpDefNode[] opDefNodes) {
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
