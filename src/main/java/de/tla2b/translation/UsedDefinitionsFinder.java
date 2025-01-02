package de.tla2b.translation;

import de.be4.classicalb.core.parser.util.Utils;
import de.tla2b.analysis.AbstractASTVisitor;
import de.tla2b.analysis.SpecAnalyser;
import de.tla2b.global.BBuiltInOPs;
import de.tla2b.util.DebugUtils;
import tla2sany.semantic.ExprNode;
import tla2sany.semantic.ModuleNode;
import tla2sany.semantic.OpApplNode;
import tla2sany.semantic.OpDefNode;

import java.util.Collection;
import java.util.HashSet;
import java.util.Set;

import static de.tla2b.global.TranslationGlobals.STANDARD_MODULES;

public class UsedDefinitionsFinder extends AbstractASTVisitor {

	private final Set<OpDefNode> usedDefinitions = new HashSet<>();

	public UsedDefinitionsFinder(SpecAnalyser specAnalyser) {
		DebugUtils.printMsg("Finding used definitions");
		// some definitions are not yet supported, like recursive definitions
		// hence it is important not to try and translate all of them and only the used ones

		if (specAnalyser.getConfigFileEvaluator() != null) {
			Collection<OpDefNode> cons = specAnalyser.getConfigFileEvaluator().getConstantOverrides().values();
			for (OpDefNode def : cons) {
				visitExprNode(def.getBody());
			}
			Collection<OpDefNode> ops = specAnalyser.getConfigFileEvaluator().getOperatorOverrides().values();
			for (OpDefNode def : ops) {
				visitExprNode(def.getBody());
			}
			usedDefinitions.addAll(cons);
			usedDefinitions.addAll(ops);
		}

		visitAssumptions(specAnalyser.getModuleNode().getAssumptions());

		if (specAnalyser.getNext() != null) {
			visitExprNode(specAnalyser.getNext());
		}

		if (specAnalyser.getInitDef() != null) {
			usedDefinitions.add(specAnalyser.getInitDef());
		}

		if (specAnalyser.getInits() != null) {
			for (ExprNode init : specAnalyser.getInits()) {
				visitExprNode(init);
			}
		}

		if (specAnalyser.getInvariants() != null) {
			for (OpDefNode def : specAnalyser.getInvariants()) {
				usedDefinitions.add(def);
				visitExprNode(def.getBody());
			}
		}

		for (OpDefNode opDef : specAnalyser.getModuleNode().getOpDefs()) {
			String defName = opDef.getName().toString();
			// GOAL, ANIMATION_FUNCTION, ANIMATION_IMGxx, SET_PREF_xxx, etc.
			// DebugUtils.printDebugMsg("Checking definition: " + defName);
			if (Utils.isProBSpecialDefinitionName(defName)) {
				DebugUtils.printMsg("ProB special definition: " + defName);
				usedDefinitions.add(opDef);
			}
		}
	}

	public Set<OpDefNode> getUsedDefinitions() {
		return usedDefinitions;
	}

	@Override
	public void visitUserDefinedNode(OpApplNode n) {
		super.visitUserDefinedNode(n);

		OpDefNode def = (OpDefNode) n.getOperator();
		ModuleNode moduleNode = def.getSource().getOriginallyDefinedInModuleNode();
		if (moduleNode.getName().toString().equals("TLA2B"))
			return;
		if (BBuiltInOPs.contains(def.getName()) && STANDARD_MODULES.contains(moduleNode.getName().toString()))
			return;

		if (usedDefinitions.add(def)) {
			visitExprNode(def.getBody());
		}
	}
}
