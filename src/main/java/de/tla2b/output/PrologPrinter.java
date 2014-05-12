package de.tla2b.output;

import java.io.File;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Hashtable;
import java.util.List;
import java.util.Map;

import de.be4.classicalb.core.parser.BParser;
import de.be4.classicalb.core.parser.analysis.pragma.Pragma;
import de.be4.classicalb.core.parser.analysis.prolog.ASTProlog;
import de.be4.classicalb.core.parser.analysis.prolog.ClassicalPositionPrinter;
import de.be4.classicalb.core.parser.analysis.prolog.NodeIdAssignment;
import de.be4.classicalb.core.parser.analysis.prolog.RecursiveMachineLoader;
import de.be4.classicalb.core.parser.node.Node;
import de.be4.classicalb.core.parser.node.Start;
import de.hhu.stups.sablecc.patch.SourcePositions;
import de.prob.prolog.output.IPrologTermOutput;
import de.prob.prolog.output.PrologTermOutput;
import de.tla2b.types.TLAType;

public class PrologPrinter {
	RecursiveMachineLoader rml;
	BParser bParser;
	String moduleName;

	private final Map<String, SourcePositions> positions = new HashMap<String, SourcePositions>();
	private final List<File> files = new ArrayList<File>();
	private final Hashtable<Node, TLAType> typeTable;
		
	
	public PrologPrinter(RecursiveMachineLoader rml, BParser bParser, File mainFile,
			String moduleName, Hashtable<Node, TLAType> typeTable) {
		this.rml = rml;
		this.bParser = bParser;
		this.moduleName = moduleName;
		this.typeTable = typeTable;
		files.add(mainFile);
	}

	public void printAsProlog(final PrintWriter out, final boolean useIndention) {
		final IPrologTermOutput pout = new PrologTermOutput(out, useIndention);
		printAsProlog(pout);
	}

	public void printAsProlog(final IPrologTermOutput pout) {
		// final ClassicalPositionPrinter pprinter = new
		// ClassicalPositionPrinter(
		// rml.getNodeIdMapping());
		
		final TlaTypePrinter pprinter = new TlaTypePrinter(rml.getNodeIdMapping(), typeTable);

		final ASTProlog prolog = new ASTProlog(pout, pprinter);

		// parser version
		pout.openTerm("parser_version");
		pout.printAtom(BParser.getBuildRevision());
		pout.closeTerm();
		pout.fullstop();

		// machine
		pout.openTerm("classical_b");
		pout.printAtom(moduleName);
		pout.openList();
		for (final File file : files) {
			try {
				pout.printAtom(file.getCanonicalPath());
			} catch (IOException e) {
				pout.printAtom(file.getPath());
			}
		}
		pout.closeList();
		pout.closeTerm();
		pout.fullstop();
		for (final Map.Entry<String, Start> entry : rml.getParsedMachines()
				.entrySet()) {
			pout.openTerm("machine");
			final SourcePositions src = positions.get(entry.getKey());
			pprinter.setSourcePositions(src);
			entry.getValue().apply(prolog);
			pout.closeTerm();
			pout.fullstop();
		}

//		if (bParser.getPragmas().size() > 0) {
//			NodeIdAssignment ids = pprinter.nodeIds;
//
//			List<Pragma> pragmas = bParser.getPragmas();
//			for (Pragma pragma : pragmas) {
//				pragma.printProlog(pout, ids);
//				pout.fullstop();
//			}
//
//		}
		pout.flush();
	}
}
