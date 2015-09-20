package de.tla2b.output;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Hashtable;

import de.be4.classicalb.core.parser.analysis.prolog.NodeIdAssignment;
import de.be4.classicalb.core.parser.analysis.prolog.PositionPrinter;
import de.be4.classicalb.core.parser.node.Node;
import de.hhu.stups.sablecc.patch.PositionedNode;
import de.hhu.stups.sablecc.patch.SourcePositions;
import de.prob.prolog.output.IPrologTermOutput;
import de.tla2b.exceptions.NotImplementedException;
import de.tla2b.types.BoolType;
import de.tla2b.types.EnumType;
import de.tla2b.types.FunctionType;
import de.tla2b.types.IntType;
import de.tla2b.types.TLAType;
import de.tla2b.types.ModelValueType;
import de.tla2b.types.PairType;
import de.tla2b.types.SetType;
import de.tla2b.types.StringType;
import de.tla2b.types.StructOrFunctionType;
import de.tla2b.types.StructType;
import de.tla2b.types.TupleType;
import de.tla2b.types.UntypedType;

public class TlaTypePrinter implements PositionPrinter, TypeVisitorInterface {
	private IPrologTermOutput pout;

	// to look up the identifier of each node
	public final NodeIdAssignment nodeIds;

	private final Hashtable<Node, TLAType> typeTable;

	private HashSet<PositionedNode> positions;

	// public TlaTypePrinter(final NodeIdAssignment nodeIds) {
	// this.nodeIds = nodeIds;
	// }

	public TlaTypePrinter(NodeIdAssignment nodeIdAssignment,
			Hashtable<Node, TLAType> typeTable) {
		this.nodeIds = nodeIdAssignment;
		this.typeTable = typeTable;
	}

	public void setSourcePositions(final HashSet<PositionedNode> positions) {
		this.positions = positions;
	}

	public void printPosition(final Node node) {
		TLAType type = typeTable.get(node);
		if (type != null) {
			pout.openTerm("info");
		}

		final Integer id = nodeIds.lookup(node);
		if (id == null) {
			pout.printAtom("none");
		} else {
			if (positions != null && positions.contains(node)) {
				PositionedNode pNode = (PositionedNode) node;
				pout.openTerm("pos", true);
				pout.printNumber(id);
				pout.printNumber(nodeIds.lookupFileNumber(node));
				pout.printNumber(pNode.getStartPos().getLine());
				pout.printNumber(pNode.getStartPos().getPos());
				pout.printNumber(pNode.getEndPos().getLine());
				pout.printNumber(pNode.getEndPos().getPos());
				pout.closeTerm();
			} else {
				pout.printNumber(id);
			}
		}
		if (type != null) {
			pout.openTerm("tla_type");
			type.apply(this);
			pout.closeTerm();

			pout.closeTerm();
		}
	}

	public void setPrologTermOutput(final IPrologTermOutput pout) {
		this.pout = pout;
	}

	public void caseIntegerType(IntType t) {
		pout.printAtom("integer");

	}

	public void caseBoolType(BoolType t) {
		pout.printAtom("bool");
	}

	public void caseEnumType(EnumType type) {
		pout.printAtom("modelvalue");
	}

	public void caseFunctionType(FunctionType type) {
		pout.openTerm("function", true);
		type.getDomain().apply(this);
		type.getRange().apply(this);
		pout.closeTerm();
	}

	public void caseModelValueType(ModelValueType type) {
		pout.printAtom("modelvalue");
	}

	public void casePairType(PairType type) {
		pout.openTerm("tuple");
		pout.openList();
		type.getFirst().apply(this);
		type.getSecond().apply(this);
		pout.closeList();
		pout.closeTerm();
	}

	public void caseSetType(SetType type) {
		pout.openTerm("set");
		type.getSubType().apply(this);
		pout.closeTerm();
	}

	public void caseStringType(StringType type) {
		pout.printAtom("string");
	}

	public void caseStructOrFunction(StructOrFunctionType type) {
		throw new NotImplementedException("should not happen");
	}

	public void caseStructType(StructType type) {
		pout.openTerm("record");
		pout.openList();
		ArrayList<String> fields = type.getFields();
		for (String field : fields) {
			if (type.isExtensible()) {
				pout.openTerm("opt");
			} else {
				pout.openTerm("field");
			}
			pout.printAtom(field);
			type.getType(field).apply(this);
			pout.closeTerm();
		}
		pout.closeList();
		pout.closeTerm();
	}

	public void caseTupleType(TupleType type) {
		pout.openTerm("tuple");
		pout.openList();
		for (TLAType t : type.getTypes()) {
			t.apply(this);
		}
		pout.closeList();
		pout.closeTerm();
	}

	public void caseUntyped(UntypedType type) {
		throw new NotImplementedException("should not happen");
	}

}
