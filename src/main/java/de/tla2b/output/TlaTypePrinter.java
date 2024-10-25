package de.tla2b.output;

import de.be4.classicalb.core.parser.analysis.prolog.ClassicalPositionPrinter;
import de.be4.classicalb.core.parser.analysis.prolog.INodeIds;
import de.be4.classicalb.core.parser.node.Node;
import de.prob.prolog.output.IPrologTermOutput;
import de.tla2b.exceptions.NotImplementedException;
import de.tla2b.types.*;

import java.util.List;
import java.util.Map;

public class TlaTypePrinter extends ClassicalPositionPrinter implements TypeVisitorInterface {

	private IPrologTermOutput pout;
	private final Map<Node, TLAType> types;

	public TlaTypePrinter(INodeIds nodeIds, Map<Node, TLAType> types) {
		super(nodeIds);
		super.setPrintSourcePositions(true, true);
		this.types = types;
	}

	public void printPosition(final Node node) {
		TLAType type = types.get(node);
		if (type != null) {
			pout.openTerm("info");
		}

		super.printPosition(node);

		if (type != null) {
			pout.openTerm("tla_type");
			type.apply(this);
			pout.closeTerm();
			pout.closeTerm();
		}
	}

	public void setPrologTermOutput(final IPrologTermOutput pout) {
		super.setPrologTermOutput(pout);
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

	public void caseRealType(RealType type) {
		pout.printAtom("real");
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
		List<String> fields = type.getFields();
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
