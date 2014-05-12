package de.tla2b.output;

import de.tla2b.types.BoolType;
import de.tla2b.types.EnumType;
import de.tla2b.types.FunctionType;
import de.tla2b.types.IntType;
import de.tla2b.types.ModelValueType;
import de.tla2b.types.PairType;
import de.tla2b.types.SetType;
import de.tla2b.types.StringType;
import de.tla2b.types.StructOrFunctionType;
import de.tla2b.types.StructType;
import de.tla2b.types.TupleType;
import de.tla2b.types.UntypedType;


public interface TypeVisitorInterface {
	
	void caseIntegerType(IntType type);
	void caseBoolType(BoolType type);
	void caseEnumType(EnumType type);
	void caseFunctionType(FunctionType type);
	void caseModelValueType(ModelValueType type);
	void casePairType(PairType type);
	void caseSetType(SetType type);
	void caseStringType(StringType type);
	void caseStructOrFunction(StructOrFunctionType type);
	void caseStructType(StructType type);
	void caseTupleType(TupleType type);
	void caseUntyped(UntypedType type);
}
