package de.tla2b.output;

import de.tla2b.types.*;

public interface TypeVisitorInterface {

	void caseIntegerType(IntType type);

	void caseBoolType(BoolType type);

	void caseEnumType(EnumType type);

	void caseFunctionType(FunctionType type);

	void caseModelValueType(ModelValueType type);

	void caseRealType(RealType type);

	void caseIntegerOrRealType(IntegerOrRealType type);

	void caseSetType(SetType type);

	void caseStringType(StringType type);

	void caseStructOrFunction(StructOrFunctionType type);

	void caseStructType(StructType type);

	void caseTupleType(TupleType type);

	void caseTupleOrFunctionType(TupleOrFunction type);

	void caseUntyped(UntypedType type);
}
