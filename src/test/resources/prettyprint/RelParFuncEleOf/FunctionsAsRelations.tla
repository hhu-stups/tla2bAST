------------------------ MODULE FunctionsAsRelations ----------------------------------
EXTENDS FiniteSets, Functions, TLC, Sequences

LOCAL RelDom(f) == { <<x[1], x[2]>>[1] : x \in f } \* The domain of the function, syntax is weird to help TLA2B typechecker
LOCAL RelRan(f) == { <<x[1], x[2]>>[2] : x \in f } \* The range of the function, syntax is weird to help TLA2B typechecker
LOCAL MakeRel(f) == {<<x, f[x]>>: x \in DOMAIN f}
 \* Converting a TLA+ function to a set of pairs
LOCAL Rel(S, T) == SUBSET (S \times T) \* The set of relations
LOCAL IsFunc(f) == Cardinality(RelDom(f)) = Cardinality(f)
 \* Testing if f is a function
LOCAL IsTotal(f, dom) == RelDom(f) = dom
 \* Testing if f is a total function
LOCAL IsInj(f) == Cardinality(RelRan(f)) = Cardinality(f)
 \* Testing if f is a injective function
LOCAL IsSurj(f, ran) == RelRan(f) = ran
 \* Testing if f is a surjective function

RelCallWithoutWDCheck(f, x) == (CHOOSE y \in f: y[1] = x)[2]

RelCall(f, x) ==  IF Cardinality(f) = Cardinality(RelDom(f)) /\ x \in RelDom(f)
   THEN (CHOOSE y \in f: y[1] = x)[2]
   ELSE PrintT("Error: Invalid function call to relation "
            \o ToString(f) \o " and value " \o ToString(x) \o ".")
       /\ Assert(Cardinality(f) # Cardinality(RelDom(f)), "Applied a function call to a relation.")
       /\ Assert(x \notin RelDom(f), "Function applied outside domain.")
 \* The function call applied to function f and argument x
                  
RelTotalFunc(S, T) == {MakeRel(f): f \in [S -> T]}
 \* The set of total function
 
RelTotalFuncEleOf(S, T) == {f \in Rel(S,T): IsFunc(f) /\ IsTotal(f,S)}
 \* The set of total functions
 \* (Optimized to test if a certain function is a element of this set.)

RelTotalInjFunc(S, T) == {MakeRel(f): f \in TotalInjFunc(S, T)}
 \* The set of total injective functions

RelTotalInjFuncEleOf(S, T) == {f \in Rel(S,T): IsFunc(f) /\ IsTotal(f,S) /\ IsInj(f)}
 \* The set of total injective functions
 \* (Optimized to test if a certain function is a element of this set.)

RelTotalSurFunc(S, T) == {MakeRel(f): f \in TotalSurFunc(S, T)}
 \* The set of total surjective functions
 
RelTotalSurFuncEleOf(S, T) == {f \in Rel(S,T): 
    /\ IsFunc(f) /\ IsTotal(f,S) /\ IsSurj(f, T)}
 \* The set of total surjective functions
 \* (Optimized to test if a certain function is a element of this set.)

RelTotalBijFunc(S, T) == {MakeRel(f): f \in TotalBijFunc(S, T)} 
\* The set of total bijective functions

RelTotalBijFuncEleOf(S, T) == {f \in (SUBSET (S \times T)):
    /\ IsFunc(f) /\ IsTotal(f,S) /\ IsInj(f) /\ IsSurj(f, T)}
 \* The set of total bijective functions
 \* (Optimized to test if a certain function is a element of this set.)


RelParFunc(S, T) == {MakeRel(f):  f \in ParFunc(S, T)}
 \* The set of partial functions
 
RelParFuncEleOf(S, T) == {f \in Rel(S, T): IsFunc(f)} 
 \* The set of partial functions
 \* (Optimized to test if a certain function is a element of this set.)

RelParInjFunc(S, T) == {MakeRel(f):  f \in ParInjFunc(S, T)}
 \* The set of partial injective functions.
 
RelParInjFuncEleOf(S, T) == {f \in Rel(S, T): IsFunc(f) /\ IsInj(f)} 
 \* The set of partial injective functions
 \* (Optimized to test if a certain function is a element of this set.)
 
RelParSurFunc(S, T) == {MakeRel(f):  f \in ParSurFunc(S, T)}
 \* The set of partial surjective functions
 
RelParSurFuncEleOf(S, T) == {f \in Rel(S, T): IsFunc(f) /\ IsSurj(f, T)}
 \* The set of partial surjective functions.
 \* (Optimized to test if a certain function is a element of this set.)
 
RelParBijFunc(S, T) == {MakeRel(f):  f \in ParBijFunc(S, T)}
 \* The set of partial bijective functions
 
RelParBijFuncEleOf(S, T) == {f \in Rel(S, T): IsFunc(f) /\ IsSurj(f, T) /\ IsInj(f)}                 
 \* The set of partial bijective functions
 \* (Optimized to test if a certain function is a element of this set.)
=========================================================================================
