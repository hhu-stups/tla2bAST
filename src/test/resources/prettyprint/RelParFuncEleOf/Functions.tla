----------------------------- MODULE Functions -----------------------------
EXTENDS FiniteSets, TLC

Range(f) == {f[x] : x \in DOMAIN f}
 \* The range of the function f

Image(f,S) == {f[x] : x \in S \cap DOMAIN f}
 \* The image of the set S for the function f

Card(f) == Cardinality(DOMAIN f)
 \* The Cardinality of the function f

Id(S) == [x \in S|-> x]
 \* The identity function on set S

DomRes(S, f) == [x \in (S \cap DOMAIN f) |-> f[x]]
 \* The restriction on the domain of f for set S

DomSub(S, f) == [x \in DOMAIN f \ S |-> f[x]]
 \* The subtraction on the domain of f for set S

RanRes(f, S) == [x \in {y \in DOMAIN f: f[y] \in S} |-> f[x]]
 \* The restriction on the range of f for set S

RanSub(f, S) == [x \in {y \in DOMAIN f: f[y] \notin S} |-> f[x]]
 \* The subtraction on the range of f for set S

Inverse(f) == {<<f[x],x>>: x \in DOMAIN f}
 \* The inverse relation of the function f

Override(f, g) == [x \in (DOMAIN f) \cup DOMAIN g |-> IF x \in DOMAIN g THEN g[x] ELSE f[x]]
 \* Overwriting of the function f with the function g

FuncAssign(f, d, e) ==  d :> e @@ f
 \* [x \in (DOMAIN f) \cup {d} |-> IF x = d THEN e ELSE f[x]]
 \* Overwriting the function f at index d with value e

TotalInjFunc(S, T) == {f \in [S -> T]:
    Cardinality(DOMAIN f) = Cardinality(Range(f))}
 \* The set of all total injective functions

TotalSurFunc(S, T) == {f \in [S -> T]: T = Range(f)}
 \* The set of all total surjective functions

TotalBijFunc(S, T) == {f \in [S -> T]: T = Range(f) /\
    Cardinality(DOMAIN f) = Cardinality(Range(f))}
 \* The set of all total bijective functions

ParFunc(S, T) ==  UNION{[x -> T] :x \in SUBSET S}
 \* The set of all partial functions

ParFuncEleOf(f, S, T) == {x \in {f} :  DOMAIN f \subseteq S /\ Range(f) \subseteq T}
 \* The set containing f if f is a partial function

isEleOfParFunc(f, S, T) == DOMAIN f \subseteq S /\ Range(f) \subseteq T
 \* Test if the function f is a partial function

ParInjFunc(S, T)== {f \in ParFunc(S, T):
    Cardinality(DOMAIN f) = Cardinality(Range(f))}
\* The set of all partial injective functions

ParInjFuncEleOf(f, S, T)== {x \in {f}:
	/\ DOMAIN f \subseteq S
	/\ Range(f) \subseteq T
    /\ Cardinality(DOMAIN f) = Cardinality(Range(f))}
\* The set containing f if f is a partial injective function

ParSurFunc(S, T)== {f \in ParFunc(S, T): T = Range(f)}
\* The set of all partial surjective function

ParSurFuncEleOf(f, S, T)== {x \in {f}:
	/\ DOMAIN f \subseteq S
	/\ Range(f) \subseteq T
    /\ T = Range(f)}
\* The set containing f if f is a partial surjective function

ParBijFunc(S, T) == {f \in ParFunc(S, T):
	/\ Range(f) = T
	/\ Cardinality(DOMAIN f) = Cardinality(Range(f))}
 \* The set of all partial bijective functions

ParBijFuncEleOf(f, S, T) == {x \in {f}:
	/\ DOMAIN f \subseteq S
	/\ Range(f) \subseteq T
    /\ Cardinality(DOMAIN f) = Cardinality(Range(f))
	/\ T = Range(f)}
\* The set containing f if f is a partial bijective function
=============================================================================
