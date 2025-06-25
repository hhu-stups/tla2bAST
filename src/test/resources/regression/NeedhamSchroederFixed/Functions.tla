----------------------------- MODULE Functions -----------------------------
EXTENDS TLC

FuncAssign(f, d, e) ==  d :> e @@ f
 \* [x \in (DOMAIN f) \cup {d} |-> IF x = d THEN e ELSE f[x]]
 \* Overwriting the function f at index d with value e

ParFunc(S, T) ==  UNION{[x -> T] :x \in SUBSET S}
 \* The set of all partial functions

=============================================================================
