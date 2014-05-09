-------------- MODULE RecursiveFunctionGlobalVariable ----------------
EXTENDS Integers, FiniteSets
VARIABLES x
Sum[a \in Nat] == IF a = 0 THEN x ELSE a + Sum[a-1]
Init == x = 1
Next == x'= Sum[x]
=================================