-------------- MODULE RecursiveFunction1 ----------------
EXTENDS Integers, FiniteSets
foo(a) == LET Sum[x \in Nat] == IF x = 0 THEN a ELSE x + Sum[x-1] IN Sum[3]
ASSUME 11 = foo(5)
=================================