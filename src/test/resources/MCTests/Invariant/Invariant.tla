----------------------------- MODULE Invariant -----------------------------
EXTENDS Naturals
VARIABLES x
Init == x = 1
Next == x' = 2
Inv == x \in 1..3

=============================================================================
\* Modification History
\* Last modified Fri May 09 12:27:40 CEST 2014 by hansen
\* Created Fri May 09 12:26:48 CEST 2014 by hansen
