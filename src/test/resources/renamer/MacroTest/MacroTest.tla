---- MODULE MacroTest ----
EXTENDS Integers
egt(x) == \E y \in Nat \ {0}: y<100 /\ x<y
egt2(x) == \E yy \in Nat \ {0}: yy<100 /\ x<yy
VARIABLES y
Invariant ==  y \in Int /\ egt(y+1) (* is false ! *)
 /\ egt2(y+1) (* is true *)
Init ==  y = 5
======