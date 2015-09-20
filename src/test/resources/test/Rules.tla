----- MODULE Rules -----
EXTENDS Naturals
CONSTANTS a,b,c

Add(x,y)== x + y

Rule1 == Add(a,a) \in 1..10
Rule2 == b \in {TRUE,FALSE}
Rule3 == c \in SUBSET({<<1,2>>, <<2,3>>})
=======================
