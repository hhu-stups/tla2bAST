---------------------------- MODULE Let -------------------------------
EXTENDS Naturals
VARIABLES x
-----------------------------------------------------------------------------
Init == x = 1
val == 4
Next ==  
	\E e \in {1,2}:
	LET
		foo(p) == 1 + e + p
	IN
		x' =  x + foo(3) + val
=============================================================================
