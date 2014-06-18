--------------- MODULE InvariantExpression -------------
VARIABLES x
Init == x = 1
Inv == TRUE
Next == 1= 2 /\ UNCHANGED x
=========================================