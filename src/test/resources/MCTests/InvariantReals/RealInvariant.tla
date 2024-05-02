--------------------------- MODULE RealInvariant ---------------------------
EXTENDS Reals
VARIABLES x,y
Init == x = 1.0 /\ y = 2.0
Next == x' = 2.0 /\ y' = 3.0
TestExpression == x*x + y*y
Inv == TestExpression <= 10.0

============================================================================
