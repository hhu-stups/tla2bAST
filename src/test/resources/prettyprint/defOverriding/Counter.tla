-------------------------- MODULE Counter -----------------------------
EXTENDS Naturals
CONSTANTS start, foo(_)
VARIABLE x
-----------------------------------------------------------------------
Init  ==  x = start
val == foo(1)
Next  ==  x' = x + val
=======================================================================
