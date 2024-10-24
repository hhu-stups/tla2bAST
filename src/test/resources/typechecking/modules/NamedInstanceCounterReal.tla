-------------- MODULE NamedInstanceCounterReal ----------------
CONSTANTS start
VARIABLES c
count == INSTANCE CounterReal WITH x <- c
Init == count!Init
Next == count!Next
=================================