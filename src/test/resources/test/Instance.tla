----- MODULE Instance -----
EXTENDS Data1, Naturals
R1 == INSTANCE Rules WITH a <- 7, b <- def_b, c <- def_c
R2 == INSTANCE Rules WITH a <- 8, b <- def_b, c <- def_c


CONSTANTS k
Add2(x,y) == 3

ASSUME LabelName == R1!Rule1
ASSUME LabelName2 == R2!Rule1
=======================

