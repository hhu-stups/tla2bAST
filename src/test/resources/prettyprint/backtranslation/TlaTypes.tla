------------------------- MODULE TlaTypes ---------------------

EXTENDS Naturals, TLC
CONSTANTS a, b, c, d, e, f, g, h, i, j, k, l
 ,m
ASSUME a = 1
ASSUME b = TRUE
ASSUME c = "abc"
ASSUME d = m

ASSUME e = <<1,2>>
ASSUME f = <<1,2,3>>
ASSUME g = << <<1,2>>,3>>
ASSUME h = <<>> /\ h \in UNION{[x -> Nat] :x \in SUBSET Nat}
ASSUME i = <<1>>
ASSUME j = (1 :> 2)

ASSUME k = [a|-> 1, b|-> TRUE]
ASSUME l = [a|-> 1] /\ l # [b|-> TRUE]
========