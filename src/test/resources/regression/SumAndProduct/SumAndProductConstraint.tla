------------------------- MODULE SumAndProductConstraint -------------------------
(****************************************************************************)
(* This module formalizes the "sum and product" puzzle, due to Freudenthal  *)
(* (1969), and which goes as follows:                                       *)
(* J says to S and P: I have chosen two integers x and y such that          *)
(* 1 < x <= y < 100. In a moment, I will inform S only of the sum x+y       *)
(* and P only of the product x*y. These announcements remain private.       *)
(* You are required to determine the pair (x,y). He acts as said.           *)
(* The following conversation now takes place:                              *)
(* 1. P says: "I don't know it."                                            *)
(* 2. S says: "I knew you didn't."                                          *)
(* 3. P says: "Now I know it."                                              *)
(* 4. S says: "I now also know it."                                         *)
(* Determine the pair (x,y).                                                *)
(* In fact, the first announcement is implied by the second one, so we will *)
(* not take it into account in the following formal.                        *)
(****************************************************************************)

EXTENDS Naturals, FiniteSets, TLC

Pairs == { <<i,j>> \in (2 .. 99) \X (2 .. 99) : i <= j }

(* S and P can only observe the sum and product of a pair of numbers *)
obsS(i,j) == i+j
obsP(i,j) == i*j

equivS(i,j,k,l) == obsS(i,j) = obsS(k,l)
equivP(i,j,k,l) == obsP(i,j) = obsP(k,l)

(* Assertions are formalized as sets of pairs, and a "world" is a pair.
   S and P know an assertion A in world <<i,j>> \in W if all worlds in W
   equivalent to (i,j) satisfy A. *)
knowsS(W,i,j,A) == \A <<k,l>> \in W : equivS(i,j,k,l) => <<k,l>> \in A
knowsP(W,i,j,A) == \A <<k,l>> \in W : equivP(i,j,k,l) => <<k,l>> \in A

(* S and P know that A is false in world <<i,j>> if no world equivalent to
   (i,j) satisfies A. *)
knowsS_neg(W,i,j,A) == \A <<k,l>> \in W : equivS(i,j,k,l) => <<k,l>> \notin A
knowsP_neg(W,i,j,A) == \A <<k,l>> \in W : equivP(i,j,k,l) => <<k,l>> \notin A

(* worlds in which P can identify the pair uniquely *)
knowP_pair == { <<i,j>> \in Pairs : knowsP(Pairs, i,j, {<<i,j>>}) }
(* worlds in which S knows that P cannot know the pair *)
Step2 == { <<i,j>> \in Pairs : knowsS_neg(Pairs, i,j, knowP_pair) }
(* filter out worlds in Step2 for which P now knows the pair uniquely *)
Step3 == { <<i,j>> \in Step2 : knowsP(Step2, i,j, {<<i,j>>}) }
(* now restrict to worlds in Step3 for which also S knows the pair uniquely *)
Step4 == { <<i,j>> \in Step3 : knowsS(Step3, i,j, {<<i,j>>}) }

CONSTANTS k
ASSUME k = Step4

==================================================================================
\* Modification History
\* Last modified Mon Apr 22 11:02:28 CEST 2013 by merz
\* Created Sun Apr 21 19:19:53 CEST 2013 by merz
