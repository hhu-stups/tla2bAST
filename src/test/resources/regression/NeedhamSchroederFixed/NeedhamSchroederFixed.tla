---- MODULE NeedhamSchroederFixed ----
EXTENDS Naturals, Sequences, TLC, Functions
CONSTANTS initiator, responder, responder_2_generate, responder_1_receive, initiator_3_receive, initiator_4_send, initiator_2_send, initiator_1_generate, responder_4_receive, responder_3_send
VARIABLES threads

ROLE == {initiator, responder}
ACTION_1 == {responder_2_generate, responder_1_receive, initiator_3_receive, initiator_4_send, initiator_2_send, initiator_1_generate, responder_4_receive, responder_3_send}
MaxThreads == TLCEval(2)
Protocol == TLCEval((responder:><<responder_1_receive, responder_2_generate, responder_3_send, responder_4_receive>> @@ initiator:><<initiator_1_generate, initiator_2_send, initiator_3_receive, initiator_4_send>>))
AGENT == TLCEval({1, 4, 3, 2})
ValidSubs == TLCEval({(initiator:>1 @@ responder:>3), (responder:>4 @@ initiator:>3), (responder:>2 @@ initiator:>1), (initiator:>3 @@ responder:>1)})

Invariant1 == threads \in Seq([role : DOMAIN Protocol, sub : ParFunc(DOMAIN Protocol, AGENT)])

Init == threads = <<>>

create(tid, role, sub) == (tid =< MaxThreads /\ threads' = FuncAssign(threads, tid, [role |-> role, sub |-> sub]))

Next == \E tid \in {Len(threads) + 1}, role \in DOMAIN Protocol, sub \in ValidSubs : create(tid, role, sub)
====
