-------------- MODULE OperationsTest ----------------
EXTENDS Naturals
VARIABLES a,b,c
Init == a = 1 /\ b = 2 /\ c =3

begin1 == UNCHANGED<<a,b,c>>
begin2 == a' = 1  /\ b' = 2 /\ c' = 3

any1 == a' + 1 = 2 /\ UNCHANGED<<b,c>>
any2 == 1 = 1 /\ a' + 1 = 2 /\ UNCHANGED<<b,c>>
any3 == a'= 2 /\ a' >1 /\ UNCHANGED<<b,c>>

select == 1 = 1 /\ a' = 1  /\ b' = 2 /\ c' =3

Next == 
    \/ begin1
    \/ begin2
    \/ any1
    \/ any2
    \/ any3
    \/ select
=================================