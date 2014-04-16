---- MODULE MC ----
EXTENDS SimpleAllocator, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
c1, c2, c3
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
r1, r2, r3
----

\* MV CONSTANT definitions Clients
const_13975725253553000 == 
{c1, c2, c3}
----

\* MV CONSTANT definitions Resources
const_13975725253664000 == 
{r1, r2, r3}
----

\* INIT definition @modelBehaviorInit:0
init_13975725253775000 ==
Init
----
\* NEXT definition @modelBehaviorNext:0
next_13975725253886000 ==
Next
----
=============================================================================
\* Modification History
\* Created Tue Apr 15 16:35:25 CEST 2014 by hansen
