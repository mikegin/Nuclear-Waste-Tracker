---- MODULE MC ----
EXTENDS nuclear_waste_tracker, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
pid1, pid2, pid3
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
cid1, cid2, cid3
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
name1, name2, name3
----

\* MV CONSTANT definitions U_PID
const_1512599750276129000 == 
{pid1, pid2, pid3}
----

\* MV CONSTANT definitions U_CID
const_1512599750276130000 == 
{cid1, cid2, cid3}
----

\* MV CONSTANT definitions PHASE_NAME
const_1512599750276131000 == 
{name1, name2, name3}
----

\* SYMMETRY definition
symm_1512599750276132000 == 
Permutations(const_1512599750276129000) \union Permutations(const_1512599750276130000) \union Permutations(const_1512599750276131000)
----

\* CONSTANT definitions @modelParameterConstants:1N
const_1512599750276133000 == 
3
----

\* INIT definition @modelBehaviorInit:0
init_1512599750276134000 ==
Init
----
\* NEXT definition @modelBehaviorNext:0
next_1512599750277135000 ==
Next
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1512599750277136000 ==
TypeOK
----
=============================================================================
\* Modification History
\* Created Wed Dec 06 17:35:50 EST 2017 by mikegin
