----------------------- MODULE nuclear_waste_tracker -----------------------
EXTENDS Integers, Sequences, FiniteSets, TLC
CONSTANTS
    N
    , U_CID
    , U_PID
    , PHASE_NAME
ASSUME
    N > 0

VALUE == -N .. N \* abstract value of mSv

\* types of materials processed in the nuclear plant
MATERIAL == {"glass", "metal", "plastic", "liquid"}

\* set of all phase records
PHASE ==  [ phase_name: PHASE_NAME
          , capacity: Int
          , expected_materials: {MATERIAL}
          ]
          
\* set of all container records
CONTAINER ==  [ material: MATERIAL
              , radioactivity: Int
              ] 
VARIABLES
    PID \* registered phases
    , CID  \* registered containers
    , containers \* mapping of cid's to container attributes
    , phases \* mapping of pid's to phase attributes
    , container_phase \* mapping of cid's to pid'
    , maximum_phase_radiation \* max phase radiation
    , maximum_container_radiation \* max container radiation
    


-------
\* Invariants
TypeOK ==
    /\ PID \subseteq U_PID
    /\ CID \subseteq U_CID
    /\ containers \in [CID -> CONTAINER]
    /\ phases \in [PID -> PHASE]
    /\ container_phase \in [CID -> PID]
    /\ maximum_phase_radiation \in VALUE
    /\ maximum_container_radiation \in VALUE
-------
\* Actions
new_tracker(a_maximum_phase_radiation, a_maximum_container_radiation) ==
    /\ Cardinality(CID) = 0
    /\ a_maximum_phase_radiation \in Nat
    /\ a_maximum_container_radiation \in Nat
    /\ a_maximum_phase_radiation >= a_maximum_container_radiation
    /\ maximum_phase_radiation' = a_maximum_phase_radiation
    /\ maximum_container_radiation' = a_maximum_container_radiation
    /\ UNCHANGED <<PID, CID, containers, phases, container_phase>>

new_phase(pid, phase_name, capacity, expected_materials) ==
    /\ pid \in U_PID
    /\ pid \notin PID
    /\ phase_name \in PHASE_NAME
    /\ capacity \in Nat
    /\ capacity > 0
    /\ expected_materials \in {MATERIAL}
    /\ expected_materials /= {}
    /\ PID' = PID \union {pid}
    /\ phases' = 
        phases @@ pid :> [ phase_name |-> phase_name
                         , capacity |-> capacity
                         , expected_materials |-> expected_materials
                         ]
    /\ UNCHANGED <<CID, containers, container_phase, maximum_phase_radiation, maximum_container_radiation>>
-------

Init == 
    /\ PID = {}
    /\ CID = {}
    /\ containers = <<>>
    /\ phases = <<>>
    /\ container_phase = <<>>
    /\ maximum_phase_radiation = 0
    /\ maximum_container_radiation = 0

Next ==
    \/ (\E mpr, mcr \in VALUE : new_tracker(mpr, mcr))
    \/ (\E   pid \in U_PID
           , phase_name \in PHASE_NAME
           , capacity \in VALUE
           , expected_materials \in {MATERIAL}
                : new_phase(pid, phase_name, capacity, expected_materials))
        
=============================================================================
\* Modification History
\* Last modified Wed Dec 06 15:43:03 EST 2017 by mikegin
\* Created Sat Nov 25 16:49:51 EST 2017 by mikegin
