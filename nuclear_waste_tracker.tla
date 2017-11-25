----------------------- MODULE nuclear_waste_tracker -----------------------
EXTENDS Integers, TLC
CONSTANTS
    N
    , CONTAINERS
    , PHASES
ASSUME
    N > 0
    
VALUE == -N .. N
MATERIAL == <<"glass", "metal", "plastic", "liquid">>
PHASE == [phase_name: STRING, capacity: Int, expected_materials: {MATERIAL}]
CONTAINER == [material: MATERIAL, radioactivity: Int]
PID == Int
CID == Int
MPR == Int
MCR == Int

VARIABLES
    containers
    , phases
    , pid_to_phase
    , cid_to_container
    , cid_to_pid
    , mpr
    , mcr
vars == <<containers, phases, cid_to_pid>>

-------
\* Invariants
TypeOK ==
    /\ containers \subseteq CONTAINERS
    /\ phases \subseteq PHASES
    /\ pid_to_phase \in [PID -> PHASE]
    /\ cid_to_container \in [CID -> CONTAINER] 
    /\ cid_to_pid \in [CID -> PID]
    /\ mpr \in MPR
    /\ mcr \in MCR
    
-------
\* Actions
new_tracker(_mpr, _mcr) ==
    /\ _mpr \in MPR
    /\ _mcr \in MCR
    /\ _mpr >= 0
    /\ _mcr >= 0
    /\ mpr' = _mpr
    /\ mcr' = _mcr
    /\ UNCHANGED <<containers, phases, pid_to_phase, cid_to_container, cid_to_pid>>

new_phase(pid, phase_name, capacity, expected_materials) ==
    /\ pid \in PID
    /\ phase_name \in PHASES
    /\ capacity \in Int
    /\ expected_materials = {MATERIAL}
    /\ phases' = phases \union phase_name
    /\ pid_to_phase' = [pid_to_phase EXCEPT ![pid].phase_name = phase_name, ![pid].capacity = capacity, ![pid].expected_materials = expected_materials]
    /\ UNCHANGED <<containers, cid_to_container, cid_to_pid>>
-------

=============================================================================
\* Modification History
\* Last modified Sat Nov 25 18:51:16 EST 2017 by mikegin
\* Created Sat Nov 25 16:49:51 EST 2017 by mikegin
