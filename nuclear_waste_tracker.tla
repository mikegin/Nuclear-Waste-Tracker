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
          , container_count: Int
          , current_rad: VALUE
          ]
          
\* set of all container records
CONTAINER ==  [ material: MATERIAL
              , radioactivity: VALUE
              ] 
VARIABLES
    PID \* registered phases
    , CID  \* registered containers
    , containers \* mapping of cid's to container attributes
    , phases \* mapping of pid's to phase attributes
    , container_phase \* mapping of cid's to pid's
    , maximum_phase_radiation \* max phase radiation
    , maximum_container_radiation \* max container radiation
    
-------
\* Helpers
Range(f) ==
    {f[x] : x \in DOMAIN f}

RangeRes(f, S) ==
    [x \in {z \in DOMAIN f: f[z] \in S} |-> f[x]]

DomainRes(f, S) ==
    [x \in (S \intersect DOMAIN f) |-> f[x]]
    
DomainSub(f, S) ==
    [x \in DOMAIN f \ S |-> f[x]]


RECURSIVE SetSum(_)
SetSum(S) ==
    IF S = {}
    THEN 0
    ELSE LET x == CHOOSE x \in S : TRUE
         IN  x + SetSum(S \ {x})

-------
\* Invariants

TypeOK == \* Well Definedness
    /\ PID \subseteq U_PID
    /\ CID \subseteq U_CID
    /\ containers \in [CID -> CONTAINER]
    /\ phases \in [PID -> PHASE]
    /\ container_phase \in [CID -> PID]
    /\ maximum_phase_radiation \in VALUE
    /\ maximum_container_radiation \in VALUE
    


\* consistent variables == (dom containers = dom container_phase) /\ (dom phases = range container_phase)

\* Sum of all radiations of containers in a phase equals current_rad
\* \A pid \in DOMAIN phases, SUM({\A cid \in DOMAIN RangeResBy(container_phase, {pid}), containers[cid].radioactivity}) = phases[pid].current_rad
\*ConsistentCurrentRad ==
\*    (\A pid \in DOMAIN phases : SetSum({containers[cid].radioactivity : cid \in DOMAIN RangeRes(container_phase, pid)}) = phases[pid].current_rad)

\* Current_rad <= maximum_phase_radiation
CurrentRadCorrect ==
    (\A p \in Range(phases) : p.current_rad <= maximum_phase_radiation)

\* Every container has radiation <= maximum_container_radiation

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
                         , container_count |-> 0
                         , current_rad |-> 0
                         ]
    /\ UNCHANGED <<CID, containers, container_phase, maximum_phase_radiation, maximum_container_radiation>>
\*    /\ Print (Range(phases'), TRUE)

new_container(cid, c, pid) ==
    /\ cid \in U_CID
    /\ cid \notin CID
    /\ pid \in PID
    /\ c \in CONTAINER
    /\ c.material \in phases[pid].expected_materials
    /\ c.radioactivity \in VALUE
    /\ c.radioactivity > 0
    /\ c.radioactivity <= maximum_container_radiation
    /\ c.radioactivity + phases[pid].current_rad <= maximum_phase_radiation
    /\ phases[pid].container_count < phases[pid].capacity
    /\ CID' = CID \union {cid}
    /\ containers' = containers @@ cid :> c
    /\ phases' = [phases EXCEPT ![pid].current_rad = @ + c.radioactivity, ![pid].container_count = @ + 1]
    /\ container_phase' = container_phase @@ cid :> pid
    /\ UNCHANGED <<PID, maximum_phase_radiation, maximum_container_radiation>>

remove_phase(pid) ==
    /\ pid \in PID
    /\ Cardinality(CID) = 0
    /\ PID' = PID \ {pid}
    /\ phases' = DomainSub(phases, {pid})
    /\ UNCHANGED <<CID, containers, container_phase, maximum_phase_radiation, maximum_container_radiation>>
    
remove_container(cid) ==
    /\ cid \in CID
    /\ containers' = DomainSub(containers, {cid})
    /\ container_phase' = DomainSub(container_phase, {cid})
    /\ CID' = CID \ {cid}
    
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
    \/ (\E   cid \in U_CID
           , c \in CONTAINER
           , pid \in U_PID
                : new_container(cid, c, pid))
        
=============================================================================
\* Modification History
\* Last modified Tue Dec 12 19:07:06 EST 2017 by mikegin
\* Created Sat Nov 25 16:49:51 EST 2017 by mikegin
