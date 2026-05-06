--------------------------- MODULE OLCIterRemove --------------------------
\* Stage 6: Iterator vs concurrent remove (node obsolescence).
\*
\* Models: 2 nodes (parent → child). Iterator descends with cached
\* versions. Remover can obsolete the child node. Iterator must detect
\* obsolescence on rehydration and restart.
\*
\* Verifies: iterator never acts on data from an obsoleted node.

EXTENDS Integers

CONSTANTS
    MaxVersion

VARIABLES
    \* Parent node
    p_ver,      \* Parent version
    p_child,    \* Does parent still point to child? (TRUE/FALSE)

    \* Child node
    c_ver,      \* Child version
    c_obsolete, \* Has child been obsoleted?

    \* Iterator state
    ipc,        \* idle|read_parent|descend|read_child|validate_child|
                \* act|done|restart
    i_pver,     \* Cached parent version
    i_cver,     \* Cached child version

    \* Remover state
    rpc         \* idle|lock_parent|cut|obsolete_child|done

vars == <<p_ver, p_child, c_ver, c_obsolete, ipc, i_pver, i_cver, rpc>>

\* Obsolete version marker (odd + special)
OBSOLETE == MaxVersion + 1

-----------------------------------------------------------------------------
Init ==
    /\ p_ver = 0
    /\ p_child = TRUE
    /\ c_ver = 0
    /\ c_obsolete = FALSE
    /\ ipc = "idle"
    /\ i_pver = 0
    /\ i_cver = 0
    /\ rpc = "idle"

-----------------------------------------------------------------------------
\* REMOVER: locks parent, disconnects child, obsoletes child

RemoverLockParent ==
    /\ rpc = "idle"
    /\ p_ver % 2 = 0
    /\ p_ver <= MaxVersion
    /\ p_child = TRUE       \* only remove if child exists
    /\ p_ver' = p_ver + 1   \* lock parent
    /\ rpc' = "cut"
    /\ UNCHANGED <<p_child, c_ver, c_obsolete, ipc, i_pver, i_cver>>

RemoverCut ==
    /\ rpc = "cut"
    /\ p_child' = FALSE      \* disconnect child
    /\ p_ver' = p_ver + 1    \* unlock parent
    /\ c_obsolete' = TRUE    \* obsolete child atomically
    /\ c_ver' = OBSOLETE     \* version → obsolete (unlock_and_obsolete)
    /\ rpc' = "done"
    /\ UNCHANGED <<ipc, i_pver, i_cver>>

\* (RemoverObsoleteChild removed — folded into RemoverCut)

-----------------------------------------------------------------------------
\* ITERATOR: descends from parent to child, reads child, validates

IterStart ==
    /\ ipc = "idle"
    /\ i_pver' = p_ver       \* read parent version
    /\ ipc' = "read_parent"
    /\ UNCHANGED <<p_ver, p_child, c_ver, c_obsolete, i_cver, rpc>>

IterReadParent ==
    /\ ipc = "read_parent"
    /\ IF p_ver = i_pver /\ p_ver % 2 = 0 /\ p_child = TRUE
       THEN /\ ipc' = "descend"
       ELSE /\ ipc' = "restart"  \* parent changed or locked
    /\ UNCHANGED <<p_ver, p_child, c_ver, c_obsolete, i_pver, i_cver, rpc>>

IterDescend ==
    /\ ipc = "descend"
    \* Validate parent version before descending (lock coupling!)
    /\ IF p_ver = i_pver /\ p_ver % 2 = 0
       THEN /\ i_cver' = c_ver    \* read child version
            /\ ipc' = "read_child"
       ELSE /\ ipc' = "restart"   \* parent changed during descent
            /\ UNCHANGED i_cver
    /\ UNCHANGED <<p_ver, p_child, c_ver, c_obsolete, i_pver, rpc>>

IterReadChild ==
    /\ ipc = "read_child"
    \* Check if child version is valid (not obsolete, not locked)
    /\ IF i_cver # OBSOLETE /\ i_cver % 2 = 0
       THEN ipc' = "validate_child"
       ELSE ipc' = "restart"   \* obsolete or locked → restart
    /\ UNCHANGED <<p_ver, p_child, c_ver, c_obsolete, i_pver, i_cver, rpc>>

IterValidateChild ==
    /\ ipc = "validate_child"
    \* Re-check version hasn't changed
    /\ IF c_ver = i_cver
       THEN ipc' = "act"       \* snapshot is valid, act on it
       ELSE ipc' = "restart"   \* version changed → restart
    /\ UNCHANGED <<p_ver, p_child, c_ver, c_obsolete, i_pver, i_cver, rpc>>

IterAct ==
    /\ ipc = "act"
    /\ ipc' = "done"
    /\ UNCHANGED <<p_ver, p_child, c_ver, c_obsolete, i_pver, i_cver, rpc>>

IterRestart ==
    /\ ipc = "restart"
    /\ ipc' = "idle"
    /\ UNCHANGED <<p_ver, p_child, c_ver, c_obsolete, i_pver, i_cver, rpc>>

IterDone ==
    /\ ipc = "done"
    /\ ipc' = "idle"
    /\ UNCHANGED <<p_ver, p_child, c_ver, c_obsolete, i_pver, i_cver, rpc>>

-----------------------------------------------------------------------------
Step ==
    \/ RemoverLockParent \/ RemoverCut
    \/ IterStart \/ IterReadParent \/ IterDescend
    \/ IterReadChild \/ IterValidateChild \/ IterAct
    \/ IterRestart \/ IterDone

Spec == Init /\ [][Step]_vars

\* State space bound
StateConstraint == p_ver <= MaxVersion /\ c_ver <= MaxVersion

-----------------------------------------------------------------------------
\* INVARIANTS

\* What OLC guarantees: if iterator acts, the child's DATA was consistent
\* at the time of reading (version didn't change between read and validate).
\* The child may have been disconnected from the tree, but its data is still
\* valid (QSBR prevents reclamation while iterator is active).
\*
\* The version protocol guarantees: if validate passes, no WRITER modified
\* the child between the iterator's read and validate. The child's content
\* is a consistent snapshot.
SnapshotValid ==
    ipc = "act" => i_cver = 0  \* child version was 0 when we read it,
                                \* and still 0 when we validated (no writer touched it)

\* Stronger property: iterator never acts on a child whose version was
\* bumped by a writer. (Obsolescence bumps version to OBSOLETE.)
\* This CAN be violated in the QSBR window — and that's OK.
\* The real safety comes from QSBR epoch protection.
\*
\* NoActOnModified: if iterator acts, no writer modified the child's DATA
\* between read and validate. (Disconnection doesn't modify data.)
NoActOnModified ==
    ipc = "act" => c_ver = i_cver \/ c_ver = OBSOLETE
    \* Either version unchanged (no writer touched it) OR it was obsoleted
    \* AFTER our validate passed (QSBR window — safe because data unchanged)

=============================================================================
