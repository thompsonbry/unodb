--------------------------- MODULE OLCInsert ------------------------------
\* Stage 3: Two writers racing to insert into the same node.
\*
\* Models: 2 writers + 1 node with N slots. Each writer reads version,
\* finds an empty slot, upgrades to write lock, inserts. Only one can
\* succeed; the other must detect the version change and restart.
\*
\* Verifies: no lost updates, mutual exclusion on write lock.

EXTENDS Integers, FiniteSets

CONSTANTS
    N,          \* Number of slots (3)
    MaxVersion  \* Version bound (6)

VARIABLES
    slots,      \* slots[1..N] \in {0, 1} (0=empty, 1=occupied)
    version,    \* Even=unlocked, Odd=locked
    count,      \* Number of occupied slots

    \* Writer 1
    w1pc,       \* idle|read_ver|find_slot|upgrade|write|unlock|done|restart
    w1ver,      \* Cached version
    w1target,   \* Slot writer 1 chose

    \* Writer 2
    w2pc,
    w2ver,
    w2target

vars == <<slots, version, count, w1pc, w1ver, w1target, w2pc, w2ver, w2target>>

Slots == 1..N

-----------------------------------------------------------------------------
Init ==
    /\ slots = [i \in Slots |-> 0]
    /\ version = 0
    /\ count = 0
    /\ w1pc = "idle" /\ w1ver = 0 /\ w1target = 1
    /\ w2pc = "idle" /\ w2ver = 0 /\ w2target = 1

-----------------------------------------------------------------------------
\* WRITER ACTIONS (parameterized by writer ID)

WReadVer(wpc, wver, wpc_, wver_) ==
    /\ wpc = "idle"
    /\ version <= MaxVersion
    /\ count < N              \* only attempt if node not full
    /\ wver_ = version
    /\ wpc_ = "find_slot"

WFindSlot(wpc, wver, wtarget, wpc_, wtarget_) ==
    /\ wpc = "find_slot"
    /\ \E i \in Slots :
        /\ slots[i] = 0      \* find empty slot (reads shared state)
        /\ wtarget_ = i
    /\ wpc_ = "upgrade"

WUpgrade(wpc, wver, wpc_) ==
    /\ wpc = "upgrade"
    /\ IF version = wver /\ version % 2 = 0
       THEN /\ version' = version + 1  \* acquire lock
            /\ wpc_ = "write"
       ELSE /\ wpc_ = "restart"        \* version changed → restart
            /\ UNCHANGED version

WWrite(wpc, wtarget, wpc_) ==
    /\ wpc = "write"
    /\ slots' = [slots EXCEPT ![wtarget] = 1]
    /\ count' = count + 1
    /\ wpc_ = "unlock"

WUnlock(wpc, wpc_) ==
    /\ wpc = "unlock"
    /\ version' = version + 1  \* release lock (even)
    /\ wpc_ = "done"

WRestart(wpc, wpc_) ==
    /\ wpc = "restart"
    /\ wpc_ = "idle"

\* Writer 1 actions
W1ReadVer == WReadVer(w1pc, w1ver, w1pc', w1ver') /\ UNCHANGED <<slots, version, count, w1target, w2pc, w2ver, w2target>>
W1FindSlot == WFindSlot(w1pc, w1ver, w1target, w1pc', w1target') /\ UNCHANGED <<slots, version, count, w1ver, w2pc, w2ver, w2target>>
W1Upgrade == WUpgrade(w1pc, w1ver, w1pc') /\ UNCHANGED <<slots, count, w1ver, w1target, w2pc, w2ver, w2target>>
W1Write == WWrite(w1pc, w1target, w1pc') /\ UNCHANGED <<version, w1ver, w1target, w2pc, w2ver, w2target>>
W1Unlock == WUnlock(w1pc, w1pc') /\ UNCHANGED <<slots, count, w1ver, w1target, w2pc, w2ver, w2target>>
W1Restart == WRestart(w1pc, w1pc') /\ UNCHANGED <<slots, version, count, w1ver, w1target, w2pc, w2ver, w2target>>

\* Writer 2 actions
W2ReadVer == WReadVer(w2pc, w2ver, w2pc', w2ver') /\ UNCHANGED <<slots, version, count, w2target, w1pc, w1ver, w1target>>
W2FindSlot == WFindSlot(w2pc, w2ver, w2target, w2pc', w2target') /\ UNCHANGED <<slots, version, count, w2ver, w1pc, w1ver, w1target>>
W2Upgrade == WUpgrade(w2pc, w2ver, w2pc') /\ UNCHANGED <<slots, count, w2ver, w2target, w1pc, w1ver, w1target>>
W2Write == WWrite(w2pc, w2target, w2pc') /\ UNCHANGED <<version, w2ver, w2target, w1pc, w1ver, w1target>>
W2Unlock == WUnlock(w2pc, w2pc') /\ UNCHANGED <<slots, count, w2ver, w2target, w1pc, w1ver, w1target>>
W2Restart == WRestart(w2pc, w2pc') /\ UNCHANGED <<slots, version, count, w2ver, w2target, w1pc, w1ver, w1target>>

-----------------------------------------------------------------------------
Step ==
    \/ W1ReadVer \/ W1FindSlot \/ W1Upgrade \/ W1Write \/ W1Unlock \/ W1Restart
    \/ W2ReadVer \/ W2FindSlot \/ W2Upgrade \/ W2Write \/ W2Unlock \/ W2Restart

Spec == Init /\ [][Step]_vars

-----------------------------------------------------------------------------
\* INVARIANTS

\* Mutual exclusion: at most one writer holds the lock
MutualExclusion ==
    ~(w1pc \in {"write", "unlock"} /\ w2pc \in {"write", "unlock"})

\* Count consistency: count equals actual occupied slots
CountConsistency ==
    count = Cardinality({i \in Slots : slots[i] = 1})

\* No lost update: if both target same slot and both reach "done",
\* the slot is occupied (trivially true since write sets it to 1).
\* The real property: a writer in "write" state has exclusive access.
ExclusiveWrite ==
    (w1pc = "write" => version % 2 = 1) /\
    (w2pc = "write" => version % 2 = 1)

=============================================================================
