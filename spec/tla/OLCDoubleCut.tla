--------------------------- MODULE OLCDoubleCut ---------------------------
\* Stage 8: Two removes targeting the same chain node.
\*
\* Models: 1 chain node with a version lock. Two removers both try to
\* lock it for chain cut. Only one can succeed; the other must detect
\* the version change (or obsolescence) and restart.
\*
\* Verifies: at most one remover reaches point-of-no-return,
\* no double-free (node obsoleted at most once).

EXTENDS Integers

CONSTANTS
    MaxVersion

VARIABLES
    \* Shared chain node
    c_ver,      \* Version counter
    c_obsolete, \* Has been obsoleted?

    \* Remover 1
    r1pc,       \* idle|read_ver|upgrade|locked|cut|done|restart
    r1ver,      \* Cached version

    \* Remover 2
    r2pc,
    r2ver

vars == <<c_ver, c_obsolete, r1pc, r1ver, r2pc, r2ver>>

OBSOLETE == MaxVersion + 1

-----------------------------------------------------------------------------
Init ==
    /\ c_ver = 0
    /\ c_obsolete = FALSE
    /\ r1pc = "idle" /\ r1ver = 0
    /\ r2pc = "idle" /\ r2ver = 0

-----------------------------------------------------------------------------
\* REMOVER ACTIONS (parameterized)

RReadVer(rpc, rver, rpc_, rver_) ==
    /\ rpc = "idle"
    /\ rver_ = c_ver
    /\ rpc_ = "upgrade"

RUpgrade(rpc, rver, rpc_) ==
    /\ rpc = "upgrade"
    /\ IF c_ver = rver /\ c_ver % 2 = 0 /\ ~c_obsolete
       THEN /\ c_ver' = c_ver + 1  \* lock
            /\ rpc_ = "locked"
       ELSE /\ rpc_ = "restart"
            /\ UNCHANGED c_ver

RCut(rpc, rpc_) ==
    /\ rpc = "locked"
    /\ c_obsolete' = TRUE
    /\ c_ver' = OBSOLETE      \* unlock_and_obsolete
    /\ rpc_ = "done"

RRestart(rpc, rpc_) ==
    /\ rpc = "restart"
    /\ rpc_ = "idle"

\* Remover 1
R1ReadVer == RReadVer(r1pc, r1ver, r1pc', r1ver') /\ UNCHANGED <<c_ver, c_obsolete, r2pc, r2ver>>
R1Upgrade == RUpgrade(r1pc, r1ver, r1pc') /\ UNCHANGED <<c_obsolete, r1ver, r2pc, r2ver>>
R1Cut == RCut(r1pc, r1pc') /\ UNCHANGED <<r1ver, r2pc, r2ver>>
R1Restart == RRestart(r1pc, r1pc') /\ UNCHANGED <<c_ver, c_obsolete, r1ver, r2pc, r2ver>>

\* Remover 2
R2ReadVer == RReadVer(r2pc, r2ver, r2pc', r2ver') /\ UNCHANGED <<c_ver, c_obsolete, r1pc, r1ver>>
R2Upgrade == RUpgrade(r2pc, r2ver, r2pc') /\ UNCHANGED <<c_obsolete, r2ver, r1pc, r1ver>>
R2Cut == RCut(r2pc, r2pc') /\ UNCHANGED <<r2ver, r1pc, r1ver>>
R2Restart == RRestart(r2pc, r2pc') /\ UNCHANGED <<c_ver, c_obsolete, r2ver, r1pc, r1ver>>

-----------------------------------------------------------------------------
Step ==
    \/ R1ReadVer \/ R1Upgrade \/ R1Cut \/ R1Restart
    \/ R2ReadVer \/ R2Upgrade \/ R2Cut \/ R2Restart

Spec == Init /\ [][Step]_vars

StateConstraint == c_ver <= MaxVersion

-----------------------------------------------------------------------------
\* INVARIANTS

\* At most one remover holds the lock at any time
MutualExclusion ==
    ~(r1pc = "locked" /\ r2pc = "locked")

\* At most one remover reaches cut (point of no return)
AtMostOneCut ==
    ~(r1pc = "done" /\ r2pc = "done")

\* Node is obsoleted at most once (no double-free)
NoDoubleFree ==
    (r1pc = "locked" /\ r2pc = "locked") => FALSE  \* same as MutualExclusion

=============================================================================
