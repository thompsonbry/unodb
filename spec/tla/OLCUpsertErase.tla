------------------------- MODULE OLCUpsertErase -------------------------
(* Stage 9: Upsert-erase CAS protocol — version-validated positioned erase.

   Models the critical interleaving: an upserter finds a duplicate key,
   the lambda observes the current value and returns "erase". The upserter
   must release its optimistic read locks, re-traverse, and remove the
   value — but ONLY if the value hasn't changed since the lambda observed it.

   Hazard H9: Between releasing RCS and re-acquiring write locks, a
   concurrent writer can change the value. The version counter must detect
   this and force the upserter to retry (re-observe, re-invoke lambda).

   Key CAS invariant: if the upserter successfully erases, the value at
   the moment of erasure == the value the lambda observed.

   Processes:
   - 1 upserter: observe → lambda(erase) → release → retraverse → validate → remove|retry
   - 1 concurrent writer: can change the value at any time (models insert/update/other-upsert)
*)

EXTENDS Naturals

CONSTANTS Values, Empty
  (* Values = {V1, V2} — the domain of possible values at this key.
     Empty — sentinel indicating the key has been erased. Must not be in Values. *)

ASSUME Empty \notin Values

VARIABLES
    (* --- Shared node state --- *)
    value,          \* current value at the key (or Empty if erased)
    version,        \* OLC version counter (even=unlocked, odd=write-locked)

    (* --- Upserter state --- *)
    upc,            \* upserter program counter
    u_observed,     \* value the lambda saw
    u_obs_ver,      \* version when the lambda observed the value

    (* --- Concurrent writer state --- *)
    wpc,            \* writer program counter
    w_new_val       \* value the writer will install

vars == <<value, version, upc, u_observed, u_obs_ver, wpc, w_new_val>>

TypeOK ==
    /\ value \in Values \cup {Empty}
    /\ version \in Nat
    /\ upc \in {"idle", "observed", "released", "retraversing",
                "validate", "write_locked", "erased", "done"}
    /\ u_observed \in Values \cup {Empty}
    /\ u_obs_ver \in Nat
    /\ wpc \in {"idle", "locked", "written", "done"}
    /\ w_new_val \in Values

Init ==
    /\ value \in Values          \* key exists with some value
    /\ version = 0
    /\ upc = "idle"
    /\ u_observed = Empty
    /\ u_obs_ver = 0
    /\ wpc = "idle"
    /\ w_new_val \in Values

(* ================================================================== *)
(* --- Upserter actions ---                                           *)
(*                                                                    *)
(* Protocol: find duplicate → read value under RCS → lambda returns   *)
(* erase → release RCS → re-traverse → try upgrade → validate        *)
(* version → if match: erase; if mismatch: retry from idle.           *)
(* ================================================================== *)

(* Step 1: Upserter finds the key and observes value under RCS.
   Precondition: node is not write-locked (version is even) and key exists. *)
UObserve ==
    /\ upc = "idle"
    /\ version % 2 = 0
    /\ value # Empty             \* key must exist to observe
    /\ u_observed' = value
    /\ u_obs_ver' = version
    /\ upc' = "observed"
    /\ UNCHANGED <<value, version, wpc, w_new_val>>

(* Step 2: Lambda returns "erase". Upserter releases RCS.
   This is the critical moment — after this, the value can change. *)
URelease ==
    /\ upc = "observed"
    /\ upc' = "released"
    /\ UNCHANGED <<value, version, u_observed, u_obs_ver, wpc, w_new_val>>

(* Step 3: Re-traverse from root. Arrives at the node.
   Models the re-traversal as a single step (we don't model tree structure,
   only the lock protocol at the target node). *)
URetraverse ==
    /\ upc = "released"
    /\ upc' = "retraversing"
    /\ UNCHANGED <<value, version, u_observed, u_obs_ver, wpc, w_new_val>>

(* Step 4: Attempt to upgrade to write lock (acquire parent + node).
   Can only succeed if version is even (no one else holds write lock).
   If the node is currently write-locked, must restart. *)
UValidate ==
    /\ upc = "retraversing"
    /\ version % 2 = 0          \* can acquire write lock
    /\ IF u_obs_ver = version
       THEN                      \* Version matches — value unchanged, proceed
            /\ version' = version + 1   \* acquire write lock (odd)
            /\ upc' = "write_locked"
       ELSE                      \* Version mismatch — value may have changed, retry
            /\ upc' = "idle"
            /\ UNCHANGED version
    /\ UNCHANGED <<value, u_observed, u_obs_ver, wpc, w_new_val>>

(* Step 4b: Upserter arrives at node but it's write-locked. Restart.
   Models the case where try_upgrade fails because writer holds the lock. *)
URestartOnLocked ==
    /\ upc = "retraversing"
    /\ version % 2 = 1          \* write-locked by someone else
    /\ upc' = "idle"
    /\ UNCHANGED <<value, version, u_observed, u_obs_ver, wpc, w_new_val>>

(* Step 5: Erase the value (under write lock). *)
UErase ==
    /\ upc = "write_locked"
    /\ value' = Empty
    /\ upc' = "erased"
    /\ UNCHANGED <<version, u_observed, u_obs_ver, wpc, w_new_val>>

(* Step 6: Unlock (version becomes even again). *)
UUnlock ==
    /\ upc = "erased"
    /\ version' = version + 1   \* even = unlocked
    /\ upc' = "done"
    /\ UNCHANGED <<value, u_observed, u_obs_ver, wpc, w_new_val>>

(* Step 7: Upserter cycles back to idle (models repeated upsert calls). *)
UDone ==
    /\ upc = "done"
    /\ upc' = "idle"
    /\ UNCHANGED <<value, version, u_observed, u_obs_ver, wpc, w_new_val>>

(* ================================================================== *)
(* --- Concurrent writer actions ---                                  *)
(*                                                                    *)
(* Models any concurrent mutation: another upsert-update, a standalone *)
(* insert (re-inserting after erase), or another upsert-erase.        *)
(* ================================================================== *)

(* Writer acquires write lock. *)
WLock ==
    /\ wpc = "idle"
    /\ version % 2 = 0
    /\ version' = version + 1
    /\ wpc' = "locked"
    /\ UNCHANGED <<value, upc, u_observed, u_obs_ver, w_new_val>>

(* Writer changes the value (or re-inserts after erase). *)
WWrite ==
    /\ wpc = "locked"
    /\ value' = w_new_val
    /\ wpc' = "written"
    /\ UNCHANGED <<version, upc, u_observed, u_obs_ver, w_new_val>>

(* Writer unlocks. *)
WUnlock ==
    /\ wpc = "written"
    /\ version' = version + 1
    /\ wpc' = "done"
    /\ UNCHANGED <<value, upc, u_observed, u_obs_ver, w_new_val>>

(* Writer cycles back (models repeated concurrent mutations). *)
WDone ==
    /\ wpc = "done"
    /\ w_new_val' \in Values     \* pick a new value for next write
    /\ wpc' = "idle"
    /\ UNCHANGED <<value, version, upc, u_observed, u_obs_ver>>

(* ================================================================== *)
(* --- Specification ---                                              *)
(* ================================================================== *)

Step ==
    \/ UObserve \/ URelease \/ URetraverse \/ UValidate
    \/ URestartOnLocked \/ UErase \/ UUnlock \/ UDone
    \/ WLock \/ WWrite \/ WUnlock \/ WDone

Spec == Init /\ [][Step]_vars /\ WF_vars(Step)

(* ================================================================== *)
(* --- Safety Properties ---                                          *)
(* ================================================================== *)

(* CAS SAFETY: The core invariant. If the upserter is about to erase
   (holds write lock, about to set value=Empty), then the current value
   MUST be the value the lambda observed. No stale-assumption erase. *)
CASSafety ==
    upc = "write_locked" => value = u_observed

(* MUTUAL EXCLUSION: Upserter and writer never both hold write lock. *)
MutualExclusion ==
    ~(upc = "write_locked" /\ wpc = "locked")
    /\ ~(upc = "write_locked" /\ wpc = "written")
    /\ ~(upc = "erased" /\ wpc = "locked")
    /\ ~(upc = "erased" /\ wpc = "written")

(* VERSION CONSISTENCY: version is odd iff exactly one process holds
   the write lock. *)
VersionConsistency ==
    version % 2 = 1 <=>
        ( upc \in {"write_locked", "erased"}
        \/ wpc \in {"locked", "written"} )

(* NO ERASE OF EMPTY: upserter never erases an already-empty slot. *)
NoEraseOfEmpty ==
    upc = "write_locked" => value # Empty

(* ================================================================== *)
(* --- Liveness Properties ---                                        *)
(* ================================================================== *)

(* PROGRESS: Under weak fairness, the upserter eventually reaches "done"
   or "erased" — it doesn't loop forever. Note: this requires the writer
   to eventually stop (otherwise the upserter can be starved). We check
   this as a temporal property, not an invariant. *)
UpsertProgress == <>(upc = "done")

(* State constraint to keep version counter bounded for model checking. *)
StateConstraint == version <= 10

=========================================================================
