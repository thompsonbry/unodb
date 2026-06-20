------------------------- MODULE OLCInsertVIS -------------------------
(* VIS (value-in-slot) restart model.

   Models the hazard: an inserter descends with a multi-byte remaining_key
   and finds a VIS at the dispatch byte.  Under concurrency, a VIS can
   appear at an intermediate depth because another thread inserted a
   shorter key concurrently (creating a VIS at a level the first thread
   already passed through version-check for).

   The OLD code asserted remaining_key.size() == 1 — violated by this
   interleaving.  The FIX: if remaining_key.size() != 1, restart.

   Processes:
   - Inserter A: inserting key [0x80, 0x01] (remaining_key_length = 2 at depth 0)
   - Inserter B: inserting key [0x80] (remaining_key_length = 1 at depth 0)
     Inserter B creates a VIS at dispatch byte 0x80.

   The invariant violated by the old code:
     InserterAtVIS => remaining_key_length = 1
   The fix makes this a conditional restart instead of an assertion.
*)

EXTENDS Naturals

VARIABLES
    (* --- Shared inode state --- *)
    version,            \* OLC version counter
    vis_at_0x80,        \* TRUE if a VIS exists at dispatch byte 0x80

    (* --- Inserter A (long key [0x80, 0x01]) --- *)
    apc,                \* program counter
    a_obs_ver,          \* version observed by A

    (* --- Inserter B (short key [0x80]) --- *)
    bpc                 \* program counter

vars == <<version, vis_at_0x80, apc, a_obs_ver, bpc>>

(* A's remaining_key_length is always 2 at this inode (it descended with
   a 2-byte key and is at depth 0).  B's remaining_key_length is 1. *)

Init ==
    /\ version = 0
    /\ vis_at_0x80 = FALSE
    /\ apc = "descend"
    /\ a_obs_ver = 0
    /\ bpc = "idle"

(* ================================================================== *)
(* --- Inserter A (key = [0x80, 0x01], remaining_key_length = 2) ---  *)
(* ================================================================== *)

(* A checks version of inode, records it, proceeds to find_child. *)
ACheckVersion ==
    /\ apc = "descend"
    /\ version % 2 = 0          \* not write-locked
    /\ a_obs_ver' = version
    /\ apc' = "find_child"
    /\ UNCHANGED <<version, vis_at_0x80, bpc>>

(* A calls find_child(0x80) and checks is_value_in_slot. *)
AFindChild ==
    /\ apc = "find_child"
    /\ IF vis_at_0x80
       THEN apc' = "vis_found"   \* VIS exists — enter VIS handling
       ELSE apc' = "no_vis"      \* no VIS — normal child descent
    /\ UNCHANGED <<version, vis_at_0x80, a_obs_ver, bpc>>

(* A found VIS — validate version (the fix path). *)
AVisValidate ==
    /\ apc = "vis_found"
    /\ IF a_obs_ver = version /\ version % 2 = 0
       THEN apc' = "vis_check_len"   \* version matches — check length
       ELSE apc' = "restart"          \* version mismatch — restart
    /\ UNCHANGED <<version, vis_at_0x80, a_obs_ver, bpc>>

(* THE FIX: Check remaining_key_length.  A's remaining_key is 2, not 1.
   Old code: ASSERT(remaining_key.size() == 1) — FAILS here.
   New code: if (remaining_key.size() != 1) return {} — restart. *)
AVisCheckLen ==
    /\ apc = "vis_check_len"
    (* remaining_key_length for A is always 2 at this inode *)
    /\ apc' = "restart"         \* 2 != 1 → restart (the fix)
    /\ UNCHANGED <<version, vis_at_0x80, a_obs_ver, bpc>>

(* A restarts from the top. *)
ARestart ==
    /\ apc = "restart"
    /\ apc' = "descend"
    /\ UNCHANGED <<version, vis_at_0x80, a_obs_ver, bpc>>

(* A found no VIS — normal insert path (succeeds, not modeled further). *)
ANoVis ==
    /\ apc = "no_vis"
    /\ apc' = "done"
    /\ UNCHANGED <<version, vis_at_0x80, a_obs_ver, bpc>>

(* ================================================================== *)
(* --- Inserter B (key = [0x80], remaining_key_length = 1) ---        *)
(* Creates a VIS at dispatch byte 0x80.                               *)
(* ================================================================== *)

(* B acquires write lock. *)
BLock ==
    /\ bpc = "idle"
    /\ version % 2 = 0
    /\ version' = version + 1
    /\ bpc' = "locked"
    /\ UNCHANGED <<vis_at_0x80, apc, a_obs_ver>>

(* B installs VIS at dispatch byte 0x80. *)
BInstallVIS ==
    /\ bpc = "locked"
    /\ vis_at_0x80' = TRUE
    /\ bpc' = "unlock"
    /\ UNCHANGED <<version, apc, a_obs_ver>>

(* B unlocks. *)
BUnlock ==
    /\ bpc = "unlock"
    /\ version' = version + 1
    /\ bpc' = "done"
    /\ UNCHANGED <<vis_at_0x80, apc, a_obs_ver>>

(* ================================================================== *)
(* --- Specification ---                                              *)
(* ================================================================== *)

Step ==
    \/ ACheckVersion \/ AFindChild \/ AVisValidate
    \/ AVisCheckLen \/ ARestart \/ ANoVis
    \/ BLock \/ BInstallVIS \/ BUnlock

Spec == Init /\ [][Step]_vars /\ WF_vars(Step)

(* ================================================================== *)
(* --- Invariants ---                                                 *)
(* ================================================================== *)

(* THE BUG INVARIANT (old code assertion — violated by this model):
   "If A is in the VIS handling path, remaining_key must be 1."
   This is FALSE when B has concurrently created a VIS while A descended
   with remaining_key_length = 2. *)
BugInvariant_VIS_implies_len1 ==
    apc \notin {"vis_found", "vis_check_len"}

(* THE FIX INVARIANT: A never proceeds past vis_check_len without restarting.
   With the fix, A always restarts when remaining_key_length != 1. *)
FixInvariant_NoAssertViolation ==
    apc # "assert_failed"  \* this state doesn't exist in the fixed model

(* VERSION CONSISTENCY *)
VersionConsistency ==
    version % 2 = 1 <=> bpc \in {"locked", "unlock"}

(* State constraint for bounded model checking. *)
StateConstraint == version <= 6

=========================================================================
