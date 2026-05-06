--------------------------- MODULE OLCChainCut ----------------------------
\* Stage 5: Chain cut with cut_point_parent evaluation (Cases A/B/C).
\*
\* Models: parent → chain_node → leaf. Remover locks chain bottom-up,
\* then evaluates parent (CPP). Inserter can add children to parent
\* or chain_node concurrently.
\*
\* Verifies: Cases A/B/C are correctly handled, no cut on stale view.

EXTENDS Integers

CONSTANTS
    MaxVersion

VARIABLES
    \* Parent node
    p_count,    \* Number of children in parent (1..3)
    p_child,    \* Does parent still point to chain? (TRUE/FALSE)
    p_ver,      \* Parent version

    \* Chain node (single I4 between parent and leaf)
    c_count,    \* Children count (1 or 2)
    c_ver,      \* Chain node version

    \* Remover state
    rpc,        \* idle|lock_chain|read_parent|validate_parent|
                \* case_a|case_b|case_c|cut|done|restart
    r_pver,     \* Cached parent version
    r_p_count,  \* Cached parent count
    r_p_child,  \* Cached parent-has-child
    r_chain_locked, \* Has remover locked the chain node?
    r_cut_level,    \* 0=cut at chain, 1=cut at parent (Case B)

    \* Inserter state
    ipc,        \* idle|choose|lock_p|write_p|unlock_p|lock_c|write_c|unlock_c|done
    i_target    \* "parent" or "chain"

vars == <<p_count, p_child, p_ver, c_count, c_ver,
          rpc, r_pver, r_p_count, r_p_child, r_chain_locked, r_cut_level,
          ipc, i_target>>

-----------------------------------------------------------------------------
Init ==
    /\ p_count = 2     \* parent has 2 children (chain + one other)
    /\ p_child = TRUE  \* parent points to chain
    /\ p_ver = 0
    /\ c_count = 1     \* chain node has 1 child (the leaf)
    /\ c_ver = 0
    /\ rpc = "idle"
    /\ r_pver = 0 /\ r_p_count = 0 /\ r_p_child = FALSE
    /\ r_chain_locked = FALSE /\ r_cut_level = 0
    /\ ipc = "idle" /\ i_target = "parent"

-----------------------------------------------------------------------------
\* INSERTER: can add a child to parent or chain node

InsertChoose ==
    /\ ipc = "idle"
    /\ \E t \in {"parent", "chain"} :
        /\ (t = "parent" => p_count < 3)
        /\ (t = "chain" => c_count < 2)
        /\ i_target' = t
    /\ ipc' = "lock_target"
    /\ UNCHANGED <<p_count, p_child, p_ver, c_count, c_ver,
                   rpc, r_pver, r_p_count, r_p_child, r_chain_locked, r_cut_level>>

InsertLockTarget ==
    /\ ipc = "lock_target"
    /\ IF i_target = "parent"
       THEN /\ p_ver % 2 = 0 /\ p_ver <= MaxVersion
            /\ p_ver' = p_ver + 1
            /\ UNCHANGED c_ver
       ELSE /\ c_ver % 2 = 0 /\ c_ver <= MaxVersion
            /\ c_ver' = c_ver + 1
            /\ UNCHANGED p_ver
    /\ ipc' = "write_target"
    /\ UNCHANGED <<p_count, p_child, c_count,
                   rpc, r_pver, r_p_count, r_p_child, r_chain_locked, r_cut_level, i_target>>

InsertWriteTarget ==
    /\ ipc = "write_target"
    /\ IF i_target = "parent"
       THEN /\ p_count' = p_count + 1
            /\ UNCHANGED c_count
       ELSE /\ c_count' = c_count + 1
            /\ UNCHANGED p_count
    /\ ipc' = "unlock_target"
    /\ UNCHANGED <<p_child, p_ver, c_ver,
                   rpc, r_pver, r_p_count, r_p_child, r_chain_locked, r_cut_level, i_target>>

InsertUnlockTarget ==
    /\ ipc = "unlock_target"
    /\ IF i_target = "parent"
       THEN /\ p_ver' = p_ver + 1
            /\ UNCHANGED c_ver
       ELSE /\ c_ver' = c_ver + 1
            /\ UNCHANGED p_ver
    /\ ipc' = "done"
    /\ UNCHANGED <<p_count, p_child, c_count,
                   rpc, r_pver, r_p_count, r_p_child, r_chain_locked, r_cut_level, i_target>>

-----------------------------------------------------------------------------
\* REMOVER: lock chain, then evaluate parent (CPP)

RemoverStart ==
    /\ rpc = "idle"
    /\ rpc' = "lock_chain"
    /\ r_chain_locked' = FALSE
    /\ r_cut_level' = 0
    /\ UNCHANGED <<p_count, p_child, p_ver, c_count, c_ver,
                   r_pver, r_p_count, r_p_child, ipc, i_target>>

\* Lock the chain node (simplified: try upgrade)
RemoverLockChain ==
    /\ rpc = "lock_chain"
    /\ IF c_ver % 2 = 0 /\ c_count = 1  \* unlocked AND still single-child
       THEN /\ c_ver' = c_ver + 1        \* lock it
            /\ r_chain_locked' = TRUE
            /\ rpc' = "read_parent"
       ELSE /\ rpc' = "restart"          \* can't lock or not chain member
            /\ UNCHANGED <<c_ver, r_chain_locked>>
    /\ UNCHANGED <<p_count, p_child, p_ver, c_count,
                   r_pver, r_p_count, r_p_child, r_cut_level, ipc, i_target>>

\* Read parent state
RemoverReadParent ==
    /\ rpc = "read_parent"
    /\ r_pver' = p_ver
    /\ r_p_count' = p_count
    /\ r_p_child' = p_child
    /\ rpc' = "validate_parent"
    /\ UNCHANGED <<p_count, p_child, p_ver, c_count, c_ver,
                   r_chain_locked, r_cut_level, ipc, i_target>>

\* Validate parent version
RemoverValidateParent ==
    /\ rpc = "validate_parent"
    /\ IF p_ver = r_pver /\ p_ver % 2 = 0
       THEN \* Valid read — evaluate cases
            IF ~r_p_child
            THEN rpc' = "case_c"          \* child pointer gone
            ELSE IF r_p_count = 1
            THEN rpc' = "case_b"          \* parent became single-child
            ELSE rpc' = "case_a"          \* normal: parent has 2+ children
       ELSE rpc' = "read_parent"          \* invalid — re-read
    /\ UNCHANGED <<p_count, p_child, p_ver, c_count, c_ver,
                   r_pver, r_p_count, r_p_child, r_chain_locked, r_cut_level, ipc, i_target>>

\* Case A: parent has 2+ children, one is chain. Lock parent, cut.
RemoverCaseA ==
    /\ rpc = "case_a"
    /\ IF p_ver = r_pver /\ p_ver % 2 = 0
       THEN /\ p_ver' = p_ver + 1    \* lock parent
            /\ rpc' = "cut"
       ELSE /\ rpc' = "read_parent"  \* upgrade failed, re-read
            /\ UNCHANGED p_ver
    /\ UNCHANGED <<p_count, p_child, c_count, c_ver,
                   r_pver, r_p_count, r_p_child, r_chain_locked, r_cut_level, ipc, i_target>>

\* Case B: parent is single-child I4 → extends chain upward.
\* In full algorithm, we'd lock parent and move cut_level up.
\* Here we model it as: lock parent as chain member, restart CPP eval.
RemoverCaseB ==
    /\ rpc = "case_b"
    /\ IF p_ver = r_pver /\ p_ver % 2 = 0
       THEN /\ p_ver' = p_ver + 1    \* lock parent (now part of chain)
            /\ r_cut_level' = 1       \* cut moved up
            /\ rpc' = "done"          \* simplified: would eval grandparent
       ELSE /\ rpc' = "read_parent"
            /\ UNCHANGED <<p_ver, r_cut_level>>
    /\ UNCHANGED <<p_count, p_child, c_count, c_ver,
                   r_pver, r_p_count, r_p_child, r_chain_locked, ipc, i_target>>

\* Case C: child pointer gone → restart
RemoverCaseC ==
    /\ rpc = "case_c"
    /\ rpc' = "restart"
    /\ UNCHANGED <<p_count, p_child, p_ver, c_count, c_ver,
                   r_pver, r_p_count, r_p_child, r_chain_locked, r_cut_level, ipc, i_target>>

\* Cut: remove chain from parent (point of no return)
RemoverCut ==
    /\ rpc = "cut"
    /\ p_child' = FALSE       \* disconnect chain from parent
    /\ p_count' = p_count - 1
    /\ p_ver' = p_ver + 1     \* unlock parent
    /\ c_ver' = c_ver + 1     \* unlock+obsolete chain
    /\ r_chain_locked' = FALSE \* released
    /\ rpc' = "done"
    /\ UNCHANGED <<c_count, r_pver, r_p_count, r_p_child, r_cut_level, ipc, i_target>>

RemoverRestart ==
    /\ rpc = "restart"
    \* Release chain lock if held
    /\ IF r_chain_locked
       THEN c_ver' = c_ver + 1
       ELSE UNCHANGED c_ver
    /\ r_chain_locked' = FALSE
    /\ rpc' = "idle"
    /\ UNCHANGED <<p_count, p_child, p_ver, c_count,
                   r_pver, r_p_count, r_p_child, r_cut_level, ipc, i_target>>

RemoverDone ==
    /\ rpc = "done"
    /\ rpc' = "idle"
    /\ UNCHANGED <<p_count, p_child, p_ver, c_count, c_ver,
                   r_pver, r_p_count, r_p_child, r_chain_locked, r_cut_level, ipc, i_target>>

-----------------------------------------------------------------------------
Step ==
    \/ InsertChoose \/ InsertLockTarget \/ InsertWriteTarget \/ InsertUnlockTarget
    \/ RemoverStart \/ RemoverLockChain \/ RemoverReadParent
    \/ RemoverValidateParent
    \/ RemoverCaseA \/ RemoverCaseB \/ RemoverCaseC
    \/ RemoverCut \/ RemoverRestart \/ RemoverDone

Spec == Init /\ [][Step]_vars

-----------------------------------------------------------------------------
\* INVARIANTS

\* CRITICAL: When remover cuts, parent actually has the chain as child
\* and has 2+ children (Case A was correct at lock time).
CutSafety ==
    rpc = "cut" => (p_child = TRUE /\ p_count >= 2)

\* Chain lock held only when chain is actually single-child
\* (only meaningful while remover actually holds the lock = c_ver is odd)
ChainLockValid ==
    (r_chain_locked /\ c_ver % 2 = 1) => c_count = 1

\* Case B only entered when parent truly has count=1
CaseBValid ==
    (rpc = "case_b" /\ p_ver = r_pver /\ p_ver % 2 = 0) => r_p_count = 1

\* Well-formedness: parent count never goes below 1 after cut
\* (parent had 2+, we remove 1, so >= 1)
WellFormedness ==
    p_count >= 1

\* State space bound
StateConstraint == p_ver <= MaxVersion /\ c_ver <= MaxVersion

=============================================================================
