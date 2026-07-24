--------------------------- MODULE tactics ---------------------------
(* TLA+ specification of the clean tactic execution state machine.
 *
 * Author: Andrew Yates <andrewyates.name@gmail.com>
 * Part of: clean theorem prover (https://github.com/alabsystems/clean)
 *
 * This spec models the AND-OR search tree for automated proof search.
 * It captures:
 * - Goal state management
 * - Tactic application and subgoal creation
 * - Backtracking via AND-OR tree semantics
 * - Speculative scopes with snapshot-based undo (PushScope/PopScope/CommitScope)
 * - Success/failure propagation
 *
 * Reference implementation:
 * - crates/clean-elab/src/tactic/mod.rs (ProofState, Goal, TacticResult)
 * - crates/clean-elab/src/tactic/search.rs (SearchTree, GoalState)
 * - crates/clean-elab/src/unify.rs (MetaState, undo trail)
 *)

EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS
    GoalIds,        \* Set of all possible goal identifiers
    RappIds,        \* Set of all possible rule application identifiers
    MetaIds,        \* Set of metavariable identifiers
    Rules,          \* Set of available tactic rules
    MaxDepth,       \* Maximum search depth
    MaxIterations   \* Maximum search iterations

(* CONSTANT validation: catch cfg misconfiguration before state exploration *)
ASSUME /\ GoalIds /= {}
       /\ RappIds /= {}
       /\ MetaIds /= {}
       /\ Rules /= {}
       /\ MaxDepth \in Nat /\ MaxDepth >= 1
       /\ MaxIterations \in Nat /\ MaxIterations >= 1
       \* Init creates goal 1 with metaId 1, so these must be in scope
       /\ 1 \in GoalIds
       /\ 1 \in MetaIds

VARIABLES
    goals,          \* Function: GoalId -> GoalRecord
    rapps,          \* Function: RappId -> RappRecord
    rootGoal,       \* The root goal being proven
    proofState,     \* Current proof state: "Searching", "Proven", "Failed"
    goalQueue,      \* Sequence of unexpanded goal IDs (frontier)
    metaAssignments, \* Function: MetaId -> ProofTerm (or <<>> if unassigned)
    undoTrail,      \* Sequence of undo records for backtracking
    scopeMarkers,   \* Sequence of state snapshots for speculative scope management
    iteration,      \* Current iteration count
    nextGoalId,     \* Counter for fresh goal IDs
    nextRappId      \* Counter for fresh rapp IDs

vars == <<goals, rapps, rootGoal, proofState, goalQueue, metaAssignments,
          undoTrail, scopeMarkers, iteration, nextGoalId, nextRappId>>

(* ------------------------------- Types ------------------------------- *)

GoalStates == {"Unknown", "ProvenByNorm", "ProvenByRapp", "Unprovable"}
NodeStates == {"Unknown", "Proven", "Unprovable"}
RuleKinds == {"Safe", "Norm", "Unsafe"}

GoalRecord == [
    id: GoalIds,
    parent: RappIds \cup {0},
    children: SUBSET RappIds,
    state: GoalStates,
    metaId: MetaIds,
    depth: Nat
]

RappRecord == [
    id: RappIds,
    parent: GoalIds,
    children: SUBSET GoalIds,
    state: NodeStates,
    rule: Rules,
    kind: RuleKinds
]

(* ------------------------------- Type Invariant ------------------------------- *)

TypeOK ==
    /\ proofState \in {"Searching", "Proven", "Failed", "Timeout"}
    /\ iteration \in Nat
    /\ iteration <= MaxIterations
    /\ nextGoalId \in Nat
    /\ nextRappId \in Nat
    \* Structural: root goal always exists in goals domain
    /\ rootGoal \in DOMAIN goals
    \* Structural: all goalQueue entries reference existing goals
    /\ \A i \in 1..Len(goalQueue) : goalQueue[i] \in DOMAIN goals
    \* Structural: all rapp children reference existing goals
    /\ \A r \in DOMAIN rapps : rapps[r].children \subseteq DOMAIN goals
    \* Structural: all goal children reference existing rapps
    /\ \A g \in DOMAIN goals : goals[g].children \subseteq DOMAIN rapps
    \* Structural: metaAssignment domain covers all goals' metaIds
    /\ \A g \in DOMAIN goals : goals[g].metaId \in DOMAIN metaAssignments

(* ------------------------------- Initial State ------------------------------- *)

Init ==
    /\ goals = [g \in {1} |-> [
           id |-> 1,
           parent |-> 0,
           children |-> {},
           state |-> "Unknown",
           metaId |-> 1,
           depth |-> 0
       ]]
    /\ rapps = [r \in {} |-> <<>>]
    /\ rootGoal = 1
    /\ proofState = "Searching"
    /\ goalQueue = <<1>>
    /\ metaAssignments = [m \in {1} |-> <<>>]
    /\ undoTrail = <<>>
    /\ scopeMarkers = <<>>
    /\ iteration = 0
    /\ nextGoalId = 2
    /\ nextRappId = 1

(* ------------------------------- Helper Operators ------------------------------- *)

(* Convert set to sequence (TLC-compatible recursive version) *)
RECURSIVE SetToSeqHelper(_, _)
SetToSeqHelper(S, acc) ==
    IF S = {} THEN acc
    ELSE LET x == CHOOSE x \in S : TRUE
         IN SetToSeqHelper(S \ {x}, Append(acc, x))

SetToSeq(S) == SetToSeqHelper(S, <<>>)

(* Get last element of sequence *)
Last(s) == s[Len(s)]

(* Get all but last element of sequence *)
Front(s) == SubSeq(s, 1, Len(s) - 1)

(* Check if all goals in a set are proven *)
AllProven(goalSet) ==
    \A g \in goalSet : goals[g].state \in {"ProvenByNorm", "ProvenByRapp"}

(* Check if all rapps in a set are unprovable *)
AllUnprovable(rappSet) ==
    \A r \in rappSet : rapps[r].state = "Unprovable"

(* Get unexpanded goals (state = Unknown) *)
UnexpandedGoals ==
    {g \in DOMAIN goals : goals[g].state = "Unknown"}

(* ------------------------------- Tactic Application ------------------------------- *)

(* Apply a tactic rule to a goal, creating subgoals *)
ApplyRule(goalId, rule, subgoalCount, ruleKind) ==
    LET
        newRappId == nextRappId
        newSubgoalIds == {nextGoalId + i : i \in 0..(subgoalCount-1)}
    IN
    /\ proofState = "Searching"
    /\ goalId \in DOMAIN goals
    /\ goals[goalId].state = "Unknown"
    /\ goals[goalId].depth < MaxDepth
    /\ iteration < MaxIterations
    \* Create new rapp
    /\ rapps' = rapps @@ (newRappId :> [
           id |-> newRappId,
           parent |-> goalId,
           children |-> newSubgoalIds,
           state |-> "Unknown",
           rule |-> rule,
           kind |-> ruleKind
       ])
    \* Update parent goal
    /\ goals' = [goals EXCEPT
           ![goalId].children = @ \cup {newRappId}
       ] @@ [g \in newSubgoalIds |-> [
           id |-> g,
           parent |-> newRappId,
           children |-> {},
           state |-> "Unknown",
           metaId |-> g,  \* Fresh metavariable
           depth |-> goals[goalId].depth + 1
       ]]
    \* Add subgoals to queue
    /\ goalQueue' = goalQueue \o SetToSeq(newSubgoalIds)
    \* Track undo for backtracking
    /\ undoTrail' = Append(undoTrail, <<"CreateRapp", newRappId, newSubgoalIds>>)
    /\ nextRappId' = nextRappId + 1
    /\ nextGoalId' = nextGoalId + subgoalCount
    /\ iteration' = iteration + 1
    \* Extend metaAssignment domain for new subgoals (unassigned)
    /\ metaAssignments' = metaAssignments @@ [g \in newSubgoalIds |-> <<>>]
    /\ UNCHANGED <<rootGoal, proofState, scopeMarkers>>

(* Close a goal with a proof (leaf node) *)
CloseGoal(goalId, proofTerm) ==
    /\ proofState = "Searching"
    /\ goalId \in DOMAIN goals
    /\ goals[goalId].state = "Unknown"
    /\ iteration < MaxIterations
    \* Guard: metaId must be in metaAssignments domain (always true for
    \* goals created via Init or ApplyRule, but TLC needs explicit check)
    /\ goals[goalId].metaId \in DOMAIN metaAssignments
    \* Assign proof to metavariable
    /\ metaAssignments' = [metaAssignments EXCEPT
           ![goals[goalId].metaId] = proofTerm
       ]
    \* Mark goal as proven
    /\ goals' = [goals EXCEPT ![goalId].state = "ProvenByNorm"]
    /\ undoTrail' = Append(undoTrail, <<"CloseGoal", goalId>>)
    /\ iteration' = iteration + 1
    /\ UNCHANGED <<rapps, rootGoal, proofState, goalQueue, scopeMarkers,
                   nextGoalId, nextRappId>>

(* ------------------------------- Propagation ------------------------------- *)

(* Propagate proven status upward (AND-OR semantics) *)
PropagateProven(goalId) ==
    /\ proofState = "Searching"
    /\ goalId \in DOMAIN goals
    /\ goals[goalId].state \in {"ProvenByNorm", "ProvenByRapp"}
    /\ goals[goalId].parent /= 0
    \* Parent rapp: ALL subgoals must be proven (AND semantics)
    /\ LET parentRapp == goals[goalId].parent IN
       /\ parentRapp \in DOMAIN rapps
       /\ AllProven(rapps[parentRapp].children)
       /\ rapps' = [rapps EXCEPT ![parentRapp].state = "Proven"]
    /\ UNCHANGED <<goals, rootGoal, proofState, goalQueue, metaAssignments,
                   undoTrail, scopeMarkers, iteration, nextGoalId, nextRappId>>

(* Propagate proven from rapp to its parent goal *)
PropagateRappProven(rappId) ==
    /\ proofState = "Searching"
    /\ rappId \in DOMAIN rapps
    /\ rapps[rappId].state = "Proven"
    \* Parent goal: at least ONE rapp proven (OR semantics)
    /\ LET parentGoal == rapps[rappId].parent IN
       goals' = [goals EXCEPT ![parentGoal].state = "ProvenByRapp"]
    /\ UNCHANGED <<rapps, rootGoal, proofState, goalQueue, metaAssignments,
                   undoTrail, scopeMarkers, iteration, nextGoalId, nextRappId>>

(* Propagate unprovable status upward *)
PropagateUnprovable(goalId) ==
    /\ proofState = "Searching"
    /\ goalId \in DOMAIN goals
    /\ goals[goalId].state = "Unprovable"
    /\ goals[goalId].parent /= 0
    \* Parent rapp becomes unprovable (AND semantics: one failure = total)
    /\ LET parentRapp == goals[goalId].parent IN
       rapps' = [rapps EXCEPT ![parentRapp].state = "Unprovable"]
    /\ UNCHANGED <<goals, rootGoal, proofState, goalQueue, metaAssignments,
                   undoTrail, scopeMarkers, iteration, nextGoalId, nextRappId>>

(* Propagate unprovable from rapp to parent goal if all rapps failed *)
PropagateRappUnprovable(rappId) ==
    /\ proofState = "Searching"
    /\ rappId \in DOMAIN rapps
    /\ rapps[rappId].state = "Unprovable"
    /\ LET parentGoal == rapps[rappId].parent IN
       \* All rapps of parent goal must be unprovable (OR semantics)
       /\ AllUnprovable(goals[parentGoal].children)
       /\ goals' = [goals EXCEPT ![parentGoal].state = "Unprovable"]
    /\ UNCHANGED <<rapps, rootGoal, proofState, goalQueue, metaAssignments,
                   undoTrail, scopeMarkers, iteration, nextGoalId, nextRappId>>

(* ------------------------------- Termination ------------------------------- *)

(* Success: root goal proven *)
ProofFound ==
    /\ proofState = "Searching"
    /\ goals[rootGoal].state \in {"ProvenByNorm", "ProvenByRapp"}
    /\ proofState' = "Proven"
    /\ UNCHANGED <<goals, rapps, rootGoal, goalQueue, metaAssignments,
                   undoTrail, scopeMarkers, iteration, nextGoalId, nextRappId>>

(* Failure: root goal unprovable *)
ProofFailed ==
    /\ proofState = "Searching"
    /\ goals[rootGoal].state = "Unprovable"
    /\ proofState' = "Failed"
    /\ UNCHANGED <<goals, rapps, rootGoal, goalQueue, metaAssignments,
                   undoTrail, scopeMarkers, iteration, nextGoalId, nextRappId>>

(* Timeout: max iterations reached *)
Timeout ==
    /\ proofState = "Searching"
    /\ iteration >= MaxIterations
    /\ proofState' = "Timeout"
    /\ UNCHANGED <<goals, rapps, rootGoal, goalQueue, metaAssignments,
                   undoTrail, scopeMarkers, iteration, nextGoalId, nextRappId>>

(* ------------------------------- Backtracking ------------------------------- *)

(* Push a scope marker for speculative operations.
   Stores a full state snapshot (goals, rapps, metaAssignments, goalQueue,
   undoTrail, nextGoalId, nextRappId). This mirrors the real implementation
   where callers clone goals before push_scope() and MetaState saves an
   undo trail position. Snapshot-based is equivalent in TLA+ since values
   are mathematical objects.
   Reference: crates/clean-elab/src/unify/meta_state/undo.rs:45-47 (push_scope)
              crates/clean-elab/src/tactic/combinator.rs:34-53 (try_tactic pattern) *)
PushScope ==
    /\ proofState = "Searching"
    /\ scopeMarkers' = Append(scopeMarkers, [
           goals |-> goals,
           rapps |-> rapps,
           metaAssignments |-> metaAssignments,
           goalQueue |-> goalQueue,
           undoTrail |-> undoTrail,
           nextGoalId |-> nextGoalId,
           nextRappId |-> nextRappId
       ])
    /\ UNCHANGED <<goals, rapps, rootGoal, proofState, goalQueue,
                   metaAssignments, undoTrail, iteration, nextGoalId, nextRappId>>

(* Pop scope and restore state (backtrack).
   Restores goals, rapps, metaAssignments, goalQueue, undoTrail, and ID
   counters to their values at the matching PushScope. This models the real
   implementation's two-part restoration:
   1. MetaState::pop_scope() replays UndoRecord entries in reverse (LIFO)
      to restore meta assignments, meta existence, and level constraints
   2. Callers manually restore goals from their saved clone
   Reference: crates/clean-elab/src/unify/meta_state/undo.rs:54-67 (pop_scope)
              crates/clean-elab/src/tactic/combinator.rs:43-50 (goal restore) *)
PopScope ==
    /\ proofState = "Searching"
    /\ Len(scopeMarkers) > 0
    /\ LET snapshot == Last(scopeMarkers) IN
       /\ goals' = snapshot.goals
       /\ rapps' = snapshot.rapps
       /\ metaAssignments' = snapshot.metaAssignments
       /\ goalQueue' = snapshot.goalQueue
       /\ undoTrail' = snapshot.undoTrail
       /\ nextGoalId' = snapshot.nextGoalId
       /\ nextRappId' = snapshot.nextRappId
       /\ scopeMarkers' = Front(scopeMarkers)
    /\ UNCHANGED <<rootGoal, proofState, iteration>>

(* Commit scope: drop scope marker without restoring, making speculative
   changes permanent. Models success in try/first/solve_by_elim patterns.
   When the last scope is committed, the undo trail is cleared (mirrors
   the memory cleanup in issue #730).
   Reference: crates/clean-elab/src/unify/meta_state/undo.rs:80-91 (commit) *)
CommitScope ==
    /\ proofState = "Searching"
    /\ Len(scopeMarkers) > 0
    /\ scopeMarkers' = Front(scopeMarkers)
    \* Memory cleanup: clear trail when last scope is committed (#730)
    /\ undoTrail' = IF Len(scopeMarkers) = 1 THEN <<>> ELSE undoTrail
    /\ UNCHANGED <<goals, rapps, rootGoal, proofState, goalQueue,
                   metaAssignments, iteration, nextGoalId, nextRappId>>

(* Terminal stuttering — search has concluded, no more actions *)
Done ==
    /\ proofState \in {"Proven", "Failed", "Timeout"}
    /\ UNCHANGED vars

(* ------------------------------- Next State ------------------------------- *)

Next ==
    \* n >= 1: rules creating 0 subgoals use CloseGoal instead.
    \* A rapp with 0 children can never be proven (PropagateProven needs a child trigger).
    \/ \E g \in DOMAIN goals, r \in Rules, n \in 1..3, k \in RuleKinds :
           ApplyRule(g, r, n, k)
    \/ \E g \in DOMAIN goals : CloseGoal(g, <<"proof">>)
    \/ \E g \in DOMAIN goals : PropagateProven(g)
    \/ \E r \in DOMAIN rapps : PropagateRappProven(r)
    \/ \E g \in DOMAIN goals : PropagateUnprovable(g)
    \/ \E r \in DOMAIN rapps : PropagateRappUnprovable(r)
    \/ ProofFound
    \/ ProofFailed
    \/ Timeout
    \/ PushScope
    \/ PopScope
    \/ CommitScope
    \/ Done

Spec == Init /\ [][Next]_vars

(* ------------------------------- Safety Properties ------------------------------- *)

(* Sound: success implies valid proof *)
(* A proven proof requires:
   1. Root goal is in a proven state
   2. Every goal closed via ProvenByNorm has its metavariable assigned
      (ProvenByRapp goals assemble proof terms from subgoal metas)
   3. Every Proven rapp has all its children proven (AND-node completeness) *)
SoundnessInvariant ==
    proofState = "Proven" =>
        /\ goals[rootGoal].state \in {"ProvenByNorm", "ProvenByRapp"}
        \* All directly-closed goals must have proof terms assigned
        /\ \A g \in DOMAIN goals :
               goals[g].state = "ProvenByNorm" =>
                   (goals[g].metaId \in DOMAIN metaAssignments
                    /\ metaAssignments[goals[g].metaId] /= <<>>)
        \* All proven rapps must have all children proven (AND completeness)
        /\ \A r \in DOMAIN rapps :
               rapps[r].state = "Proven" => AllProven(rapps[r].children)

(* No stuck states in AND-OR tree *)
(* Must account for transient states where root is proven/failed but proofState
   hasn't been updated yet — ProofFound/ProofFailed actions are still enabled.
   Also: active scopes enable PopScope/CommitScope as escape actions. *)
NoStuckStates ==
    \/ proofState \in {"Proven", "Failed", "Timeout"}
    \/ UnexpandedGoals /= {}  \* Equivalent to \E g \in DOMAIN goals : goals[g].state = "Unknown"
    \/ goals[rootGoal].state \in {"ProvenByNorm", "ProvenByRapp"}  \* ProofFound will fire
    \/ goals[rootGoal].state = "Unprovable"  \* ProofFailed will fire
    \/ Len(scopeMarkers) > 0  \* Can PopScope or CommitScope

(* Depth bound respected *)
DepthBoundRespected ==
    \A g \in DOMAIN goals : goals[g].depth <= MaxDepth

(* Goal state progression: no backwards transitions UNLESS a speculative
   scope is popped. PopScope restores state to the PushScope snapshot,
   which may revert proven/unprovable goals to Unknown. This is sound
   because the reverted proof attempt was speculative — the AND-OR tree
   explores alternatives via backtracking.
   Reference: crates/clean-elab/src/tactic/combinator.rs (try/first/solve_by_elim) *)
GoalStateMonotonic ==
    [][(\A g \in DOMAIN goals :
        goals[g].state \in {"ProvenByNorm", "ProvenByRapp", "Unprovable"} =>
            (g \in DOMAIN goals' => goals'[g].state = goals[g].state))
       \* PopScope may revert goal states (speculative backtracking)
       \/ (Len(scopeMarkers) > 0 /\ Len(scopeMarkers') = Len(scopeMarkers) - 1
           /\ goals' /= goals)]_vars

(* Stronger monotonicity: when no speculative scopes are active, goal states
   never revert. Once all scopes are committed, changes are permanent. *)
MonotonicAfterCommit ==
    [][scopeMarkers = <<>> /\ scopeMarkers' = <<>> =>
        \A g \in DOMAIN goals :
            goals[g].state \in {"ProvenByNorm", "ProvenByRapp", "Unprovable"} =>
                (g \in DOMAIN goals' => goals'[g].state = goals[g].state)]_vars

(* AND-OR consistency *)
AndOrConsistency ==
    \* Rapp proven => all subgoals proven (AND)
    /\ \A r \in DOMAIN rapps :
           rapps[r].state = "Proven" => AllProven(rapps[r].children)
    \* Goal proven by rapp => some rapp proven (OR)
    /\ \A g \in DOMAIN goals :
           goals[g].state = "ProvenByRapp" =>
               \E r \in goals[g].children : rapps[r].state = "Proven"

(* Iteration counter never decreases (action property) *)
IterationMonotonic ==
    [][iteration' >= iteration]_vars

(* Goals domain only grows — goals are never removed UNLESS a speculative
   scope is popped. PopScope may restore a smaller goals domain.
   Same weakening rationale as GoalStateMonotonic. *)
GoalsDomainMonotonic ==
    [][DOMAIN goals \subseteq DOMAIN goals'
       \/ (Len(scopeMarkers) > 0 /\ Len(scopeMarkers') = Len(scopeMarkers) - 1)]_vars

(* ------------------------------- Liveness Properties ------------------------------- *)

(* Eventually terminates *)
EventuallyTerminates ==
    <>(proofState \in {"Proven", "Failed", "Timeout"})

(* Progress-making actions. Excludes PushScope/PopScope which can cycle
   without advancing the proof. CommitScope IS progress: it means a
   speculative tactic succeeded and its changes are now permanent. *)
ProgressActions ==
    \/ \E g \in DOMAIN goals, r \in Rules, n \in 1..3, k \in RuleKinds :
           ApplyRule(g, r, n, k)
    \/ \E g \in DOMAIN goals : CloseGoal(g, <<"proof">>)
    \/ \E g \in DOMAIN goals : PropagateProven(g)
    \/ \E r \in DOMAIN rapps : PropagateRappProven(r)
    \/ \E g \in DOMAIN goals : PropagateUnprovable(g)
    \/ \E r \in DOMAIN rapps : PropagateRappUnprovable(r)
    \/ ProofFound
    \/ ProofFailed
    \/ Timeout
    \/ CommitScope

(* Fair scheduling: only progress actions are fairly scheduled.
   PushScope/PopScope may occur but are not required to, preventing
   infinite backtracking cycles that violate EventuallyTerminates.
   CommitScope is fairly scheduled since tactic success should be committed. *)
FairSpec ==
    Spec /\ WF_vars(ProgressActions)

(* With fair scheduling, we terminate *)
Termination ==
    FairSpec => EventuallyTerminates

(* ------------------------------- Main Invariant ------------------------------- *)

Safety ==
    /\ TypeOK
    /\ DepthBoundRespected
    /\ SoundnessInvariant
    /\ AndOrConsistency

=============================================================================
\* Modification History
\* Created: 2026-02-02 for clean tactic execution specification
