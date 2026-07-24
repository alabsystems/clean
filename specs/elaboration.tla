--------------------------- MODULE elaboration ---------------------------
(* TLA+ specification of the clean elaboration pipeline.
 *
 * Author: Andrew Yates <andrewyates.name@gmail.com>
 * Part of: clean theorem prover (https://github.com/alabsystems/clean)
 *
 * This spec models the state machine for elaborating Lean surface syntax
 * into validated kernel expressions. It captures:
 * - Phase transitions (Parse -> Elaborate -> TypeCheck -> Register)
 * - Error handling and rollback
 * - Environment modification
 * - Speculative scopes with snapshot-based undo for elaboration attempts
 *
 * Reference implementation:
 * - crates/clean-elab/src/lib.rs (entry points)
 * - crates/clean-elab/src/infer/mod.rs (ElabCtx)
 * - crates/clean-elab/src/infer/elaborate_decl.rs (declaration elaboration)
 * - crates/clean-elab/src/unify/meta_state/undo.rs (push_scope/pop_scope/commit)
 *
 * Known divergences from implementation (documented for spec-impl traceability):
 * - Parse is external (clean-parser); modeled here as first pipeline phase
 * - MacroExpand is interleaved per-expression in real impl; modeled as
 *   separate phase for clarity (safe abstraction: order is preserved)
 * - TypeCheck is optional in impl (STRICT_KERNEL_CHECK env var); modeled
 *   as mandatory phase (spec is stricter than default impl)
 * - MetaState is per-ElabCtx (fresh per decl); modeled as explicit clear
 * - ErrorCount/MaxErrors is aspirational; no impl counterpart yet
 *)

EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANT
    Decls,          \* Set of declarations to process
    MaxErrors       \* Maximum allowed errors before abort

(* CONSTANT validation: catch cfg misconfiguration before state exploration *)
ASSUME /\ Decls /= {}
       /\ MaxErrors \in Nat /\ MaxErrors >= 1

VARIABLE
    phase,          \* Current phase: "Init", "Parse", "MacroExpand",
                    \* "Elaborate", "TypeCheck", "Register", "Done", "Error", "Aborted"
    currentDecl,    \* Declaration currently being processed
    pending,        \* Sequence of pending declarations
    processed,      \* Set of successfully processed declarations
    environment,    \* Set of registered declarations (kernel env)
    metaState,      \* Metavariable assignments (for unification)
    errorCount,     \* Number of errors encountered
    lastError,      \* Most recent error (if any)
    scopeMarkers    \* Sequence of state snapshots for speculative elaboration
                    \* Reference: unify/meta_state/undo.rs:45-47 (push_scope)
                    \*            infer/elab_app.rs:338+ (speculative overload resolution)
                    \*            infer/instance.rs:115+ (instance candidate trying)

vars == <<phase, currentDecl, pending, processed, environment, metaState, errorCount, lastError, scopeMarkers>>

(* ------------------------------- Type Invariants ------------------------------- *)

TypeOK ==
    /\ phase \in {"Init", "Parse", "MacroExpand", "Elaborate", "TypeCheck", "Register", "Done", "Error", "Aborted"}
    /\ currentDecl \in Decls \cup {<<>>}
    /\ pending \in Seq(Decls)
    /\ processed \subseteq Decls
    /\ environment \subseteq Decls
    /\ metaState \subseteq Decls
    /\ errorCount \in Nat
    /\ errorCount <= MaxErrors
    \* Structural: lastError is either empty or a 2-tuple [ErrorKind, Decl]
    /\ lastError = <<>> \/ (Len(lastError) = 2 /\ lastError[2] \in Decls)
    \* Structural: active processing phases imply a current declaration
    /\ phase \in {"Parse", "MacroExpand", "Elaborate", "TypeCheck", "Register"}
           => currentDecl \in Decls
    \* Structural: Init/Done have no active declaration
    \* (Aborted may retain currentDecl from the failed processing phase)
    /\ phase \in {"Init", "Done"} => currentDecl = <<>>
    \* Structural: speculative scope markers are well-formed
    /\ \A i \in 1..Len(scopeMarkers) :
           /\ scopeMarkers[i].metaState \subseteq Decls
           /\ scopeMarkers[i].phase \in {"Elaborate", "TypeCheck"}

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

(* ------------------------------- Initial State ------------------------------- *)

Init ==
    /\ phase = "Init"
    /\ currentDecl = <<>>
    /\ pending = SetToSeq(Decls)
    /\ processed = {}
    /\ environment = {}
    /\ metaState = {}
    /\ errorCount = 0
    /\ lastError = <<>>
    /\ scopeMarkers = <<>>

(* ------------------------------- Phase Transitions ------------------------------- *)

(* Start processing next declaration *)
StartDecl ==
    /\ phase = "Init"
    /\ Len(pending) > 0
    /\ currentDecl' = Head(pending)
    /\ pending' = Tail(pending)
    /\ phase' = "Parse"
    /\ UNCHANGED <<processed, environment, metaState, errorCount, lastError, scopeMarkers>>

(* Parse surface syntax to SurfaceExpr/SurfaceDecl *)
Parse ==
    /\ phase = "Parse"
    /\ currentDecl /= <<>>
    \* Nondeterministic: parsing can succeed or fail
    /\ \/ /\ phase' = "MacroExpand"
          /\ UNCHANGED <<currentDecl, pending, processed, environment, metaState, errorCount, lastError, scopeMarkers>>
       \/ /\ phase' = "Error"
          /\ lastError' = <<"ParseError", currentDecl>>
          /\ errorCount' = errorCount + 1
          /\ UNCHANGED <<currentDecl, pending, processed, environment, metaState, scopeMarkers>>

(* Expand macros in surface syntax.
   Note: in the real implementation, macro expansion is interleaved
   per-expression during elaboration (infer/mod.rs:260). Modeled here
   as a separate phase for clarity — order is preserved. *)
MacroExpand ==
    /\ phase = "MacroExpand"
    /\ \/ /\ phase' = "Elaborate"
          /\ UNCHANGED <<currentDecl, pending, processed, environment, metaState, errorCount, lastError, scopeMarkers>>
       \/ /\ phase' = "Error"
          /\ lastError' = <<"MacroError", currentDecl>>
          /\ errorCount' = errorCount + 1
          /\ UNCHANGED <<currentDecl, pending, processed, environment, metaState, scopeMarkers>>

(* Elaborate surface syntax to Expr with metavariables.
   Elaboration uses speculative scopes internally for overload resolution
   and instance candidate trying (push_scope/pop_scope/commit).
   These are modeled via PushElabScope/PopElabScope/CommitElabScope below. *)
Elaborate ==
    /\ phase = "Elaborate"
    \* During elaboration:
    \* - Type inference with metavariables
    \* - Instance resolution (speculative: push_scope → try → pop/commit)
    \* - Unification constraints
    /\ \/ /\ phase' = "TypeCheck"
          \* Create fresh metavariables for unresolved types
          /\ metaState' = metaState \cup {currentDecl}
          \* All speculative scopes must be resolved before advancing
          /\ scopeMarkers = <<>>
          /\ UNCHANGED <<currentDecl, pending, processed, environment, errorCount, lastError, scopeMarkers>>
       \/ /\ phase' = "Error"
          /\ lastError' = <<"ElabError", currentDecl>>
          /\ errorCount' = errorCount + 1
          /\ UNCHANGED <<currentDecl, pending, processed, environment, metaState, scopeMarkers>>

(* Type check elaborated expression against kernel.
   Note: in the default implementation, kernel type checking is optional
   (STRICT_KERNEL_CHECK env var). The spec models it as mandatory — this
   is intentionally stricter than the default code path. *)
TypeCheck ==
    /\ phase = "TypeCheck"
    \* Kernel type checker validates:
    \* - Well-formedness
    \* - Type correctness
    \* - Universe consistency
    /\ \/ /\ phase' = "Register"
          /\ UNCHANGED <<currentDecl, pending, processed, environment, metaState, errorCount, lastError, scopeMarkers>>
       \/ /\ phase' = "Error"
          /\ lastError' = <<"TypeMismatch", currentDecl>>
          /\ errorCount' = errorCount + 1
          /\ UNCHANGED <<currentDecl, pending, processed, environment, metaState, scopeMarkers>>

(* Register validated declaration in environment *)
Register ==
    /\ phase = "Register"
    \* Add to kernel environment
    /\ environment' = environment \cup {currentDecl}
    /\ processed' = processed \cup {currentDecl}
    /\ phase' = IF Len(pending) > 0 THEN "Init" ELSE "Done"
    /\ currentDecl' = <<>>
    \* Clear metaState for next decl (models ElabCtx drop)
    /\ metaState' = {}
    /\ scopeMarkers' = <<>>
    /\ UNCHANGED <<pending, errorCount, lastError>>

(* Handle error: skip declaration and continue or abort *)
HandleError ==
    /\ phase = "Error"
    /\ IF errorCount < MaxErrors
       THEN /\ phase' = IF Len(pending) > 0 THEN "Init" ELSE "Done"
            /\ currentDecl' = <<>>
            /\ metaState' = {}
            /\ scopeMarkers' = <<>>
            /\ UNCHANGED <<pending, processed, environment, errorCount, lastError>>
       ELSE /\ phase' = "Aborted"
            /\ UNCHANGED <<currentDecl, pending, processed, environment, metaState, errorCount, lastError, scopeMarkers>>

(* Completion: all declarations processed or aborted *)
Complete ==
    /\ phase \in {"Done", "Aborted"}
    /\ UNCHANGED vars

(* ------------------------------- Speculative Scope Actions ------------------------------- *)

(* Push a scope marker for speculative elaboration.
   Used by instance resolution, overload resolution, and tactic evaluation
   to try candidates and backtrack on failure. Stores a snapshot of the
   metaState and current phase.
   Reference: unify/meta_state/undo.rs:45-47 (push_scope)
              infer/elab_app.rs:338+ (speculative overload resolution)
              infer/instance.rs:115+ (instance candidate trying) *)
PushElabScope ==
    /\ phase \in {"Elaborate", "TypeCheck"}
    /\ scopeMarkers' = Append(scopeMarkers, [
           metaState |-> metaState,
           phase |-> phase
       ])
    /\ UNCHANGED <<phase, currentDecl, pending, processed, environment,
                   metaState, errorCount, lastError>>

(* Pop scope and restore metaState (backtrack on failed candidate).
   Models MetaState::pop_scope() which replays UndoRecord entries in
   reverse to undo individual meta assignments, creations, and level
   constraints. Snapshot-based is equivalent in TLA+ since values are
   mathematical objects.
   Reference: unify/meta_state/undo.rs:54-67 (pop_scope)
              infer/instance.rs:167+ (instance candidate backtrack) *)
PopElabScope ==
    /\ phase \in {"Elaborate", "TypeCheck"}
    /\ Len(scopeMarkers) > 0
    /\ LET snapshot == Last(scopeMarkers) IN
       /\ metaState' = snapshot.metaState
       /\ scopeMarkers' = Front(scopeMarkers)
    /\ UNCHANGED <<phase, currentDecl, pending, processed, environment,
                   errorCount, lastError>>

(* Commit scope: drop marker without restoring, making speculative
   changes permanent. Models success in instance resolution, overload
   resolution, and tactic evaluation.
   Reference: unify/meta_state/undo.rs:80-91 (commit) *)
CommitElabScope ==
    /\ phase \in {"Elaborate", "TypeCheck"}
    /\ Len(scopeMarkers) > 0
    /\ scopeMarkers' = Front(scopeMarkers)
    /\ UNCHANGED <<phase, currentDecl, pending, processed, environment,
                   metaState, errorCount, lastError>>

(* ------------------------------- Rollback Actions ------------------------------- *)

(* Rollback on type error: undo metavariable assignments *)
Rollback ==
    /\ phase = "Error"
    /\ lastError[1] \in {"TypeMismatch", "ElabError"}
    /\ metaState' = {}  \* Clear all speculative assignments
    /\ scopeMarkers' = <<>>
    /\ UNCHANGED <<phase, currentDecl, pending, processed, environment, errorCount, lastError>>

(* ------------------------------- Next State ------------------------------- *)

Next ==
    \/ StartDecl
    \/ Parse
    \/ MacroExpand
    \/ Elaborate
    \/ TypeCheck
    \/ Register
    \/ HandleError
    \/ Complete
    \/ PushElabScope
    \/ PopElabScope
    \/ CommitElabScope
    \/ Rollback

Spec == Init /\ [][Next]_vars

(* ------------------------------- Safety Properties ------------------------------- *)

(* No phase skipping: transitions follow order (action property) *)
PhaseOrder ==
    [][/\ (phase = "MacroExpand" => phase' \in {"Elaborate", "Error", "MacroExpand"})
       /\ (phase = "Elaborate" => phase' \in {"TypeCheck", "Error", "Elaborate"})
       /\ (phase = "TypeCheck" => phase' \in {"Register", "Error", "TypeCheck"})]_vars

(* Environment only grows (monotonicity) *)
EnvironmentMonotonic ==
    [][environment \subseteq environment']_vars

(* Processed implies registered *)
ProcessedImpliesRegistered ==
    processed \subseteq environment

(* Only register after successful type check (state invariant) *)
OnlyRegisterAfterTypeCheck ==
    phase = "Register" =>
        \E d \in Decls : d = currentDecl /\ d \notin environment

(* Error handling preserves consistency (action property) *)
ErrorPreservesConsistency ==
    [][phase = "Error" =>
        /\ processed' = processed
        /\ environment' = environment]_vars

(* Error count never decreases (action property) *)
ErrorCountMonotonic ==
    [][errorCount' >= errorCount]_vars

(* Pending queue only shrinks: no action adds declarations to pending *)
PendingMonotonic ==
    [][Len(pending') <= Len(pending)]_vars

(* MetaState monotonicity: metaState only grows during elaboration UNLESS
   a speculative scope is popped (backtracking) or an error clears it.
   Same weakening pattern as GoalStateMonotonic in tactics.tla. *)
MetaStateMonotonic ==
    [][metaState \subseteq metaState'
       \/ (Len(scopeMarkers) > 0 /\ Len(scopeMarkers') < Len(scopeMarkers))
       \/ phase = "Error"
       \/ phase = "Register"]_vars

(* Scopes are balanced: no scope markers leak past declaration boundaries.
   At Init/Done/Aborted, all scopes must be resolved. *)
ScopesResolved ==
    phase \in {"Init", "Done", "Aborted"} => scopeMarkers = <<>>

(* ------------------------------- Liveness Properties ------------------------------- *)

(* Eventually all declarations are processed or aborted *)
EventuallyComplete ==
    <>(phase \in {"Done", "Aborted"})

(* Progress-driving actions (excludes Complete which is stuttering,
   Rollback which can cycle, and PushElabScope/PopElabScope which can
   cycle without advancing the pipeline. CommitElabScope IS progress:
   it means a speculative elaboration attempt succeeded.) *)
ProgressActions ==
    \/ StartDecl
    \/ Parse
    \/ MacroExpand
    \/ Elaborate
    \/ TypeCheck
    \/ Register
    \/ HandleError
    \/ CommitElabScope

(* Fair scheduling: only progress actions are fairly scheduled.
   Complete is a stuttering step (UNCHANGED vars). Rollback,
   PushElabScope, and PopElabScope may occur but are not required to,
   preventing infinite speculation/backtracking cycles. *)
FairSpec ==
    Spec /\ WF_vars(ProgressActions)

(* With fair scheduling, we make progress *)
Progress ==
    FairSpec => EventuallyComplete

(* ------------------------------- Invariants ------------------------------- *)

(* Main safety invariant *)
Safety ==
    /\ TypeOK
    /\ ProcessedImpliesRegistered
    /\ ScopesResolved
    \* Note: EnvironmentMonotonic is a temporal property, verified separately

(* No stuck states (always have enabled action or done/aborted).
   Active scopes enable PopElabScope/CommitElabScope as escape actions. *)
NoStuckStates ==
    \/ phase \in {"Done", "Aborted"}
    \/ ENABLED(Next)

=============================================================================
\* Modification History
\* Created: 2026-02-02 for clean elaboration pipeline specification
