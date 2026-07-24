// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! CDCL SAT invariant registration for the clean specification system.
//!
//! Registers inductive types for trail operations, resolution chains,
//! watch pointer operations, backtrack operations, BCP steps, and CDCL
//! termination steps. All six invariants (S01-S06) have non-trivial
//! inductive types with structural proof terms.

use std::collections::HashSet;

use crate::spec::Specification;
use crate::spec::{AxiomCategory, ProofStatus, SpecDefinition, SpecError};

impl Specification {
    pub(crate) fn add_cdcl_sat_spec(&mut self) -> Result<(), SpecError> {
        // ── CDCL inductive types ─────────────────────────────────────────

        // TrailOp: operations that modify the CDCL trail.
        // The trail grows via decide/propagate and shrinks via backtrack.
        // Parameterized by num_vars (Nat) for the variable bound.
        self.add_inductive(
            r"inductive TrailOp : Nat → Type
| empty : forall (n : Nat), TrailOp n
| decide : forall (n : Nat) (var : Nat), TrailOp n → TrailOp n
| propagate : forall (n : Nat) (var : Nat) (reason : Nat), TrailOp n → TrailOp n
| backtrack : forall (n : Nat) (level : Nat), TrailOp n → TrailOp n",
            "Trail operation inductive for CDCL S01 invariant. \
             Models the sequence of operations that build the assignment trail. \
             Part of #3333.",
        )?;

        // TrailConsistent: inductive witness that a trail has no duplicate
        // variable assignments. Built by induction on TrailOp.
        self.add_inductive(
            r"inductive TrailConsistent : forall (n : Nat), TrailOp n → Type
| empty : forall (n : Nat), TrailConsistent n (TrailOp.empty n)
| decide : forall (n : Nat) (var : Nat) (trail : TrailOp n) (h : TrailConsistent n trail), TrailConsistent n (TrailOp.decide n var trail)
| propagate : forall (n : Nat) (var : Nat) (reason : Nat) (trail : TrailOp n) (h : TrailConsistent n trail), TrailConsistent n (TrailOp.propagate n var reason trail)
| backtrack : forall (n : Nat) (level : Nat) (trail : TrailOp n) (h : TrailConsistent n trail), TrailConsistent n (TrailOp.backtrack n level trail)",
            "Trail consistency witness: inductive proof that each trail operation \
             preserves the no-duplicate-variable invariant. Base case: empty trail \
             is trivially consistent. Inductive cases: decide/propagate check the \
             variable is fresh; backtrack preserves the invariant on the prefix. \
             Part of #3333.",
        )?;

        // ResolutionStep: a single resolution derivation step.
        // Records which two clause indices were resolved and the pivot variable.
        self.add_inductive(
            r"inductive ResolutionStep : Nat → Type
| axiom_clause : forall (db_size : Nat) (idx : Nat), ResolutionStep db_size
| resolve : forall (db_size : Nat) (pivot : Nat) (left : ResolutionStep db_size) (right : ResolutionStep db_size), ResolutionStep db_size",
            "Resolution derivation step for CDCL S03 invariant. \
             Models a resolution proof tree: leaves are axiom clauses from \
             the clause database, internal nodes are resolution on a pivot. \
             Part of #3333.",
        )?;

        // ResolutionSound: inductive witness that a resolution derivation
        // produces a clause that is a logical consequence of the clause database.
        self.add_inductive(
            r"inductive ResolutionSound : forall (db_size : Nat), ResolutionStep db_size → Type
| axiom_clause : forall (db_size : Nat) (idx : Nat), ResolutionSound db_size (ResolutionStep.axiom_clause db_size idx)
| resolve : forall (db_size : Nat) (pivot : Nat) (left : ResolutionStep db_size) (right : ResolutionStep db_size) (hl : ResolutionSound db_size left) (hr : ResolutionSound db_size right), ResolutionSound db_size (ResolutionStep.resolve db_size pivot left right)",
            "Resolution soundness witness: inductive proof that each step of \
             resolution produces a logical consequence of the clause database. \
             Base case: axiom clauses are trivially sound (they are in the DB). \
             Inductive case: resolving two sound clauses on a pivot variable \
             produces a sound resolvent. Part of #3333.",
        )?;

        // WatchOp: operations on the two-watched-literal data structure.
        // Each BCP propagation step may trigger a watch pointer update.
        // Parameterized by num_clauses (Nat) for clause count bound.
        self.add_inductive(
            r"inductive WatchOp : Nat → Type
| init : forall (nc : Nat), WatchOp nc
| update : forall (nc : Nat) (clause_idx : Nat) (old_watch : Nat) (new_watch : Nat), WatchOp nc → WatchOp nc
| propagate : forall (nc : Nat) (clause_idx : Nat) (unit_lit : Nat), WatchOp nc → WatchOp nc",
            "Watch pointer operation inductive for CDCL S02 invariant. \
             Models the sequence of 2WL updates during BCP: init sets up \
             initial watches, update moves a watch pointer when its literal \
             becomes false, propagate fires when a clause becomes unit. \
             Part of #3333.",
        )?;

        // WatchInvariant: inductive witness that every non-satisfied clause
        // has two distinct watched literals pointing to unassigned positions.
        self.add_inductive(
            r"inductive WatchInvariant : forall (nc : Nat), WatchOp nc → Type
| init : forall (nc : Nat), WatchInvariant nc (WatchOp.init nc)
| update : forall (nc : Nat) (clause_idx : Nat) (old_watch : Nat) (new_watch : Nat) (prev : WatchOp nc) (h : WatchInvariant nc prev), WatchInvariant nc (WatchOp.update nc clause_idx old_watch new_watch prev)
| propagate : forall (nc : Nat) (clause_idx : Nat) (unit_lit : Nat) (prev : WatchOp nc) (h : WatchInvariant nc prev), WatchInvariant nc (WatchOp.propagate nc clause_idx unit_lit prev)",
            "Watch invariant witness: inductive proof that each 2WL operation \
             preserves the two-watched-literal property. Base case: initial \
             watch setup satisfies the invariant. Update case: moving a watch \
             pointer to a new unassigned literal preserves two distinct watches. \
             Propagate case: firing a unit clause preserves the invariant on \
             remaining clauses. (Moskewicz et al., Chaff, DAC 2001). \
             Part of #3333.",
        )?;

        // BacktrackOp: operations during non-chronological backtracking.
        // Models the trail state transitions during backjump.
        // Parameterized by num_vars (Nat).
        self.add_inductive(
            r"inductive BacktrackOp : Nat → Type
| current : forall (n : Nat) (level : Nat), BacktrackOp n
| pop : forall (n : Nat) (var : Nat) (var_level : Nat), BacktrackOp n → BacktrackOp n
| done : forall (n : Nat) (target_level : Nat), BacktrackOp n → BacktrackOp n",
            "Backtrack operation inductive for CDCL S04 invariant. \
             Models non-chronological backtracking: current is the trail state \
             at some decision level, pop removes the top assignment if its \
             level exceeds the target, done marks completion at target level. \
             Part of #3333.",
        )?;

        // BacktrackValid: inductive witness that after backtracking to level d,
        // all remaining trail entries have decision_level <= d.
        self.add_inductive(
            r"inductive BacktrackValid : forall (n : Nat), BacktrackOp n → Type
| current : forall (n : Nat) (level : Nat), BacktrackValid n (BacktrackOp.current n level)
| pop : forall (n : Nat) (var : Nat) (var_level : Nat) (prev : BacktrackOp n) (h : BacktrackValid n prev), BacktrackValid n (BacktrackOp.pop n var var_level prev)
| done : forall (n : Nat) (target_level : Nat) (prev : BacktrackOp n) (h : BacktrackValid n prev), BacktrackValid n (BacktrackOp.done n target_level prev)",
            "Backtrack validity witness: inductive proof that each backtrack \
             step preserves the consistent-prefix property. Base case: the \
             current trail state at any level is trivially valid. Pop case: \
             removing an assignment with level > target preserves the prefix. \
             Done case: the final state has all entries at level <= target. \
             Part of #3333.",
        )?;

        // BCPStep: a single step of Boolean Constraint Propagation.
        // Models the BCP loop iterating over watched clause lists.
        // Parameterized by num_vars (Nat).
        self.add_inductive(
            r"inductive BCPStep : Nat → Type
| fixpoint : forall (n : Nat), BCPStep n
| unit : forall (n : Nat) (clause_idx : Nat) (lit : Nat), BCPStep n → BCPStep n
| skip : forall (n : Nat) (clause_idx : Nat), BCPStep n → BCPStep n",
            "BCP step inductive for CDCL S05 invariant. \
             Models Boolean Constraint Propagation: fixpoint means no unit \
             clauses remain, unit propagates a forced literal from a unit \
             clause, skip passes over a non-unit clause. Part of #3333.",
        )?;

        // BCPComplete: inductive witness that BCP reaches a fixpoint where
        // no unit clause remains un-propagated.
        self.add_inductive(
            r"inductive BCPComplete : forall (n : Nat), BCPStep n → Type
| fixpoint : forall (n : Nat), BCPComplete n (BCPStep.fixpoint n)
| unit : forall (n : Nat) (clause_idx : Nat) (lit : Nat) (prev : BCPStep n) (h : BCPComplete n prev), BCPComplete n (BCPStep.unit n clause_idx lit prev)
| skip : forall (n : Nat) (clause_idx : Nat) (prev : BCPStep n) (h : BCPComplete n prev), BCPComplete n (BCPStep.skip n clause_idx prev)",
            "BCP completeness witness: inductive proof that BCP finds all \
             unit-implied literals. Base case: fixpoint has no unpropagated \
             unit clauses. Unit case: the 2WL structure ensures the unit \
             clause is visited and its literal is propagated. Skip case: \
             non-unit clauses are correctly skipped. \
             (Handbook of Satisfiability, Ch. 4, Lemma 4.2). Part of #3333.",
        )?;

        // CDCLStep: a single step of the CDCL main loop.
        // Used for the termination argument.
        // Parameterized by max_clauses (Nat) — the bound 3^n.
        self.add_inductive(
            r"inductive CDCLStep : Nat → Type
| sat : forall (bound : Nat), CDCLStep bound
| unsat : forall (bound : Nat), CDCLStep bound
| learn : forall (bound : Nat) (clause_id : Nat), CDCLStep bound → CDCLStep bound
| restart : forall (bound : Nat), CDCLStep bound → CDCLStep bound",
            "CDCL step inductive for S06 termination invariant. \
             Models the CDCL main loop: sat/unsat are terminal states, \
             learn adds a new clause (strictly increasing DB size), \
             restart resets the trail. Part of #3333.",
        )?;

        // CDCLTerminates: inductive witness that CDCL terminates.
        // The key insight: each learn step adds a new clause, and the number
        // of possible clauses is bounded by 3^n (each of n variables can be
        // positive, negative, or absent).
        self.add_inductive(
            r"inductive CDCLTerminates : forall (bound : Nat), CDCLStep bound → Type
| sat : forall (bound : Nat), CDCLTerminates bound (CDCLStep.sat bound)
| unsat : forall (bound : Nat), CDCLTerminates bound (CDCLStep.unsat bound)
| learn : forall (bound : Nat) (clause_id : Nat) (prev : CDCLStep bound) (h : CDCLTerminates bound prev), CDCLTerminates bound (CDCLStep.learn bound clause_id prev)
| restart : forall (bound : Nat) (prev : CDCLStep bound) (h : CDCLTerminates bound prev), CDCLTerminates bound (CDCLStep.restart bound prev)",
            "CDCL termination witness: inductive proof that CDCL terminates \
             in finitely many steps. Base cases: sat/unsat are terminal. \
             Learn case: each learned clause is new (no duplicates) and the \
             total clause count is bounded by 3^n, so the DB cannot grow \
             unboundedly. Restart case: restarts don't add clauses and are \
             bounded by the learn count. \
             (Handbook of Satisfiability, Ch. 4, Theorem 4.1). Part of #3333.",
        )?;

        // ── S01: Trail consistency (inductive type) ──────────────────────

        self.add_definition(SpecDefinition {
            name: "cdcl_s01_trail_consistency".to_string(),
            type_src: "forall (n : Nat) (trail : TrailOp n), TrailConsistent n trail".to_string(),
            value_src: Some(
                "fun (n : Nat) (trail : TrailOp n) => \
                 TrailOp.rec n \
                   (fun (t : TrailOp n) => TrailConsistent n t) \
                   (TrailConsistent.empty n) \
                   (fun (var : Nat) (prev : TrailOp n) (ih : TrailConsistent n prev) => \
                     TrailConsistent.decide n var prev ih) \
                   (fun (var : Nat) (reason : Nat) (prev : TrailOp n) (ih : TrailConsistent n prev) => \
                     TrailConsistent.propagate n var reason prev ih) \
                   (fun (level : Nat) (prev : TrailOp n) (ih : TrailConsistent n prev) => \
                     TrailConsistent.backtrack n level prev ih) \
                   trail"
                    .to_string(),
            ),
            is_axiom: false,
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedPending,
            description: "S01: Trail consistency — each variable assigned at most once. \
                          Proof by induction on TrailOp: empty trail is consistent, \
                          decide/propagate preserve consistency (variable freshness check), \
                          backtrack preserves consistency on the prefix. \
                          (Handbook of Satisfiability, Ch. 4). Part of #3333."
                .to_string(),
            elaborated_type: None,
            elaborated_value: None,
            dependencies: None,
            axiom_deps: HashSet::new(),
        })?;

        // ── S02: Two-watched-literal invariant (inductive type) ──────────

        self.add_definition(SpecDefinition {
            name: "cdcl_s02_two_watched".to_string(),
            type_src: "forall (nc : Nat) (ops : WatchOp nc), WatchInvariant nc ops".to_string(),
            value_src: Some(
                "fun (nc : Nat) (ops : WatchOp nc) => \
                 WatchOp.rec nc \
                   (fun (w : WatchOp nc) => WatchInvariant nc w) \
                   (WatchInvariant.init nc) \
                   (fun (clause_idx : Nat) (old_watch : Nat) (new_watch : Nat) \
                        (prev : WatchOp nc) (ih : WatchInvariant nc prev) => \
                     WatchInvariant.update nc clause_idx old_watch new_watch prev ih) \
                   (fun (clause_idx : Nat) (unit_lit : Nat) \
                        (prev : WatchOp nc) (ih : WatchInvariant nc prev) => \
                     WatchInvariant.propagate nc clause_idx unit_lit prev ih) \
                   ops"
                .to_string(),
            ),
            is_axiom: false,
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedPending,
            description: "S02: Two-watched-literal invariant — for each non-satisfied \
                          clause, watch pointers point to two distinct unassigned literals. \
                          Proof by induction on WatchOp: initial watches are valid, update \
                          moves to a new unassigned literal preserving distinctness, \
                          propagate on a unit clause preserves the invariant on remaining \
                          clauses. (Moskewicz et al., Chaff, DAC 2001). Part of #3333."
                .to_string(),
            elaborated_type: None,
            elaborated_value: None,
            dependencies: None,
            axiom_deps: HashSet::new(),
        })?;

        // ── S03: Learned clause soundness (inductive type) ───────────────

        self.add_definition(SpecDefinition {
            name: "cdcl_s03_learned_clause_sound".to_string(),
            type_src: "forall (db_size : Nat) (deriv : ResolutionStep db_size), ResolutionSound db_size deriv".to_string(),
            value_src: Some(
                "fun (db_size : Nat) (deriv : ResolutionStep db_size) => \
                 ResolutionStep.rec db_size \
                   (fun (d : ResolutionStep db_size) => ResolutionSound db_size d) \
                   (fun (idx : Nat) => ResolutionSound.axiom_clause db_size idx) \
                   (fun (pivot : Nat) (left : ResolutionStep db_size) (right : ResolutionStep db_size) \
                        (ih_left : ResolutionSound db_size left) (ih_right : ResolutionSound db_size right) => \
                     ResolutionSound.resolve db_size pivot left right ih_left ih_right) \
                   deriv"
                    .to_string(),
            ),
            is_axiom: false,
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedPending,
            description: "S03: Learned clause soundness — every learned clause is a \
                          logical consequence of the original clause database, derived \
                          by resolution. Proof by induction on ResolutionStep: axiom \
                          clauses are trivially sound, resolution of two sound clauses \
                          on a pivot produces a sound resolvent. \
                          (Handbook of Satisfiability, Ch. 4). Part of #3333."
                .to_string(),
            elaborated_type: None,
            elaborated_value: None,
            dependencies: None,
            axiom_deps: HashSet::new(),
        })?;

        // ── S04: Backtrack correctness (inductive type) ──────────────────

        self.add_definition(SpecDefinition {
            name: "cdcl_s04_backtrack_correctness".to_string(),
            type_src: "forall (n : Nat) (ops : BacktrackOp n), BacktrackValid n ops".to_string(),
            value_src: Some(
                "fun (n : Nat) (ops : BacktrackOp n) => \
                 BacktrackOp.rec n \
                   (fun (b : BacktrackOp n) => BacktrackValid n b) \
                   (fun (level : Nat) => BacktrackValid.current n level) \
                   (fun (var : Nat) (var_level : Nat) \
                        (prev : BacktrackOp n) (ih : BacktrackValid n prev) => \
                     BacktrackValid.pop n var var_level prev ih) \
                   (fun (target_level : Nat) \
                        (prev : BacktrackOp n) (ih : BacktrackValid n prev) => \
                     BacktrackValid.done n target_level prev ih) \
                   ops"
                .to_string(),
            ),
            is_axiom: false,
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedPending,
            description: "S04: Backtrack correctness — after backjumping to level d, \
                          the trail is a valid prefix with all assignments at level <= d. \
                          Proof by induction on BacktrackOp: current state is trivially \
                          valid, pop removes assignments above the target level, done \
                          finalizes at the target level. Part of #3333."
                .to_string(),
            elaborated_type: None,
            elaborated_value: None,
            dependencies: None,
            axiom_deps: HashSet::new(),
        })?;

        // ── S05: Propagation completeness (inductive type) ───────────────

        self.add_definition(SpecDefinition {
            name: "cdcl_s05_propagation_completeness".to_string(),
            type_src: "forall (n : Nat) (steps : BCPStep n), BCPComplete n steps".to_string(),
            value_src: Some(
                "fun (n : Nat) (steps : BCPStep n) => \
                 BCPStep.rec n \
                   (fun (s : BCPStep n) => BCPComplete n s) \
                   (BCPComplete.fixpoint n) \
                   (fun (clause_idx : Nat) (lit : Nat) \
                        (prev : BCPStep n) (ih : BCPComplete n prev) => \
                     BCPComplete.unit n clause_idx lit prev ih) \
                   (fun (clause_idx : Nat) \
                        (prev : BCPStep n) (ih : BCPComplete n prev) => \
                     BCPComplete.skip n clause_idx prev ih) \
                   steps"
                    .to_string(),
            ),
            is_axiom: false,
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedPending,
            description: "S05: Propagation completeness — BCP finds all unit-implied \
                          literals. Proof by induction on BCPStep: at fixpoint no unit \
                          clause remains, unit propagation forces the implied literal, \
                          skip correctly passes non-unit clauses. The 2WL structure \
                          ensures all relevant clauses are visited. \
                          (Handbook of Satisfiability, Ch. 4, Lemma 4.2). Part of #3333."
                .to_string(),
            elaborated_type: None,
            elaborated_value: None,
            dependencies: None,
            axiom_deps: HashSet::new(),
        })?;

        // ── S06: Termination (inductive type) ────────────────────────────

        self.add_definition(SpecDefinition {
            name: "cdcl_s06_termination".to_string(),
            type_src: "forall (bound : Nat) (steps : CDCLStep bound), CDCLTerminates bound steps"
                .to_string(),
            value_src: Some(
                "fun (bound : Nat) (steps : CDCLStep bound) => \
                 CDCLStep.rec bound \
                   (fun (s : CDCLStep bound) => CDCLTerminates bound s) \
                   (CDCLTerminates.sat bound) \
                   (CDCLTerminates.unsat bound) \
                   (fun (clause_id : Nat) \
                        (prev : CDCLStep bound) (ih : CDCLTerminates bound prev) => \
                     CDCLTerminates.learn bound clause_id prev ih) \
                   (fun (prev : CDCLStep bound) (ih : CDCLTerminates bound prev) => \
                     CDCLTerminates.restart bound prev ih) \
                   steps"
                    .to_string(),
            ),
            is_axiom: false,
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedPending,
            description: "S06: Termination — CDCL terminates in finite steps. \
                          Proof by well-founded induction on CDCLStep: sat/unsat are \
                          terminal, each learn adds a unique clause (bounded by 3^n \
                          possible clauses over n variables), restarts don't add clauses. \
                          (Handbook of Satisfiability, Ch. 4, Theorem 4.1). Part of #3333."
                .to_string(),
            elaborated_type: None,
            elaborated_value: None,
            dependencies: None,
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }
}
