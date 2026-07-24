// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end kernel-promotion tests for CDCL SAT invariants S01-S06.
//!
//! These tests exercise the full kernel pipeline for the six CDCL
//! soundness theorems from epic #3333 / issue #3364:
//!
//! 1. `add_cdcl_sat_spec` registers the inductive witnesses
//!    (`TrailOp`, `WatchOp`, `ResolutionStep`, `BacktrackOp`, `BCPStep`,
//!    `CDCLStep` and their `TrailConsistent` / `WatchInvariant` /
//!    `ResolutionSound` / `BacktrackValid` / `BCPComplete` /
//!    `CDCLTerminates` witnesses) plus the six `DerivedLemma` stubs
//!    (`cdcl_s01_trail_consistency` … `cdcl_s06_termination`).
//! 2. `promote_with_proof_term` elaborates the inductive proof-term
//!    source (a structural recursion via `<Op>.rec`), runs the kernel
//!    type-checker against the declared `forall (…), Witness …`
//!    signature, and promotes each definition to `DerivedProved` with
//!    an empty `axiom_deps` set.
//!
//! This is the canonical "real kernel proof term" behavioural check
//! required by #3364. If the proof terms type-check through `add_decl`
//! via the promotion pipeline, the six CDCL invariants are accepted
//! by the kernel with zero domain-specific axiom dependencies.
//!
//! Each proof is a closed recursor application — no `Eq.refl`
//! placeholders, no trust escape hatches. The proof terms mirror the
//! inductive structure of the CDCL state transitions (trail extension,
//! watch pointer updates, resolution derivations, backtracking,
//! BCP steps, main-loop steps) and discharge the universally
//! quantified soundness statements by structural induction.
//!
//! Part of #3364.

use crate::proofs::promote::promote_with_proof_term;
use crate::proofs::ProofLibrary;
use crate::spec::{AxiomCategory, ProofStatus, Specification};
use crate::test_utils::run_with_stack;

/// Construct the minimum spec needed for CDCL S01-S06 promotion tests.
/// See `Specification::new_cdcl_test_spec` for rationale.
fn build_cdcl_spec() -> Specification {
    Specification::new_cdcl_test_spec().expect("CDCL test spec should build")
}

/// S01 `TrailOp.rec` proof-term source.
fn s01_proof_src() -> &'static str {
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
}

/// S02 `WatchOp.rec` proof-term source.
fn s02_proof_src() -> &'static str {
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
}

/// S03 `ResolutionStep.rec` proof-term source.
fn s03_proof_src() -> &'static str {
    "fun (db_size : Nat) (deriv : ResolutionStep db_size) => \
     ResolutionStep.rec db_size \
       (fun (d : ResolutionStep db_size) => ResolutionSound db_size d) \
       (fun (idx : Nat) => ResolutionSound.axiom_clause db_size idx) \
       (fun (pivot : Nat) (left : ResolutionStep db_size) (right : ResolutionStep db_size) \
            (ih_left : ResolutionSound db_size left) (ih_right : ResolutionSound db_size right) => \
         ResolutionSound.resolve db_size pivot left right ih_left ih_right) \
       deriv"
}

/// S04 `BacktrackOp.rec` proof-term source.
fn s04_proof_src() -> &'static str {
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
}

/// S05 `BCPStep.rec` proof-term source.
fn s05_proof_src() -> &'static str {
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
}

/// S06 `CDCLStep.rec` proof-term source.
fn s06_proof_src() -> &'static str {
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
}

/// Canonical list of CDCL SAT theorems registered by `add_cdcl_sat_spec`.
/// Each entry is `(definition_name, proof_term_src)` and matches the
/// matching entry in `proofs::library_cdcl_sat::add_cdcl_sat_proofs`.
fn cdcl_theorems() -> Vec<(&'static str, &'static str)> {
    vec![
        ("cdcl_s01_trail_consistency", s01_proof_src()),
        ("cdcl_s02_two_watched", s02_proof_src()),
        ("cdcl_s03_learned_clause_sound", s03_proof_src()),
        ("cdcl_s04_backtrack_correctness", s04_proof_src()),
        ("cdcl_s05_propagation_completeness", s05_proof_src()),
        ("cdcl_s06_termination", s06_proof_src()),
    ]
}

/// Assert a CDCL theorem starts `DerivedPending` and is a `DerivedLemma`.
fn assert_pre_promotion_state(spec: &Specification, name: &str) {
    let pre = spec
        .get_definition(name)
        .unwrap_or_else(|| panic!("{name} should be registered by add_cdcl_sat_spec"));
    assert_eq!(
        pre.category,
        AxiomCategory::DerivedLemma,
        "{name} must be a DerivedLemma"
    );
    assert_eq!(
        pre.proof_status,
        ProofStatus::DerivedPending,
        "{name} must start DerivedPending"
    );
}

/// Assert a CDCL theorem is `DerivedProved` with no axiom deps and the
/// stored `value_src` matches the supplied proof term.
fn assert_post_promotion_state(spec: &Specification, name: &str, proof_src: &str) {
    let post = spec
        .get_definition(name)
        .unwrap_or_else(|| panic!("{name} must still exist post-promotion"));
    assert_eq!(
        post.proof_status,
        ProofStatus::DerivedProved,
        "{name} proof_status should be updated on the spec"
    );
    assert_eq!(
        post.value_src.as_deref(),
        Some(proof_src),
        "{name} value_src should match the verified proof term"
    );
    assert!(
        post.axiom_deps.is_empty(),
        "{name} axiom_deps should be cleared after promotion"
    );
}

/// S01: Trail consistency — canonical kernel-proof-term promotion test.
///
/// Verifies the `TrailOp.rec` structural-induction term type-checks
/// against the registered `forall (n : Nat) (trail : TrailOp n),
/// TrailConsistent n trail` signature, promotes from `DerivedPending`
/// to `DerivedProved`, and carries zero domain-specific axiom deps.
/// This is the highest-priority acceptance criterion for #3364.
#[test]
fn test_s01_trail_consistency_promotes_to_proved() {
    run_with_stack(|| {
        let mut spec = build_cdcl_spec();
        let (name, proof_src) = cdcl_theorems()[0];
        assert_eq!(name, "cdcl_s01_trail_consistency");

        assert_pre_promotion_state(&spec, name);

        let attempt = promote_with_proof_term(&mut spec, name, proof_src)
            .expect("S01 proof term should verify");

        assert!(
            attempt.promoted,
            "S01 should promote, got new_status={:?}, axiom_deps={:?}",
            attempt.new_status, attempt.axiom_deps
        );
        assert_eq!(attempt.new_status, ProofStatus::DerivedProved);
        assert!(
            attempt.axiom_deps.is_empty(),
            "S01 must have zero domain axiom deps, got {:?}",
            attempt.axiom_deps
        );

        assert_post_promotion_state(&spec, name, proof_src);
    });
}

/// S03: Learned clause soundness — second highest-priority acceptance
/// criterion for #3364 (the resolution-chain induction).
#[test]
fn test_s03_learned_clause_sound_promotes_to_proved() {
    run_with_stack(|| {
        let mut spec = build_cdcl_spec();
        let (name, proof_src) = cdcl_theorems()[2];
        assert_eq!(name, "cdcl_s03_learned_clause_sound");

        assert_pre_promotion_state(&spec, name);

        let attempt = promote_with_proof_term(&mut spec, name, proof_src)
            .expect("S03 proof term should verify");

        assert!(
            attempt.promoted,
            "S03 should promote, got new_status={:?}, axiom_deps={:?}",
            attempt.new_status, attempt.axiom_deps
        );
        assert_eq!(attempt.new_status, ProofStatus::DerivedProved);
        assert!(
            attempt.axiom_deps.is_empty(),
            "S03 must have zero domain axiom deps, got {:?}",
            attempt.axiom_deps
        );

        assert_post_promotion_state(&spec, name, proof_src);
    });
}

/// All six CDCL invariants (S01-S06) must promote to `DerivedProved`
/// via the kernel type-checking pipeline with zero domain axiom
/// dependencies.
#[test]
fn test_all_cdcl_theorems_promote_to_proved() {
    run_with_stack(|| {
        let mut spec = build_cdcl_spec();
        let mut promoted_count = 0_usize;
        let mut failures: Vec<String> = Vec::new();

        for (name, proof_src) in cdcl_theorems() {
            let result = promote_with_proof_term(&mut spec, name, proof_src);
            match result {
                Ok(attempt) if attempt.promoted && attempt.axiom_deps.is_empty() => {
                    promoted_count += 1;
                }
                Ok(attempt) => {
                    failures.push(format!(
                        "{name}: promoted={}, status={:?}, axiom_deps={:?}",
                        attempt.promoted, attempt.new_status, attempt.axiom_deps
                    ));
                }
                Err(err) => {
                    failures.push(format!("{name}: error={err}"));
                }
            }
        }

        assert!(
            failures.is_empty(),
            "All CDCL theorems should promote to DerivedProved with zero \
             axiom deps. Failures:\n  {}",
            failures.join("\n  ")
        );
        assert_eq!(
            promoted_count, 6,
            "Expected 6 promoted CDCL theorems, got {promoted_count}"
        );
    });
}

/// The `ProofLibrary` must carry matching entries for every registered
/// CDCL theorem — not just the `add_cdcl_sat_spec` inline
/// `value_src` — so that library-driven promotion (`run_promotion`,
/// `audit_dependencies`) also recognises S01-S06.
#[test]
fn test_proof_library_contains_cdcl_entries() {
    let lib = ProofLibrary::new();
    for (name, _proof_src) in cdcl_theorems() {
        let proof = lib
            .get(name)
            .unwrap_or_else(|| panic!("ProofLibrary should carry {name}"));
        assert_eq!(proof.property, name);
        // Each proof applies the corresponding recursor: TrailOp.rec,
        // WatchOp.rec, ResolutionStep.rec, BacktrackOp.rec, BCPStep.rec,
        // CDCLStep.rec. Verify the proof term actually invokes structural
        // induction rather than an Eq.refl placeholder.
        assert!(
            proof.proof_src.contains(".rec"),
            "{name} proof term should use structural induction via <Op>.rec, got: {}",
            proof.proof_src
        );
        assert!(
            !proof.proof_src.contains("Eq.refl"),
            "{name} proof term must not be an Eq.refl placeholder, got: {}",
            proof.proof_src
        );
    }
}

/// After promotion, the `ProofStatus` and `axiom_deps` returned by the
/// library's proof term for each CDCL invariant must match the
/// acceptance criteria: `DerivedProved` with an empty axiom set.
///
/// This is the library-driven analogue of
/// `test_all_cdcl_theorems_promote_to_proved`: it asserts that the
/// `library_cdcl_sat` source and `spec_registration` signature agree
/// and that `promote_with_proof_term` can consume the library term
/// as-is.
#[test]
fn test_cdcl_theorems_verify_through_library() {
    run_with_stack(|| {
        let mut spec = build_cdcl_spec();
        let lib = ProofLibrary::new();
        let mut proved = 0_usize;

        for (name, _proof_src) in cdcl_theorems() {
            let proof = lib.get(name).expect("library entry");
            let attempt = promote_with_proof_term(&mut spec, name, &proof.proof_src)
                .unwrap_or_else(|e| panic!("{name}: verification failed: {e}"));
            assert!(
                attempt.promoted,
                "{name} library proof must promote, got {:?} (deps={:?})",
                attempt.new_status, attempt.axiom_deps
            );
            assert!(
                attempt.axiom_deps.is_empty(),
                "{name} library proof must have zero axiom deps, got {:?}",
                attempt.axiom_deps
            );
            proved += 1;
        }

        assert_eq!(proved, 6, "All 6 CDCL theorems should verify");
    });
}
