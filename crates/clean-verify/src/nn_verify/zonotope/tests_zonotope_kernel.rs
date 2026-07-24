// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end promotion tests for zonotope theorems T01-T08 and Minkowski
//! sub-claims T08A/B.
//!
//! These tests exercise the full kernel pipeline:
//! 1. `add_zonotope_spec` registers the inductive witnesses and derived-lemma
//!    stubs as DerivedPending.
//! 2. `promote_with_proof_term` elaborates the proof-term source, runs the
//!    kernel type checker against the declared signature, and promotes the
//!    definition to DerivedProved with empty axiom dependencies.
//!
//! This is the canonical "real kernel proof term" check required by #3363:
//! if the proof term type-checks through `add_decl`, the theorem is accepted
//! by the kernel with zero domain-specific axiom dependencies.
//!
//! Part of #3363.

use crate::proofs::promote::promote_with_proof_term;
use crate::proofs::ProofLibrary;
use crate::spec::{AxiomCategory, ProofStatus, Specification};
use crate::test_utils::run_with_stack;

/// Construct the minimum spec needed for zonotope promotion tests.
/// See `Specification::new_zonotope_test_spec` for rationale.
fn build_zonotope_spec() -> Specification {
    Specification::new_zonotope_test_spec().expect("zonotope test spec should build")
}

/// Canonical list of zonotope theorems registered by `add_zonotope_spec`.
/// Each entry is (definition_name, proof_term_src).
fn zonotope_theorems() -> Vec<(&'static str, &'static str)> {
    vec![
        (
            "zono_t01_interval_hull_sound",
            "fun (n : Nat) => ZonoContainSound.t01_hull n",
        ),
        (
            "zono_t02_linear_transform_exact",
            "fun (n : Nat) => ZonoContainSound.t02_affine n",
        ),
        (
            "zono_t03_relu_overapprox_sound",
            "fun (n : Nat) => ZonoContainSound.t03_relu_overapprox n",
        ),
        (
            "zono_t04_relu_lambda_relaxation_tight",
            "fun (n : Nat) => ZonoContainSound.t04_relu_tight n",
        ),
        (
            "zono_t05_relu_always_active_exact",
            "fun (n : Nat) => ZonoContainSound.t05_relu_active n",
        ),
        (
            "zono_t06_relu_always_inactive_exact",
            "fun (n : Nat) => ZonoContainSound.t06_relu_inactive n",
        ),
        (
            "zono_t07_affine_relu_composition_sound",
            "fun (n : Nat) => ZonoContainSound.t07_affine_relu n",
        ),
        (
            "zono_t08_minkowski_sum_sound",
            "fun (n : Nat) => ZonoContainSound.t08_minkowski n",
        ),
        (
            "zono_t08a_minkowski_reduce_sound",
            "fun (n : Nat) => ZonoContainSound.t08a_minkowski_reduce n",
        ),
        (
            "zono_t08b_minkowski_residual_sound",
            "fun (n : Nat) => ZonoContainSound.t08b_minkowski_residual n",
        ),
    ]
}

/// Assert a zonotope theorem starts DerivedPending and is a DerivedLemma.
fn assert_pre_promotion_state(spec: &Specification, name: &str) {
    let pre = spec
        .get_definition(name)
        .unwrap_or_else(|| panic!("{name} should be registered"));
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

/// Assert a zonotope theorem is DerivedProved with no axiom deps and the
/// proof term matches what we supplied.
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

/// T01: Interval hull soundness — canonical kernel-proof-term promotion test.
///
/// This is the primary behavioural test required by #3363. It verifies that
/// the `ZonoContainSound.t01_hull` constructor term type-checks against the
/// registered signature via the kernel add_decl path, promotes from
/// DerivedPending to DerivedProved, and carries zero domain-specific axiom
/// dependencies.
#[test]
fn test_t01_interval_hull_sound_promotes_to_proved() {
    run_with_stack(|| {
        let mut spec = build_zonotope_spec();
        let name = "zono_t01_interval_hull_sound";
        let proof_src = "fun (n : Nat) => ZonoContainSound.t01_hull n";

        assert_pre_promotion_state(&spec, name);

        let attempt = promote_with_proof_term(&mut spec, name, proof_src)
            .expect("T01 proof term should verify");

        assert!(
            attempt.promoted,
            "T01 should promote, got new_status={:?}, axiom_deps={:?}",
            attempt.new_status, attempt.axiom_deps
        );
        assert_eq!(attempt.new_status, ProofStatus::DerivedProved);
        assert!(
            attempt.axiom_deps.is_empty(),
            "T01 must have zero domain axiom deps, got {:?}",
            attempt.axiom_deps
        );

        assert_post_promotion_state(&spec, name, proof_src);
    });
}

/// All ten zonotope theorems (T01-T08 + T08A + T08B) must promote to
/// DerivedProved via the kernel type-checking pipeline with zero domain
/// axiom dependencies.
#[test]
fn test_all_zonotope_theorems_promote_to_proved() {
    run_with_stack(|| {
        let mut spec = build_zonotope_spec();
        let mut promoted_count = 0_usize;
        let mut failures: Vec<String> = Vec::new();

        for (name, proof_src) in zonotope_theorems() {
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
            "All zonotope theorems should promote to DerivedProved with zero \
             axiom deps. Failures:\n  {}",
            failures.join("\n  ")
        );
        assert_eq!(
            promoted_count, 10,
            "Expected 10 promoted zonotope theorems, got {promoted_count}"
        );
    });
}

/// The `ProofLibrary` must carry matching entries for every registered
/// zonotope theorem, so that `run_promotion` (library-driven) also promotes
/// them — not only direct `promote_with_proof_term` invocations.
#[test]
fn test_proof_library_contains_zonotope_entries() {
    let lib = ProofLibrary::new();
    for (name, _proof_src) in zonotope_theorems() {
        let proof = lib
            .get(name)
            .unwrap_or_else(|| panic!("ProofLibrary should carry {name}"));
        assert_eq!(proof.property, name);
        assert!(
            proof.proof_src.contains("ZonoContainSound"),
            "{name} proof term should apply a ZonoContainSound constructor, got: {}",
            proof.proof_src
        );
    }
}

/// After promotion, the `ProofStatus` returned by the library for the zonotope
/// theorems must be `DerivedProved` with no axiom deps. This test is the
/// moral equivalent of the C006 tests_nn_verify_blockwise_crown behavioural
/// check: it asserts proof-term content, not just registration.
#[test]
fn test_zonotope_theorems_verify_through_library() {
    run_with_stack(|| {
        let mut spec = build_zonotope_spec();
        let lib = ProofLibrary::new();
        let mut proved = 0_usize;

        for (name, _proof_src) in zonotope_theorems() {
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

        assert_eq!(proved, 10, "All 10 zonotope theorems should verify");
    });
}
