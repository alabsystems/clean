// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Kernel-verified proof promotion tests for T01-T20.
//!
//! Each of the twenty interval arithmetic theorems is registered in the spec
//! as a `DerivedLemma` with `DerivedPending` status, and a matching proof term
//! is registered in the `ProofLibrary`. The promote pipeline elaborates the
//! proof term, type-checks it through the kernel against the declared theorem
//! type, and — when the resulting dependency set is empty — promotes the
//! definition to `DerivedProved` with zero domain axioms.
//!
//! Part of #3362.

use crate::proofs::promote::{promote_single, promote_with_proof_term};
use crate::proofs::ProofLibrary;
use crate::spec::{AxiomCategory, ProofStatus, Specification};

use clean_kernel::test_utils::run_with_stack;

const STACK_SIZE: usize = 32 * 1024 * 1024;

/// The 20 interval arithmetic theorem names, in T01..T20 order.
const T_NAMES: &[&str] = &[
    "ia_t01_add_containment",
    "ia_t02_sub_containment",
    "ia_t03_neg_containment",
    "ia_t04_mul_containment",
    "ia_t05_div_containment",
    "ia_t06_abs_containment",
    "ia_t07_pow_containment",
    "ia_t08_sqrt_containment",
    "ia_t09_intersection_containment",
    "ia_t10_hull_containment",
    "ia_t11_subset_transitivity",
    "ia_t12_containment_transitivity",
    "ia_t13_point_interval",
    "ia_t14_contains_reflexive",
    "ia_t15_add_width",
    "ia_t16_sub_width",
    "ia_t17_neg_width",
    "ia_t18_add_commutativity",
    "ia_t19_mul_commutativity",
    "ia_t20_add_associativity",
];

/// Build a fresh interval-arith-only spec inside the larger-stack test thread.
fn build_interval_spec() -> Specification {
    Specification::new_interval_arith_test_spec().expect("interval arith spec should build")
}

#[test]
fn test_all_20_theorems_registered_as_derived_pending() {
    run_with_stack(STACK_SIZE, || {
        let spec = build_interval_spec();
        for name in T_NAMES {
            let def = spec
                .get_definition(name)
                .unwrap_or_else(|| panic!("definition {name} should be registered"));
            assert_eq!(
                def.category,
                AxiomCategory::DerivedLemma,
                "{name} should be a DerivedLemma"
            );
            assert_eq!(
                def.proof_status,
                ProofStatus::DerivedPending,
                "{name} should start as DerivedPending"
            );
        }
    });
}

#[test]
fn test_all_20_proofs_registered_in_library() {
    // ProofLibrary construction does not elaborate; it just stores proof
    // source. Safe to run outside the larger-stack thread.
    let library = ProofLibrary::new();
    for name in T_NAMES {
        assert!(
            library.get(name).is_some(),
            "ProofLibrary should contain a proof for {name}"
        );
    }
}

#[test]
fn test_t01_add_containment_promotes_with_zero_axioms() {
    run_with_stack(STACK_SIZE, || {
        let mut spec = build_interval_spec();
        let library = ProofLibrary::new();
        let attempt = promote_single(&mut spec, &library, "ia_t01_add_containment")
            .expect("T01 promotion should succeed");
        assert!(attempt.promoted, "T01 should be promoted to DerivedProved");
        assert_eq!(attempt.new_status, ProofStatus::DerivedProved);
        assert!(
            attempt.axiom_deps.is_empty(),
            "T01 should have zero axiom dependencies, found: {:?}",
            attempt.axiom_deps
        );
        let def = spec
            .get_definition("ia_t01_add_containment")
            .expect("T01 should still exist after promotion");
        assert_eq!(def.proof_status, ProofStatus::DerivedProved);
        assert!(def.axiom_deps.is_empty());
    });
}

#[test]
fn test_all_20_theorems_promote_with_zero_axioms() {
    run_with_stack(STACK_SIZE, || {
        let mut spec = build_interval_spec();
        let library = ProofLibrary::new();
        let mut promoted = 0usize;
        let mut failures: Vec<String> = Vec::new();
        let mut axiom_deps_found: Vec<(String, Vec<String>)> = Vec::new();
        for name in T_NAMES {
            match promote_single(&mut spec, &library, name) {
                Ok(attempt) => {
                    if attempt.promoted && attempt.axiom_deps.is_empty() {
                        promoted += 1;
                    } else if !attempt.axiom_deps.is_empty() {
                        let mut deps: Vec<String> = attempt.axiom_deps.iter().cloned().collect();
                        deps.sort();
                        axiom_deps_found.push(((*name).to_string(), deps));
                    } else if let Some(err) = attempt.error {
                        failures.push(format!("{name}: {err}"));
                    } else {
                        failures.push(format!(
                            "{name}: not promoted (status={:?})",
                            attempt.new_status
                        ));
                    }
                }
                Err(e) => failures.push(format!("{name}: promote error {e}")),
            }
        }
        assert!(
            failures.is_empty(),
            "Promotion failures:\n  {}",
            failures.join("\n  ")
        );
        assert!(
            axiom_deps_found.is_empty(),
            "Theorems with nonempty axiom deps:\n  {}",
            axiom_deps_found
                .iter()
                .map(|(n, d)| format!("{n}: {d:?}"))
                .collect::<Vec<_>>()
                .join("\n  ")
        );
        assert_eq!(
            promoted, 20,
            "all 20 theorems should promote with zero deps"
        );
    });
}

#[test]
fn test_promote_with_proof_term_t02() {
    run_with_stack(STACK_SIZE, || {
        let mut spec = build_interval_spec();
        // Promote T02 by supplying the proof term source directly through
        // promote_with_proof_term, bypassing the library lookup.
        let attempt = promote_with_proof_term(
            &mut spec,
            "ia_t02_sub_containment",
            "fun (n : Nat) => IvContainSound.sub n",
        )
        .expect("T02 proof term promotion should succeed");
        assert!(attempt.promoted);
        assert_eq!(attempt.new_status, ProofStatus::DerivedProved);
        assert!(attempt.axiom_deps.is_empty());
    });
}

#[test]
fn test_promote_status_is_dynamic_not_hardcoded() {
    // AC #2: ProofStatus computed dynamically from kernel verification, not
    // hardcoded. At spec build time every T0x is DerivedPending; after the
    // promote pipeline, every T0x is DerivedProved. The flip is the signature
    // of a real kernel round-trip: if the proof term failed to elaborate or
    // type-check, the promote pipeline would leave the definition untouched.
    run_with_stack(STACK_SIZE, || {
        let mut spec = build_interval_spec();
        let library = ProofLibrary::new();

        // Before promotion: every T0x is DerivedPending.
        for name in T_NAMES {
            let def = spec.get_definition(name).unwrap();
            assert_eq!(
                def.proof_status,
                ProofStatus::DerivedPending,
                "{name} should be DerivedPending before promotion"
            );
        }

        // Run promote on every T0x.
        for name in T_NAMES {
            let _ = promote_single(&mut spec, &library, name).expect("promote should succeed");
        }

        // After promotion: every T0x is DerivedProved.
        for name in T_NAMES {
            let def = spec.get_definition(name).unwrap();
            assert_eq!(
                def.proof_status,
                ProofStatus::DerivedProved,
                "{name} should be DerivedProved after promotion"
            );
            assert!(
                def.axiom_deps.is_empty(),
                "{name} should have empty axiom_deps after promotion"
            );
        }
    });
}

#[test]
fn test_compute_proof_statuses_dynamically_20_proved_0_pending() {
    // AC #2: ProofStatus computed dynamically from kernel verification, not
    // hardcoded. This test calls the dynamic helper, which builds a fresh
    // interval-arith spec and runs the full kernel promote pipeline on every
    // T0x. The resulting statuses are what the kernel actually accepted.
    run_with_stack(STACK_SIZE, || {
        let dynamic = super::theorems_promote::compute_proof_statuses_dynamically()
            .expect("dynamic proof-status computation should succeed");
        assert_eq!(
            dynamic.len(),
            20,
            "dynamic proof-status vector must cover all 20 theorems"
        );
        let proved = dynamic
            .iter()
            .filter(|(_, _, s, _)| matches!(s, ProofStatus::DerivedProved))
            .count();
        let pending = dynamic
            .iter()
            .filter(|(_, _, s, _)| matches!(s, ProofStatus::DerivedPending))
            .count();
        let nonempty_deps: Vec<_> = dynamic
            .iter()
            .filter(|(_, _, _, d)| !d.is_empty())
            .collect();
        assert!(
            nonempty_deps.is_empty(),
            "expected zero axiom-dep theorems, found: {nonempty_deps:?}"
        );
        assert_eq!(proved, 20, "expected all 20 theorems to be DerivedProved");
        assert_eq!(pending, 0, "expected zero DerivedPending theorems");
    });
}

#[test]
fn test_wrong_proof_term_fails_verification() {
    // Sanity check: if we supply an ill-typed proof term, promote_with_proof_term
    // must REJECT it (verification failure). This proves the kernel is doing real
    // work — the promotion signal is not vacuous.
    run_with_stack(STACK_SIZE, || {
        let mut spec = build_interval_spec();
        // Supply an obviously wrong proof term — a Nat constant — for T01.
        let result = promote_with_proof_term(&mut spec, "ia_t01_add_containment", "Nat.zero");
        assert!(
            result.is_err(),
            "ill-typed proof term for T01 should fail kernel verification"
        );
        // AndType the status must remain DerivedPending.
        let def = spec.get_definition("ia_t01_add_containment").unwrap();
        assert_eq!(
            def.proof_status,
            ProofStatus::DerivedPending,
            "failed promotion must leave status unchanged"
        );
    });
}
