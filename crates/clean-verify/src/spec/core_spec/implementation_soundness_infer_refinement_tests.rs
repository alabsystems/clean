// Copyright 2026 Andrew Yates.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use crate::spec::types::ProofStatus;
use crate::test_utils::build_spec_with_stack;

#[test]
fn test_infer_refinement_root_definitions_exist() {
    let spec = build_spec_with_stack();
    // Root module contains sort/bvar foundations + InferSoundAt motive
    for name in [
        "not_lt_zero_goal",
        "not_lt_zero",
        "is_closed_at_bvar_inv",
        "bvar_not_closed",
        "kernel_infer_const_sound",
        "kernel_infer_sort_result",
        "kernel_infer_sort_sound",
        "InferSoundAt",
    ] {
        assert!(
            spec.definitions().contains_key(name),
            "expected root infer refinement definition {name} to be registered"
        );
    }
}

#[test]
fn test_not_lt_zero_is_constructive() {
    let spec = build_spec_with_stack();
    let def = spec
        .definitions()
        .get("not_lt_zero")
        .expect("not_lt_zero should be registered");
    assert!(
        !def.is_axiom,
        "not_lt_zero should now be a derived definition (discharged via Lt.rec)"
    );
    assert_eq!(
        def.proof_status,
        ProofStatus::DerivedProved,
        "not_lt_zero should be fully constructive"
    );
    assert!(
        def.axiom_deps.is_empty(),
        "not_lt_zero should have no axiom deps: {:?}",
        def.axiom_deps
    );
    let deps = def
        .dependencies
        .as_ref()
        .expect("not_lt_zero should record dependencies");
    assert!(
        deps.contains("Lt.rec") && deps.contains("not_lt_zero_goal"),
        "not_lt_zero should use Lt.rec + goal alias, got {deps:?}"
    );
}

#[test]
fn test_not_lt_zero_goal_is_semireducible() {
    let spec = build_spec_with_stack();
    let def = spec
        .definitions()
        .get("not_lt_zero_goal")
        .expect("not_lt_zero_goal should be registered");
    assert!(
        !def.is_axiom,
        "not_lt_zero_goal should be a derived definition"
    );
    assert_eq!(
        def.proof_status,
        ProofStatus::DerivedProved,
        "not_lt_zero_goal should be fully constructive"
    );
}

#[test]
fn test_is_closed_at_bvar_inv_is_constructive() {
    let spec = build_spec_with_stack();
    let def = spec
        .definitions()
        .get("is_closed_at_bvar_inv")
        .expect("is_closed_at_bvar_inv should be registered");
    assert!(
        !def.is_axiom,
        "is_closed_at_bvar_inv should now be a constructive inversion lemma"
    );
    assert_eq!(
        def.proof_status,
        ProofStatus::DerivedProved,
        "is_closed_at_bvar_inv should be fully constructive"
    );
    assert!(
        def.axiom_deps.is_empty(),
        "is_closed_at_bvar_inv should have no axiom deps: {:?}",
        def.axiom_deps
    );
    assert!(
        def.value_src.is_some(),
        "is_closed_at_bvar_inv should carry a proof term"
    );
    let deps = def
        .dependencies
        .as_ref()
        .expect("is_closed_at_bvar_inv should record dependencies");
    assert!(
        deps.contains("is_closed_at.rec") && deps.contains("KExpr.rec"),
        "is_closed_at_bvar_inv should use is_closed_at.rec + KExpr.rec discrimination, got {deps:?}"
    );
}

#[test]
fn test_bvar_not_closed_is_fully_constructive() {
    let spec = build_spec_with_stack();
    let def = spec
        .definitions()
        .get("bvar_not_closed")
        .expect("bvar_not_closed should be registered");
    assert!(!def.is_axiom, "bvar_not_closed should be a definition");
    assert_eq!(
        def.proof_status,
        ProofStatus::DerivedProved,
        "bvar_not_closed should be fully constructive"
    );
    let deps = def
        .dependencies
        .as_ref()
        .expect("bvar_not_closed should record dependencies");
    assert!(
        deps.contains("not_lt_zero") && deps.contains("is_closed_at_bvar_inv"),
        "bvar_not_closed should compose not_lt_zero with is_closed_at_bvar_inv, got {deps:?}"
    );
    assert!(
        def.axiom_deps.is_empty(),
        "bvar_not_closed should have no axiom deps: {:?}",
        def.axiom_deps
    );
}

#[test]
fn test_kernel_infer_sort_sound_is_constructive_from_exact_result() {
    let spec = build_spec_with_stack();

    // kernel_infer_sort_result is no longer a HelperAxiom: it is DERIVED from
    // the faithful KernelInferAccepts inductive via kernel_infer_inversion
    // (Step 3), with the KExprEqT universe adapter converted back to the
    // byte-identical Prop equation.
    let result = spec
        .definitions()
        .get("kernel_infer_sort_result")
        .expect("kernel_infer_sort_result should be registered");
    assert!(
        !result.is_axiom,
        "kernel_infer_sort_result should now be derived, not a HelperAxiom"
    );
    assert_eq!(
        result.proof_status,
        ProofStatus::DerivedProved,
        "kernel_infer_sort_result should be DerivedProved (kernel-checked derivation)"
    );
    assert!(
        result
            .value_src
            .as_ref()
            .expect("kernel_infer_sort_result should carry a derivation proof term")
            .contains("kernel_infer_inversion"),
        "kernel_infer_sort_result should be derived via kernel_infer_inversion"
    );

    let sound = spec
        .definitions()
        .get("kernel_infer_sort_sound")
        .expect("kernel_infer_sort_sound should be registered");
    assert!(
        !sound.is_axiom,
        "kernel_infer_sort_sound should be a derived definition"
    );
    assert_eq!(
        sound.proof_status,
        ProofStatus::DerivedPending,
        "kernel_infer_sort_sound should be pending on kernel_infer_sort_result"
    );
    let deps = sound
        .dependencies
        .as_ref()
        .expect("kernel_infer_sort_sound should record dependencies");
    assert!(
        deps.contains("kernel_infer_sort_result") && deps.contains("Typing.sort"),
        "kernel_infer_sort_sound should use exact result + Typing.sort, got {deps:?}"
    );
}

// App-case local bridge tests are now in:
//   implementation_soundness_infer_refinement_app_tests.rs
// Lam/pi sound theorem tests are now in:
//   implementation_soundness_infer_refinement_binder_typing_tests.rs
// Dispatcher tests (kernel_infer_returns_well_typed) are now in:
//   implementation_soundness_infer_refinement_dispatch_tests.rs
