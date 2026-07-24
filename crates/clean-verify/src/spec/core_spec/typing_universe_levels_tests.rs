// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Ratchet tests for the `imax_nat` universe helper.
//! Ensures the closed Nat-level shadow of production `Level::imax`
//! remains correctly registered, non-axiomatic, and consumed by the
//! post-landing lam/pi universe surface.
//! Reference: Lean 4 `Level.lean:17` defines `imax n m := if m = 0 then 0 else max n m`.
//! Part of #2870.

use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::test_utils::build_spec_with_stack;

// ── 1. Direct imax_nat registration ratchets ────────────────────────

#[test]
fn test_imax_nat_is_registered() {
    let spec = build_spec_with_stack();
    spec.definitions()
        .get("imax_nat")
        .expect("imax_nat should be registered in the specification");
}

#[test]
fn test_imax_nat_is_non_axiom_derived_proved() {
    let spec = build_spec_with_stack();
    let def = spec
        .definitions()
        .get("imax_nat")
        .expect("imax_nat should be registered");
    assert!(
        !def.is_axiom,
        "imax_nat should be a reducible definition, not an axiom"
    );
    assert_eq!(
        def.category,
        AxiomCategory::DerivedLemma,
        "imax_nat should be a DerivedLemma"
    );
    assert_eq!(
        def.proof_status,
        ProofStatus::DerivedProved,
        "imax_nat should be DerivedProved (fully constructive definition)"
    );
}

#[test]
fn test_imax_nat_has_constructive_value() {
    let spec = build_spec_with_stack();
    let def = spec
        .definitions()
        .get("imax_nat")
        .expect("imax_nat should be registered");
    assert!(
        def.value_src.is_some(),
        "imax_nat should have a constructive definition body"
    );
    let value = def.value_src.as_ref().unwrap();
    assert!(
        value.contains("Nat.rec"),
        "imax_nat should be defined via Nat.rec (case split on m): {value}"
    );
    assert!(
        value.contains("Nat.zero"),
        "imax_nat should return Nat.zero in the m=0 base case: {value}"
    );
}

#[test]
fn test_imax_nat_description_documents_prop_case() {
    let spec = build_spec_with_stack();
    let def = spec
        .definitions()
        .get("imax_nat")
        .expect("imax_nat should be registered");
    assert!(
        def.description.contains("imax_nat n 0 = 0"),
        "description should document the m=0 Prop case: {}",
        def.description
    );
    assert!(
        def.description.contains("#2870"),
        "description should reference the tracking issue: {}",
        def.description
    );
}

#[test]
fn test_imax_nat_type_signature() {
    let spec = build_spec_with_stack();
    let def = spec
        .definitions()
        .get("imax_nat")
        .expect("imax_nat should be registered");
    assert_eq!(
        def.type_src, "Nat -> Nat -> Nat",
        "imax_nat should map two Nat universe levels to a Nat result"
    );
}

#[test]
fn test_imax_nat_dependencies() {
    let spec = build_spec_with_stack();
    let def = spec
        .definitions()
        .get("imax_nat")
        .expect("imax_nat should be registered");
    let deps = def
        .dependencies
        .as_ref()
        .expect("imax_nat should record dependencies");
    for expected in ["Nat.rec", "Nat.add", "Nat.sub"] {
        assert!(
            deps.contains(expected),
            "imax_nat should depend on {expected}: {deps:?}"
        );
    }
}

#[test]
fn test_sort_universe_consistency_is_registered_and_constructive() {
    let spec = build_spec_with_stack();
    let def = spec
        .definitions()
        .get("sort_universe_consistency")
        .expect("sort_universe_consistency should be registered");

    assert!(
        !def.is_axiom,
        "sort_universe_consistency should be a constructive definition"
    );
    assert_eq!(
        def.category,
        AxiomCategory::DerivedLemma,
        "sort_universe_consistency should be a DerivedLemma"
    );
    assert_eq!(
        def.proof_status,
        ProofStatus::DerivedProved,
        "sort_universe_consistency should be DerivedProved"
    );
    assert!(
        def.axiom_deps.is_empty(),
        "sort_universe_consistency should not depend on helper axioms: {:?}",
        def.axiom_deps
    );
}

#[test]
fn test_sort_universe_consistency_uses_sort_projection() {
    let spec = build_spec_with_stack();
    let def = spec
        .definitions()
        .get("sort_universe_consistency")
        .expect("sort_universe_consistency should be registered");
    let value = def
        .value_src
        .as_ref()
        .expect("sort_universe_consistency should have a proof term");

    assert!(
        value.contains("Eq.cong"),
        "sort_universe_consistency should use Eq.cong to project equality: {value}"
    );
    assert!(
        value.contains("KExpr.rec"),
        "sort_universe_consistency should project the sort level with KExpr.rec: {value}"
    );

    let deps = def
        .dependencies
        .as_ref()
        .expect("sort_universe_consistency should record dependencies");
    for expected in ["Eq.cong", "KExpr.rec"] {
        assert!(
            deps.contains(expected),
            "sort_universe_consistency should depend on {expected}: {deps:?}"
        );
    }
}

// ── 2. Downstream consumer ratchets ─────────────────────────────────

#[test]
fn test_pi_formation_consumes_imax_nat() {
    let spec = build_spec_with_stack();
    let def = spec
        .definitions()
        .get("pi_formation")
        .expect("pi_formation should be registered");
    assert!(
        def.type_src.contains("Level.imax n m"),
        "pi_formation result sort should use Level.imax n m: {}",
        def.type_src
    );
    let value = def
        .value_src
        .as_ref()
        .expect("pi_formation should have a proof term");
    assert!(
        value.contains("Typing.pi"),
        "pi_formation should delegate to Typing.pi constructor: {value}"
    );
}

#[test]
fn test_kernel_infer_pi_sound_consumes_imax_nat() {
    // The skolem-named kernel_infer_pi_imax_result_step was RETIRED — the imax
    // result conversion now lives INSIDE kernel_infer_pi_sound's PiInferWitness.rec
    // elimination (the witness binds dom/cod and carries the
    // is_def_eq (Sort (imax_nat dom cod)) T field). Pin that the imax logic is
    // still present in the pi sound bridge.
    let spec = build_spec_with_stack();
    let def = spec
        .definitions()
        .get("kernel_infer_pi_sound")
        .expect("kernel_infer_pi_sound should be registered");
    let value = def
        .value_src
        .as_ref()
        .expect("kernel_infer_pi_sound should carry a proof term");
    assert!(
        value.contains("Level.imax") && value.contains("Typing.pi"),
        "kernel_infer_pi_sound should build Sort(Level.imax dom cod) via Typing.pi: {value}"
    );
}

#[test]
fn test_kernel_infer_pi_sound_eliminates_pi_infer_witness() {
    let spec = build_spec_with_stack();
    let def = spec
        .definitions()
        .get("kernel_infer_pi_sound")
        .expect("kernel_infer_pi_sound should be registered");
    let deps = def
        .dependencies
        .as_ref()
        .expect("kernel_infer_pi_sound should record dependencies");
    assert!(
        deps.contains("PiInferWitness.rec") && deps.contains("kernel_infer_pi_decomposition"),
        "kernel_infer_pi_sound should eliminate PiInferWitness via its recursor over the \
         decomposition: {deps:?}"
    );
}
