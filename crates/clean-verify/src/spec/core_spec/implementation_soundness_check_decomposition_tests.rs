// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>

use crate::spec::types::ProofStatus;
use crate::test_utils::{build_implementation_soundness_spec_with_stack, build_spec_with_stack};

/// After the KernelInferResult un-Skolemization, the check band's Skolem-naming
/// decomposition/step/admissibility lemmas are RETIRED: their types named the
/// inferred type as the Skolem KernelInferResult st e, which no longer exists
/// (KernelCheckAccepts.mk binds the inferred type R existentially, shared by
/// binding between the infer and defeq halves). The two halves are recovered
/// together by eliminating KernelCheckAccepts.rec (binding R once) inside
/// kernel_check_returns_well_typed_from_infer and tc_check_completeness.
#[test]
fn test_check_type_decomposition_lemmas_are_retired() {
    let spec = build_implementation_soundness_spec_with_stack();

    for retired in [
        "kernel_check_decomposition",
        "kernel_check_infer_step",
        "kernel_check_defeq_step",
        "kernel_check_types_admissible",
    ] {
        assert!(
            spec.definitions().get(retired).is_none(),
            "{retired} should be RETIRED by the KernelInferResult un-Skolemization"
        );
    }

    // KernelInferResult is now DELETED (census 13->12) — the determinism skolem
    // was retired by the existential reframe (Rf/Ra bound on the app ctor +
    // AppInferWitness, one shared R on KernelCheckAccepts.mk).
    assert!(
        spec.definitions().get("KernelInferResult").is_none(),
        "KernelInferResult should be DELETED (census 13->12 existential reframe)"
    );
}

/// The local check bridge now eliminates KernelCheckAccepts.rec directly (binding
/// the inferred type R), then joins the infer and defeq halves through
/// raw_type_conversion + kernel_def_eq_reflects_spec — no Skolem-naming
/// decomposition lemmas.
#[test]
fn test_kernel_check_local_bridge_is_derived_pending() {
    let spec = build_implementation_soundness_spec_with_stack();

    let local = spec
        .definitions()
        .get("kernel_check_returns_well_typed_from_infer")
        .expect("kernel_check_returns_well_typed_from_infer should exist");
    assert!(
        !local.is_axiom,
        "kernel_check_returns_well_typed_from_infer should be a derived lemma"
    );
    assert_eq!(
        local.proof_status,
        ProofStatus::DerivedPending,
        "kernel_check_returns_well_typed_from_infer should remain pending on implementation contracts"
    );
    let value = local
        .value_src
        .as_ref()
        .expect("kernel_check_returns_well_typed_from_infer should carry a proof term");
    assert!(
        value.contains("KernelCheckAccepts.rec"),
        "the local bridge should eliminate KernelCheckAccepts.rec directly: {value}"
    );
    let local_deps = local
        .dependencies
        .as_ref()
        .expect("kernel_check_returns_well_typed_from_infer should record dependencies");
    for expected_dep in [
        "raw_type_conversion",
        "kernel_def_eq_reflects_spec",
        "KernelCheckAccepts.rec",
    ] {
        assert!(
            local_deps.contains(expected_dep),
            "local bridge should depend on {expected_dep}, got {local_deps:?}"
        );
    }
    for retired in [
        "kernel_check_infer_step",
        "kernel_check_defeq_step",
        "kernel_check_types_admissible",
    ] {
        assert!(
            !local_deps.contains(retired),
            "local bridge should no longer depend on the retired {retired}: {local_deps:?}"
        );
    }
    assert!(
        !local_deps.contains("kernel_infer_returns_well_typed"),
        "local bridge should not depend on the global infer theorem: {local_deps:?}"
    );
}

#[test]
fn test_kernel_check_returns_well_typed_is_now_derived() {
    let spec = build_implementation_soundness_spec_with_stack();

    let def = spec
        .definitions()
        .get("kernel_check_returns_well_typed")
        .expect("kernel_check_returns_well_typed should exist");

    // Previously a HelperAxiom, now a DerivedLemma with constructive proof.
    assert!(
        !def.is_axiom,
        "kernel_check_returns_well_typed should now be a derived lemma, not an axiom"
    );
    assert_eq!(
        def.proof_status,
        ProofStatus::DerivedPending,
        "kernel_check_returns_well_typed should be DerivedPending (depends on pending axioms)"
    );
    assert!(
        def.value_src.is_some(),
        "kernel_check_returns_well_typed should have a proof term"
    );

    let deps = def
        .dependencies
        .as_ref()
        .expect("kernel_check_returns_well_typed should record dependencies");

    // Proof factors through the local bridge plus the global infer theorem.
    for expected_dep in [
        "kernel_check_returns_well_typed_from_infer",
        "kernel_infer_returns_well_typed",
    ] {
        assert!(
            deps.contains(expected_dep),
            "should depend on {expected_dep}, got {deps:?}"
        );
    }

    // After the un-Skolemization the only surfaced residual leaf is the named
    // DerivedPending infer dispatcher; KernelInferResult is gone.
    assert!(
        def.axiom_deps.contains("kernel_infer_returns_well_typed"),
        "axiom_deps should surface kernel_infer_returns_well_typed: {:?}",
        def.axiom_deps
    );
    assert!(
        !def.axiom_deps.contains("KernelInferResult"),
        "axiom_deps must no longer name the retired KernelInferResult: {:?}",
        def.axiom_deps
    );

    // Retired/derived check-band lemmas should NOT appear in axiom_deps.
    for retired in [
        "kernel_check_infer_step",
        "kernel_check_defeq_step",
        "kernel_check_decomposition",
        "kernel_check_types_admissible",
    ] {
        assert!(
            !def.axiom_deps.contains(retired),
            "{retired} is retired and should not appear in axiom_deps: {:?}",
            def.axiom_deps
        );
    }
}

#[test]
fn test_check_sound_summary_transitive_axiom_deps() {
    // Uses the full spec because KernelCheckSound_summary is a simulation wrapper
    // defined in add_implementation_soundness_simulation(), not the subset spec.
    let spec = build_spec_with_stack();

    let summary = spec
        .definitions()
        .get("KernelCheckSound_summary")
        .expect("KernelCheckSound_summary should exist");
    assert!(
        summary
            .axiom_deps
            .contains("kernel_infer_returns_well_typed"),
        "KernelCheckSound_summary axiom_deps should surface kernel_infer_returns_well_typed: {:?}",
        summary.axiom_deps
    );
    assert!(
        !summary.axiom_deps.contains("KernelInferResult"),
        "KernelCheckSound_summary must no longer name the retired KernelInferResult: {:?}",
        summary.axiom_deps
    );
    assert!(
        !summary.axiom_deps.contains("KernelEnvValid"),
        "KernelEnvValid was retired to a DerivedProved lemma and must no longer be \
         an axiom leaf of KernelCheckSound_summary: {:?}",
        summary.axiom_deps
    );
    // DerivedLemmas / retired lemmas should NOT appear in axiom_deps.
    for derived in [
        "kernel_check_returns_well_typed",
        "kernel_def_eq_reflects_spec",
        "kernel_check_infer_step",
        "kernel_check_defeq_step",
        "kernel_check_decomposition",
        "kernel_check_types_admissible",
    ] {
        assert!(
            !summary.axiom_deps.contains(derived),
            "KernelCheckSound_summary should not list {derived} in axiom_deps: {:?}",
            summary.axiom_deps
        );
    }
}
