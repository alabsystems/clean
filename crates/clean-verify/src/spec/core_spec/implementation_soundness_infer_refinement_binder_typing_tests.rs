// Copyright 2026 Andrew Yates.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use crate::spec::types::ProofStatus;
use crate::test_utils::build_spec_with_stack;

#[test]
fn test_binder_typing_step_axioms_retired() {
    let spec = build_spec_with_stack();
    // The five skolem-named lam/pi typing-step projections are RETIRED — their
    // types named the retired body-type / level Skolems, now bound inside the
    // Lam/PiInferWitness existentials. The typing evidence is recovered directly
    // inside the *_sound bridges' witness eliminations.
    for retired in [
        "kernel_infer_lam_domain_sort",
        "kernel_infer_lam_body_typing",
        "kernel_infer_lam_result_step",
        "kernel_infer_pi_domain_sort",
        "kernel_infer_pi_codomain_sort",
        "kernel_infer_pi_imax_result_step",
    ] {
        assert!(
            !spec.definitions().contains_key(retired),
            "binder-typing step projection {retired} should be retired"
        );
    }
}

#[test]
fn test_lam_sound_is_derived_pending_eliminating_witness() {
    let spec = build_spec_with_stack();
    let lam = spec
        .definitions()
        .get("kernel_infer_lam_sound")
        .expect("kernel_infer_lam_sound should be registered");

    assert!(
        !lam.is_axiom,
        "kernel_infer_lam_sound should be a DerivedLemma, not a HelperAxiom"
    );
    assert_eq!(
        lam.proof_status,
        ProofStatus::DerivedPending,
        "kernel_infer_lam_sound should be DerivedPending"
    );
    assert!(
        lam.value_src
            .as_ref()
            .is_some_and(|v| v.contains("LamInferWitness.rec")),
        "kernel_infer_lam_sound should eliminate LamInferWitness via its recursor"
    );
    assert!(
        lam.description.contains("#2870"),
        "lam_sound should reference #2870 in its universe-alignment description: {}",
        lam.description
    );

    let deps = lam
        .dependencies
        .as_ref()
        .expect("kernel_infer_lam_sound should record dependencies");
    for expected in [
        "Typing.lam",
        "raw_type_conversion",
        "LamInferWitness.rec",
        "kernel_infer_lam_decomposition",
    ] {
        assert!(
            deps.contains(expected),
            "kernel_infer_lam_sound should depend on {expected}: {deps:?}"
        );
    }

    // The residual expands through the master inversion to the single surviving
    // skolem KernelInferResult; the retired body-type / level / vestigial-guard
    // Skolems and the derived decomposition must NOT appear.
    assert!(
        !lam.axiom_deps.contains("kernel_infer_lam_decomposition"),
        "axiom_deps should expand past the derived decomposition: {:?}",
        lam.axiom_deps
    );
    assert!(
        !lam.axiom_deps.contains("KernelInferResult"),
        "axiom_deps must no longer name the retired KernelInferResult (un-Skolemization): {:?}",
        lam.axiom_deps
    );
    for retired in [
        "KernelLamBodyType",
        "KernelLamDomainLevel",
        "KernelLamBodyAdmissible",
    ] {
        assert!(
            !lam.axiom_deps.contains(retired),
            "retired Skolem {retired} should not appear in axiom_deps: {:?}",
            lam.axiom_deps
        );
    }
}

#[test]
fn test_pi_sound_is_derived_pending_eliminating_witness() {
    let spec = build_spec_with_stack();
    let pi = spec
        .definitions()
        .get("kernel_infer_pi_sound")
        .expect("kernel_infer_pi_sound should be registered");

    assert!(
        !pi.is_axiom,
        "kernel_infer_pi_sound should be a DerivedLemma, not a HelperAxiom"
    );
    assert_eq!(
        pi.proof_status,
        ProofStatus::DerivedPending,
        "kernel_infer_pi_sound should be DerivedPending"
    );
    assert!(
        pi.value_src
            .as_ref()
            .is_some_and(|v| v.contains("PiInferWitness.rec")),
        "kernel_infer_pi_sound should eliminate PiInferWitness via its recursor"
    );
    assert!(
        pi.description.contains("#2870"),
        "pi_sound should reference #2870 in its universe-alignment description: {}",
        pi.description
    );

    let deps = pi
        .dependencies
        .as_ref()
        .expect("kernel_infer_pi_sound should record dependencies");
    for expected in [
        "Typing.pi",
        "raw_type_conversion",
        "PiInferWitness.rec",
        "imax_nat",
        "kernel_infer_pi_decomposition",
    ] {
        assert!(
            deps.contains(expected),
            "kernel_infer_pi_sound should depend on {expected}: {deps:?}"
        );
    }

    assert!(
        !pi.axiom_deps.contains("kernel_infer_pi_decomposition"),
        "axiom_deps should expand past the derived decomposition: {:?}",
        pi.axiom_deps
    );
    assert!(
        !pi.axiom_deps.contains("KernelInferResult"),
        "axiom_deps must no longer name the retired KernelInferResult (un-Skolemization): {:?}",
        pi.axiom_deps
    );
    for retired in [
        "KernelPiDomainLevel",
        "KernelPiCodomainLevel",
        "KernelPiBodyAdmissible",
    ] {
        assert!(
            !pi.axiom_deps.contains(retired),
            "retired Skolem {retired} should not appear in axiom_deps: {:?}",
            pi.axiom_deps
        );
    }
}
