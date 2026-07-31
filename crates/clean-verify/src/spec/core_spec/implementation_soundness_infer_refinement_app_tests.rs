// Copyright 2026 Andrew Yates.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use crate::spec::types::ProofStatus;
use crate::test_utils::build_spec_with_stack;

#[test]
fn test_app_case_remaining_helper_axioms() {
    let spec = build_spec_with_stack();
    // The app pi domain/codomain Skolems (KernelInferAppPiDomain /
    // KernelInferAppPiCodomain) are RETIRED — bound internally by the
    // AppInferWitness packaged-existential inductive. They must be GONE, and
    // AppInferWitness must be a kernel-checked inductive (not an axiom).
    for retired in ["KernelInferAppPiDomain", "KernelInferAppPiCodomain"] {
        assert!(
            spec.definitions().get(retired).is_none(),
            "{retired} should be retired (bound inside AppInferWitness)"
        );
    }
    for name in [
        "AppInferWitness",
        "AppInferWitness.mk",
        "AppInferWitness.rec",
    ] {
        let def = spec
            .definitions()
            .get(name)
            .unwrap_or_else(|| panic!("{name} should be registered"));
        assert!(
            !def.is_axiom,
            "{name} must be a kernel inductive, not an axiom"
        );
    }
    // kernel_infer_app_fun_type_admissible was RETIRED by the KernelInferResult
    // un-Skolemization (its type named the inferred function type as the Skolem
    // KernelInferResult st f); its guard evidence is recovered directly inside
    // kernel_infer_app_sound. Only kernel_infer_app_decomposition survives, now
    // concluding in the AppInferDecomp existential.
    assert!(
        spec.definitions()
            .get("kernel_infer_app_fun_type_admissible")
            .is_none(),
        "kernel_infer_app_fun_type_admissible should be retired (KernelInferResult un-Skolemization)"
    );
    let decomp = spec
        .definitions()
        .get("kernel_infer_app_decomposition")
        .expect("kernel_infer_app_decomposition should be registered");
    assert!(
        !decomp.is_axiom,
        "kernel_infer_app_decomposition should be derived from the faithful KernelInferAccepts inductive"
    );
    assert_eq!(
        decomp.proof_status,
        ProofStatus::DerivedProved,
        "kernel_infer_app_decomposition should be DerivedProved (kernel-checked derivation)"
    );
    assert!(
        decomp.type_src.contains("AppInferDecomp st f a T"),
        "kernel_infer_app_decomposition should conclude in the AppInferDecomp existential: {}",
        decomp.type_src
    );
}

#[test]
fn test_app_case_step_projections_are_retired() {
    let spec = build_spec_with_stack();
    // ALL app-case step projections are now RETIRED. The whnf/arg-check/result
    // step projections were retired when the pi domain/codomain Skolems moved
    // inside AppInferWitness; kernel_infer_app_fun_step was retired by the
    // KernelInferResult un-Skolemization (its type projected an infer acceptance
    // at the Skolem KernelInferResult st f, which no longer exists). Their
    // evidence is recovered directly inside kernel_infer_app_sound by eliminating
    // AppInferDecomp (bind Rf/Ra) then AppInferWitness (bind dom/cod).
    for retired in [
        "kernel_infer_app_fun_step",
        "kernel_infer_app_pi_step",
        "kernel_infer_app_arg_check_step",
        "kernel_infer_app_result_step",
    ] {
        assert!(
            spec.definitions().get(retired).is_none(),
            "{retired} should be retired"
        );
    }
}
