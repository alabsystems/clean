// Copyright 2026 Andrew Yates.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use crate::spec::types::ProofStatus;
use crate::test_utils::build_spec_with_stack;

#[test]
fn test_kernel_infer_app_sound_is_now_local_bridge() {
    let spec = build_spec_with_stack();
    let def = spec
        .definitions()
        .get("kernel_infer_app_sound")
        .expect("kernel_infer_app_sound should be registered");
    assert!(
        !def.is_axiom,
        "kernel_infer_app_sound should now be a derived local bridge"
    );
    assert_eq!(
        def.proof_status,
        ProofStatus::DerivedPending,
        "kernel_infer_app_sound should remain pending on narrower implementation leaves"
    );
    assert!(
        def.value_src.is_some(),
        "kernel_infer_app_sound should carry a proof term"
    );

    let deps = def
        .dependencies
        .as_ref()
        .expect("kernel_infer_app_sound should record dependencies");
    // The app-case bridge now eliminates the AppInferDecomp existential (inferred
    // subtypes Rf/Ra — KernelInferResult retired) then the AppInferWitness packaged
    // existential (pi domain/codomain), and builds the KernelCheckAccepts token
    // internally (KernelCheckAccepts.mk over the arg-infer acceptance at Ra).
    for expected in [
        "raw_type_conversion",
        "Typing.app",
        "kernel_whnf_returns_def_eq",
        "kernel_check_returns_well_typed_from_infer",
        "kernel_input_admissible_app_arg",
        "AppInferDecomp.rec",
        "AppInferWitness.rec",
        "KernelCheckAccepts.mk",
        "kernel_infer_app_decomposition",
    ] {
        assert!(
            deps.contains(expected),
            "kernel_infer_app_sound should depend on {expected}: {deps:?}"
        );
    }

    // After the KernelInferResult un-Skolemization the residual axiom closure is
    // EMPTY: the inferred subtypes are bound existentially inside AppInferDecomp /
    // AppInferWitness (kernel-generated inductives), and every sub-lemma is
    // skolem-free. KernelInferResult must NOT appear.
    assert!(
        !def.axiom_deps.contains("KernelInferResult"),
        "kernel_infer_app_sound axiom_deps must no longer name the retired KernelInferResult: {:?}",
        def.axiom_deps
    );
    for retired in ["KernelInferAppPiDomain", "KernelInferAppPiCodomain"] {
        assert!(
            !def.axiom_deps.contains(retired),
            "retired Skolem {retired} should not appear in axiom_deps: {:?}",
            def.axiom_deps
        );
    }

    // The retired step projections and the derived decomposition lemma must not
    // appear in axiom_deps.
    for name in [
        "kernel_infer_app_fun_step",
        "kernel_infer_app_pi_step",
        "kernel_infer_app_arg_check_step",
        "kernel_infer_app_result_step",
        "kernel_infer_app_decomposition",
        "kernel_infer_app_fun_type_admissible",
    ] {
        assert!(
            !def.axiom_deps.contains(name),
            "{name} is derived/retired and should not appear in axiom_deps: {:?}",
            def.axiom_deps
        );
    }
}
