// Copyright 2026 Andrew Yates.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use crate::test_utils::build_spec_with_stack;

#[test]
fn test_kernel_infer_sound_axiom_deps_expand_dispatch_leaves() {
    let spec = build_spec_with_stack();
    let def = spec
        .definitions()
        .get("KernelInferSound")
        .expect("KernelInferSound should be registered");

    // Step 3 retired the per-case infer axioms (derived from the faithful
    // KernelInferAccepts inductive via kernel_infer_inversion); Step 4 retired
    // the check band (KernelCheckAccepts is a faithful inductive). The
    // KernelInferResult un-Skolemization retired the LAST infer-band skolem, so
    // KernelInferSound's residual axiom closure is now EMPTY.
    assert!(
        def.axiom_deps.is_empty(),
        "KernelInferSound residual axiom closure should be EMPTY after the \
         KernelInferResult un-Skolemization: {:?}",
        def.axiom_deps
    );

    for derived in [
        "KernelInferResult",
        "kernel_infer_app_sound",
        "kernel_infer_lam_sound",
        "kernel_infer_pi_sound",
        "kernel_infer_sort_result",
        "kernel_infer_const_sound",
        "kernel_infer_app_decomposition",
        "kernel_infer_app_fun_type_admissible",
        "kernel_infer_lam_decomposition",
        "kernel_infer_pi_decomposition",
        "KernelInferAccepts",
        "KernelCheckAccepts",
        "kernel_check_decomposition",
        "kernel_check_types_admissible",
    ] {
        assert!(
            !def.axiom_deps.contains(derived),
            "KernelInferSound should not list derived {derived}: {:?}",
            def.axiom_deps
        );
    }
}

#[test]
fn test_kernel_infer_sound_summary_exposes_leaf_and_state_deps() {
    let spec = build_spec_with_stack();
    let def = spec
        .definitions()
        .get("KernelInferSound_summary")
        .expect("KernelInferSound_summary should be registered");

    // KernelEnvValid was retired to a DerivedProved DerivedLemma (:= EnvSound) and
    // KernelLocalCtxWellFormed was retired to a faithful nil/cons inductive, so
    // neither appears as an axiom leaf in the summary's transitive closure.
    // reason: this expected-axiom-deps set mirrors the sibling `for derived in [..]`
    // membership loops and is a documented shrink/growth point (two entries were
    // retired per the comment above); keeping the loop form preserves that idiom and
    // avoids churn when more expected deps are re-added. See JUSTIFIED_EXCEPTIONS §10.
    #[allow(clippy::single_element_loop)]
    for expected in ["kernel_infer_returns_well_typed"] {
        assert!(
            def.axiom_deps.contains(expected),
            "KernelInferSound_summary axiom_deps should include {expected}: {:?}",
            def.axiom_deps
        );
    }
    assert!(
        !def.axiom_deps.contains("KernelInferResult"),
        "KernelInferSound_summary must no longer name the retired KernelInferResult: {:?}",
        def.axiom_deps
    );
    assert!(
        !def.axiom_deps.contains("KernelEnvValid"),
        "KernelEnvValid was retired to a DerivedProved lemma and must no longer be \
         an axiom leaf of KernelInferSound_summary: {:?}",
        def.axiom_deps
    );
    assert!(
        !def.axiom_deps.contains("KernelLocalCtxWellFormed"),
        "KernelLocalCtxWellFormed was retired to a faithful nil/cons inductive and \
         must no longer be an axiom leaf of KernelInferSound_summary: {:?}",
        def.axiom_deps
    );

    for derived in [
        "kernel_infer_app_sound",
        "kernel_infer_lam_sound",
        "kernel_infer_pi_sound",
        "kernel_infer_lam_domain_sort",
        "kernel_infer_lam_body_typing",
        "kernel_infer_lam_result_step",
        "kernel_infer_pi_domain_sort",
        "kernel_infer_pi_codomain_sort",
        "kernel_infer_pi_imax_result_step",
        "kernel_infer_sort_result",
        "kernel_infer_const_sound",
        "kernel_infer_app_decomposition",
        "kernel_infer_app_fun_type_admissible",
        "kernel_infer_lam_decomposition",
        "kernel_infer_pi_decomposition",
        "KernelInferAccepts",
        "KernelCheckAccepts",
        "kernel_check_decomposition",
        "kernel_check_types_admissible",
    ] {
        assert!(
            !def.axiom_deps.contains(derived),
            "KernelInferSound_summary should not list derived {derived}: {:?}",
            def.axiom_deps
        );
    }
}
