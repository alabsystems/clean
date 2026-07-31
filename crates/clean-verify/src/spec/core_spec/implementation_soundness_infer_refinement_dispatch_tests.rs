// Copyright 2026 Andrew Yates.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use crate::spec::types::ProofStatus;
use crate::test_utils::build_spec_with_stack;

#[test]
fn test_dispatcher_exists_and_is_derived() {
    let spec = build_spec_with_stack();
    let def = spec
        .definitions()
        .get("kernel_infer_returns_well_typed")
        .expect("kernel_infer_returns_well_typed should be registered");
    assert!(
        !def.is_axiom,
        "kernel_infer_returns_well_typed should be a derived lemma, not a HelperAxiom"
    );
    assert_eq!(
        def.proof_status,
        ProofStatus::DerivedPending,
        "kernel_infer_returns_well_typed should be pending (per-case axioms pending)"
    );
    assert!(
        def.value_src.is_some(),
        "kernel_infer_returns_well_typed should have a constructive proof term"
    );
}

#[test]
fn test_dispatcher_depends_on_motive_and_case_wrappers() {
    let spec = build_spec_with_stack();
    let def = spec
        .definitions()
        .get("kernel_infer_returns_well_typed")
        .expect("kernel_infer_returns_well_typed should be registered");

    let deps = def
        .dependencies
        .as_ref()
        .expect("kernel_infer_returns_well_typed should record dependencies");

    assert!(
        deps.contains("KExpr.rec"),
        "proof should use KExpr.rec for structural recursion: {deps:?}"
    );

    assert!(
        deps.contains("InferSoundAt"),
        "proof should use InferSoundAt as the named motive: {deps:?}"
    );

    for expected in [
        "infer_sound_at_sort",
        "infer_sound_at_bvar",
        "infer_sound_at_app",
        "infer_sound_at_lam",
        "infer_sound_at_pi",
        "infer_sound_at_const",
    ] {
        assert!(
            deps.contains(expected),
            "proof should dispatch to {expected}: {deps:?}"
        );
    }
}

#[test]
fn test_dispatch_wrappers_reference_per_case_sound_theorems() {
    let spec = build_spec_with_stack();

    // Each wrapper should delegate to the corresponding per-case sound theorem
    let wrapper_to_delegate = [
        ("infer_sound_at_sort", "kernel_infer_sort_sound"),
        ("infer_sound_at_bvar", "bvar_not_closed"),
        ("infer_sound_at_app", "kernel_infer_app_sound"),
        ("infer_sound_at_lam", "kernel_infer_lam_sound"),
        ("infer_sound_at_pi", "kernel_infer_pi_sound"),
        ("infer_sound_at_const", "kernel_infer_const_sound"),
    ];

    for (wrapper, delegate) in wrapper_to_delegate {
        let def = spec
            .definitions()
            .get(wrapper)
            .unwrap_or_else(|| panic!("{wrapper} should be registered"));
        let deps = def
            .dependencies
            .as_ref()
            .unwrap_or_else(|| panic!("{wrapper} should record dependencies"));
        assert!(
            deps.contains(delegate),
            "{wrapper} should depend on {delegate}: {deps:?}"
        );
        assert!(
            deps.contains("InferSoundAt"),
            "{wrapper} should depend on InferSoundAt: {deps:?}"
        );
    }
}

#[test]
fn test_dispatch_wrappers_have_value_src() {
    let spec = build_spec_with_stack();

    for name in [
        "infer_sound_at_sort",
        "infer_sound_at_bvar",
        "infer_sound_at_app",
        "infer_sound_at_lam",
        "infer_sound_at_pi",
        "infer_sound_at_const",
    ] {
        let def = spec
            .definitions()
            .get(name)
            .unwrap_or_else(|| panic!("{name} should be registered"));
        assert!(
            def.value_src.is_some(),
            "{name} should have a constructive proof term"
        );
        assert!(!def.is_axiom, "{name} should be derived, not an axiom");
    }
}

#[test]
fn test_bvar_wrapper_is_fully_constructive() {
    let spec = build_spec_with_stack();
    let def = spec
        .definitions()
        .get("infer_sound_at_bvar")
        .expect("infer_sound_at_bvar should be registered");
    assert_eq!(
        def.proof_status,
        ProofStatus::DerivedProved,
        "infer_sound_at_bvar should now be fully constructive"
    );
    assert!(
        def.axiom_deps.is_empty(),
        "infer_sound_at_bvar should have no axiom deps: {:?}",
        def.axiom_deps
    );
}

#[test]
fn test_infer_sound_at_motive_exists() {
    let spec = build_spec_with_stack();
    let def = spec
        .definitions()
        .get("InferSoundAt")
        .expect("InferSoundAt should be registered");
    assert!(
        def.value_src.is_some(),
        "InferSoundAt should have a definition (reducible)"
    );
    assert_eq!(
        def.proof_status,
        ProofStatus::DerivedProved,
        "InferSoundAt should be DerivedProved (it is a pure definition, not a theorem)"
    );
}

#[test]
fn test_app_wrapper_uses_admissibility_inversions() {
    let spec = build_spec_with_stack();
    let def = spec
        .definitions()
        .get("infer_sound_at_app")
        .expect("infer_sound_at_app should be registered");
    let deps = def
        .dependencies
        .as_ref()
        .expect("infer_sound_at_app should record dependencies");

    // App case needs admissibility inversions to supply IH admissibility
    assert!(
        deps.contains("kernel_input_admissible_app_fun"),
        "app wrapper should use fun admissibility inversion: {deps:?}"
    );
    assert!(
        deps.contains("kernel_input_admissible_app_arg"),
        "app wrapper should use arg admissibility inversion: {deps:?}"
    );
}

#[test]
fn test_dispatcher_value_src_uses_kexpr_rec_and_named_motive() {
    let spec = build_spec_with_stack();
    let def = spec
        .definitions()
        .get("kernel_infer_returns_well_typed")
        .expect("kernel_infer_returns_well_typed should be registered");
    let value_src = def
        .value_src
        .as_ref()
        .expect("kernel_infer_returns_well_typed should have a proof term");

    for snippet in [
        "KExpr.rec InferSoundAt",
        "infer_sound_at_sort",
        "infer_sound_at_bvar",
        "infer_sound_at_app",
        "infer_sound_at_lam",
        "infer_sound_at_pi",
        "infer_sound_at_const",
    ] {
        assert!(
            value_src.contains(snippet),
            "dispatcher proof term should mention {snippet}: {value_src}"
        );
    }
}

#[test]
fn test_dispatcher_axiom_deps_core_and_app() {
    let spec = build_spec_with_stack();
    let def = spec
        .definitions()
        .get("kernel_infer_returns_well_typed")
        .expect("kernel_infer_returns_well_typed should be registered");

    // Core deps. KernelEnvValid was retired to a DerivedProved DerivedLemma
    // (:= EnvSound) and KernelLocalCtxWellFormed was retired to a faithful
    // nil/cons inductive, so neither is an axiom leaf here. In Step 3 the six
    // per-case infer axioms were retired too (derived from the faithful
    // KernelInferAccepts inductive via kernel_infer_inversion) — the residual
    // is the skolem-witness closure.
    for retired in [
        "kernel_infer_sort_result",
        "kernel_infer_const_sound",
        "KernelInferAccepts",
    ] {
        assert!(
            !def.axiom_deps.contains(retired),
            "{retired} was retired to a derivation from the faithful inductive \
             and must no longer be an axiom leaf: {:?}",
            def.axiom_deps
        );
    }
    // After the KernelInferResult un-Skolemization the dispatcher's residual
    // infer-band skolem closure is EMPTY (the inferred subtypes are bound
    // existentially inside AppInferDecomp / App/Lam/PiInferWitness).
    assert!(
        !def.axiom_deps.contains("KernelInferResult"),
        "kernel_infer_returns_well_typed must no longer name the retired KernelInferResult: {:?}",
        def.axiom_deps
    );
    assert!(
        !def.axiom_deps.contains("KernelEnvValid"),
        "KernelEnvValid was retired to a DerivedProved lemma and must no longer be \
         an axiom leaf of kernel_infer_returns_well_typed: {:?}",
        def.axiom_deps
    );
    assert!(
        !def.axiom_deps.contains("KernelLocalCtxWellFormed"),
        "KernelLocalCtxWellFormed was retired to a faithful nil/cons inductive and \
         must no longer be an axiom leaf of kernel_infer_returns_well_typed: {:?}",
        def.axiom_deps
    );
    assert!(
        !def.axiom_deps.contains("is_closed_at_bvar_inv"),
        "dispatcher should no longer depend on is_closed_at_bvar_inv: {:?}",
        def.axiom_deps
    );

    // App-case deps: the pi domain/codomain Skolems are RETIRED (bound inside
    // AppInferWitness), so they must NOT appear.
    for retired in ["KernelInferAppPiDomain", "KernelInferAppPiCodomain"] {
        assert!(
            !def.axiom_deps.contains(retired),
            "retired app-case Skolem {retired} should not appear in axiom_deps: {:?}",
            def.axiom_deps
        );
    }

    // The step projections (retired or fun-only) and their former parent
    // decomposition + admissibility lemmas are all derived — none may appear.
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
            "{name} is derived and should not appear in axiom_deps: {:?}",
            def.axiom_deps
        );
    }
}

#[test]
fn test_dispatcher_axiom_deps_binder_cases() {
    let spec = build_spec_with_stack();
    let def = spec
        .definitions()
        .get("kernel_infer_returns_well_typed")
        .expect("kernel_infer_returns_well_typed should be registered");

    // Binder-case residual: after the KernelInferResult un-Skolemization NO
    // infer-band skolem survives; the body-type / domain-level Skolems, the two
    // vestigial guards, and the final KernelInferResult determinism anchor are all
    // RETIRED (bound inside AppInferDecomp / Lam/PiInferWitness or dropped outright).
    assert!(
        !def.axiom_deps.contains("KernelInferResult"),
        "axiom_deps must no longer name the retired KernelInferResult: {:?}",
        def.axiom_deps
    );
    for retired in [
        "KernelLamBodyType",
        "KernelLamDomainLevel",
        "KernelLamBodyAdmissible",
        "KernelPiDomainLevel",
        "KernelPiCodomainLevel",
        "KernelPiBodyAdmissible",
    ] {
        assert!(
            !def.axiom_deps.contains(retired),
            "retired binder-case Skolem {retired} should not appear in axiom_deps: {:?}",
            def.axiom_deps
        );
    }

    // Derived binder projections/theorems AND the retired decomposition
    // parents (Step 3) should NOT appear in axiom_deps: the trust surface
    // points at the skolem witnesses instead. (kernel_infer_lam/pi_body_step
    // are now retired entirely, census 18->16.)
    for name in [
        "kernel_infer_lam_result_step",
        "kernel_infer_lam_domain_sort",
        "kernel_infer_lam_body_typing",
        "kernel_infer_pi_domain_sort",
        "kernel_infer_pi_codomain_sort",
        "kernel_infer_pi_imax_result_step",
        "kernel_infer_lam_sound",
        "kernel_infer_pi_sound",
        "kernel_infer_lam_decomposition",
        "kernel_infer_pi_decomposition",
    ] {
        assert!(
            !def.axiom_deps.contains(name),
            "{name} is derived and should not appear in axiom_deps: {:?}",
            def.axiom_deps
        );
    }

    // not_lt_zero is constructive — should NOT be in axiom_deps
    assert!(
        !def.axiom_deps.contains("not_lt_zero"),
        "not_lt_zero is constructive and should not appear in axiom_deps: {:?}",
        def.axiom_deps
    );
}
