// Copyright 2026 Andrew Yates.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use crate::spec::types::{ProofStatus, TrustLevel};
use crate::test_utils::build_spec_with_stack;
use clean_kernel::{ConstantKind, Name, Reducibility};

fn assert_split_state_predicate_pending(spec: &crate::Specification, name: &str) {
    let def = spec
        .definitions()
        .get(name)
        .unwrap_or_else(|| panic!("missing split state predicate {name}"));
    assert!(!def.is_axiom, "{name} should be a definition");
    assert_eq!(
        def.proof_status,
        ProofStatus::DerivedPending,
        "{name} should stay pending because it still depends on implementation-side state invariants"
    );
    assert_eq!(
        def.trust_level(),
        TrustLevel::AxiomPending,
        "{name} should still surface as a pending implementation assumption"
    );
}

fn assert_alias_is_semireducible(spec: &crate::Specification, name: &str) {
    let info = spec
        .env()
        .get_const(&Name::from_string(name))
        .unwrap_or_else(|| panic!("{name} should be registered"));
    assert!(
        matches!(info.reducibility, Reducibility::Regular(_)),
        "{name} should be semireducible so wrapper proofs can unfold it during declaration checking, got {:?}",
        info.reducibility
    );
    assert!(
        !info.is_reducible,
        "{name} should not become fully reducible"
    );
    assert_eq!(
        info.kind,
        ConstantKind::Definition,
        "{name} should remain a regular definition alias"
    );
}

fn assert_constructive_input_admissibility(spec: &crate::Specification) {
    let unary = spec
        .definitions()
        .get("KernelInputAdmissible")
        .expect("KernelInputAdmissible should register");
    assert!(
        !unary.is_axiom,
        "KernelInputAdmissible should be a definition"
    );
    assert_eq!(
        unary.proof_status,
        ProofStatus::DerivedProved,
        "KernelInputAdmissible should reduce to the constructive is_closed predicate"
    );
    assert_eq!(
        unary.trust_level(),
        TrustLevel::Derived,
        "KernelInputAdmissible should no longer contribute a pending assumption"
    );

    let binary = spec
        .definitions()
        .get("KernelBinaryInputAdmissible")
        .expect("KernelBinaryInputAdmissible should register");
    assert!(
        !binary.is_axiom,
        "KernelBinaryInputAdmissible should be a definition"
    );
    assert_eq!(
        binary.proof_status,
        ProofStatus::DerivedProved,
        "KernelBinaryInputAdmissible should be derived from unary admissibility"
    );
    assert_eq!(
        binary.trust_level(),
        TrustLevel::Derived,
        "KernelBinaryInputAdmissible should no longer contribute a pending assumption"
    );
}

fn assert_summary_state_alias(spec: &crate::Specification) {
    let state = spec
        .definitions()
        .get("KernelStateMatchesSpec")
        .expect("KernelStateMatchesSpec should register");
    assert_alias_is_semireducible(spec, "KernelStateMatchesSpec");
    assert!(
        !state.is_axiom,
        "KernelStateMatchesSpec should be a definition-backed summary alias, not a fresh axiom"
    );
    assert_eq!(
        state.proof_status,
        ProofStatus::DerivedPending,
        "KernelStateMatchesSpec should remain pending because it depends on state invariants"
    );
    assert_eq!(
        state.trust_level(),
        TrustLevel::AxiomPending,
        "KernelStateMatchesSpec should still surface the remaining pending state assumptions"
    );

    let state_deps = state
        .dependencies
        .as_ref()
        .expect("KernelStateMatchesSpec should record its split-state dependencies");
    assert!(
        state_deps.contains("KernelStateEnvValid")
            && state_deps.contains("KernelStateLocalCtxWellFormed"),
        "KernelStateMatchesSpec should package the split state predicates, got {state_deps:?}"
    );

    let summary_builder = spec
        .definitions()
        .get("KernelStateMatchesSpec.mk")
        .expect("KernelStateMatchesSpec.mk should register");
    assert!(
        !summary_builder.is_axiom,
        "KernelStateMatchesSpec.mk should now be a derived definition"
    );
    assert_eq!(
        summary_builder.proof_status,
        ProofStatus::DerivedPending,
        "KernelStateMatchesSpec.mk should stay pending because its split-state predicates remain pending"
    );
    let builder_deps = summary_builder
        .dependencies
        .as_ref()
        .expect("KernelStateMatchesSpec.mk should record its split-state dependencies");
    assert!(
        builder_deps.contains("KernelStateEnvValid")
            && builder_deps.contains("KernelStateLocalCtxWellFormed"),
        "KernelStateMatchesSpec.mk should rebuild the summary alias from the split state predicates, got {builder_deps:?}"
    );
    assert!(
        builder_deps.contains("KernelStateMatchesSpec"),
        "KernelStateMatchesSpec.mk should reference KernelStateMatchesSpec (its return type), got {builder_deps:?}"
    );
    assert!(
        !builder_deps.contains("KernelEnvValid")
            && !builder_deps.contains("KernelLocalCtxWellFormed"),
        "KernelStateMatchesSpec.mk should not require callers to re-enter the raw env/ctx bridge, got {builder_deps:?}"
    );
}

#[test]
fn test_implementation_soundness_contracts_exist() {
    let spec = build_spec_with_stack();
    for name in [
        "KernelState",
        "KernelStateEnvValid",
        "KernelStateLocalCtxWellFormed",
        "KernelStateMatchesSpec",
        "KernelStateMatchesSpec.mk",
        "KernelStateMatchesSpec.envValid",
        "KernelStateMatchesSpec.ctxWellFormed",
        "KernelInputAdmissible",
        "KernelBinaryInputAdmissible",
        "KernelInferAccepts",
        "KernelCheckAccepts",
        "KernelWhnfAccepts",
        "KernelDefEqAccepts",
        // KernelInferResult DELETED (census 13->12) — the determinism skolem,
        // retired by the existential reframe (Rf/Ra on KernelInferAccepts.app +
        // AppInferWitness; one shared R on KernelCheckAccepts.mk).
        "beta_reduces_preserves_def_eq",
        "whnf_to_preserves_def_eq",
        "kernel_whnf_reduces_to_spec_whnf",
        // kernel_check_decomposition / kernel_check_infer_step /
        // kernel_check_defeq_step / kernel_check_types_admissible were RETIRED by
        // the KernelInferResult un-Skolemization (their types named the Skolem
        // KernelInferResult st e; the halves are now recovered together by
        // eliminating KernelCheckAccepts.rec).
        "kernel_check_returns_well_typed",
        "kernel_whnf_returns_def_eq",
        "DefEqJoinable",
        "def_eq_joinable_reflects",
        "kernel_def_eq_reflects_spec",
        "KernelInferSound",
        "KernelCheckSound",
        "KernelWhnfSound",
        "KernelDefEqSound",
        "KernelWhnfPreservesTyping",
        "KernelInferSound_summary",
        "KernelCheckSound_summary",
        "KernelWhnfSound_summary",
        "KernelDefEqSound_summary",
        "kernel_empty_env_valid",
        "kernel_empty_ctx_well_formed",
        "KernelInitialStateValid",
    ] {
        assert!(
            spec.definitions().contains_key(name),
            "expected implementation-soundness definition {name} to be registered"
        );
    }
}

#[test]
fn test_initial_state_validity_base_case() {
    let spec = build_spec_with_stack();

    // kernel_empty_env_valid is now PROVED (DefinitionalExtension.refl over the
    // KernelEnvValid := EnvSound := DefinitionalExtension KEnv.empty env unfolding):
    // a DerivedProved DerivedLemma with no remaining pending assumption.
    let empty_env = spec
        .definitions()
        .get("kernel_empty_env_valid")
        .expect("missing initial-state base case kernel_empty_env_valid");
    assert!(
        !empty_env.is_axiom,
        "kernel_empty_env_valid should now be a proved derived lemma, not an axiom"
    );
    assert_eq!(
        empty_env.category,
        crate::spec::types::AxiomCategory::DerivedLemma,
        "kernel_empty_env_valid should be a DerivedLemma after retirement"
    );
    assert_eq!(
        empty_env.proof_status,
        ProofStatus::DerivedProved,
        "kernel_empty_env_valid should be DerivedProved (DefinitionalExtension.refl)"
    );
    assert_eq!(
        empty_env.trust_level(),
        TrustLevel::Derived,
        "kernel_empty_env_valid should no longer contribute a pending assumption"
    );
    assert!(
        empty_env.axiom_deps.is_empty(),
        "kernel_empty_env_valid should carry zero axiom_deps (foundational closure): {:?}",
        empty_env.axiom_deps
    );

    // kernel_empty_ctx_well_formed is now PROVED (KernelLocalCtxWellFormed.nil over
    // the faithful inductive KernelLocalCtxWellFormed with env as a uniform
    // parameter): a DerivedProved DerivedLemma with no remaining pending assumption.
    let empty_ctx = spec
        .definitions()
        .get("kernel_empty_ctx_well_formed")
        .expect("missing initial-state base case kernel_empty_ctx_well_formed");
    assert!(
        !empty_ctx.is_axiom,
        "kernel_empty_ctx_well_formed should now be a proved derived lemma, not an axiom"
    );
    assert_eq!(
        empty_ctx.category,
        crate::spec::types::AxiomCategory::DerivedLemma,
        "kernel_empty_ctx_well_formed should be a DerivedLemma after retirement"
    );
    assert_eq!(
        empty_ctx.proof_status,
        ProofStatus::DerivedProved,
        "kernel_empty_ctx_well_formed should be DerivedProved (KernelLocalCtxWellFormed.nil)"
    );
    assert_eq!(
        empty_ctx.trust_level(),
        TrustLevel::Derived,
        "kernel_empty_ctx_well_formed should no longer contribute a pending assumption"
    );
    assert!(
        empty_ctx.axiom_deps.is_empty(),
        "kernel_empty_ctx_well_formed should carry zero axiom_deps (foundational closure): {:?}",
        empty_ctx.axiom_deps
    );

    // KernelInitialStateValid should be a derived theorem composing the two axioms.
    let init = spec
        .definitions()
        .get("KernelInitialStateValid")
        .expect("KernelInitialStateValid should exist");
    assert!(
        !init.is_axiom,
        "KernelInitialStateValid should be a derived theorem"
    );
    assert_eq!(
        init.proof_status,
        ProofStatus::DerivedPending,
        "KernelInitialStateValid should remain pending until the initial-state axioms are discharged"
    );
    assert!(
        init.value_src.is_some(),
        "KernelInitialStateValid should have a proof term"
    );

    let deps = init
        .dependencies
        .as_ref()
        .expect("KernelInitialStateValid should record dependencies");
    assert!(
        deps.contains("KernelStateMatchesSpec.mk"),
        "should compose via the summary builder, got {deps:?}"
    );
    assert!(
        deps.contains("kernel_empty_env_valid"),
        "should use the empty-env axiom, got {deps:?}"
    );
    assert!(
        deps.contains("kernel_empty_ctx_well_formed"),
        "should use the empty-ctx axiom, got {deps:?}"
    );

    // Both base-case leaves are now PROVED: kernel_empty_env_valid via
    // DefinitionalExtension.refl and kernel_empty_ctx_well_formed via
    // KernelLocalCtxWellFormed.nil. Neither appears as an axiom leaf any longer,
    // so KernelInitialStateValid's recorded axiom closure is now empty.
    assert!(
        !init.axiom_deps.contains("kernel_empty_env_valid"),
        "kernel_empty_env_valid was retired to a DerivedProved lemma and must no \
         longer appear as an axiom leaf: {:?}",
        init.axiom_deps
    );
    assert!(
        !init.axiom_deps.contains("kernel_empty_ctx_well_formed"),
        "kernel_empty_ctx_well_formed was retired to a DerivedProved lemma and must \
         no longer appear as an axiom leaf: {:?}",
        init.axiom_deps
    );
    assert!(
        init.axiom_deps.is_empty(),
        "KernelInitialStateValid should depend on zero remaining axiom leaves \
         after both base-case lemmas were proved: {:?}",
        init.axiom_deps
    );
}

#[test]
fn test_implementation_soundness_theorems_are_pending() {
    let spec = build_spec_with_stack();
    for name in [
        "KernelInferSound",
        "KernelCheckSound",
        "KernelWhnfSound",
        "KernelDefEqSound",
        "KernelWhnfPreservesTyping",
    ] {
        let def = spec
            .definitions()
            .get(name)
            .unwrap_or_else(|| panic!("missing implementation-soundness theorem {name}"));
        assert_eq!(
            def.proof_status,
            ProofStatus::DerivedPending,
            "{name} should remain a pending proof target"
        );
        assert_eq!(
            def.trust_level(),
            TrustLevel::AxiomPending,
            "{name} should surface as a pending trust assumption until #461 is proved"
        );
        assert!(
            !def.is_axiom,
            "{name} should be tracked as a theorem wrapper, not a foundational axiom"
        );
    }
}

#[test]
fn test_implementation_soundness_aliases_reduce_axioms() {
    let spec = build_spec_with_stack();

    for name in ["KernelStateEnvValid", "KernelStateLocalCtxWellFormed"] {
        assert_split_state_predicate_pending(&spec, name);
        assert_alias_is_semireducible(&spec, name);
    }

    assert_constructive_input_admissibility(&spec);
    assert_summary_state_alias(&spec);
}

#[test]
fn test_implementation_soundness_forward_contracts_use_split_state_surface() {
    let _spec = build_spec_with_stack();

    // All four forward contracts are now DerivedLemmas (decomposed):
    // - kernel_infer_returns_well_typed: per-case axioms via KExpr.rec (PART 21f)
    // - kernel_check_returns_well_typed: infer + def_eq steps (PART 21a)
    // - kernel_whnf_returns_def_eq: spec whnf witness + DefEq bridge (PART 21e)
    // - kernel_def_eq_reflects_spec: normalization + structural comparison (PART 21d)
    //
    // kernel_infer_returns_well_typed still preserves the split-state surface
    // (uses KernelStateEnvValid/KernelStateLocalCtxWellFormed, not summary alias).
    // Tested in implementation_soundness_infer_refinement_tests.rs.
}

#[test]
fn test_summary_alias_eliminators_exist_with_deps() {
    let spec = build_spec_with_stack();

    for (name, expected_dep) in [
        ("KernelStateMatchesSpec.envValid", "KernelStateEnvValid"),
        (
            "KernelStateMatchesSpec.ctxWellFormed",
            "KernelStateLocalCtxWellFormed",
        ),
    ] {
        let def = spec
            .definitions()
            .get(name)
            .unwrap_or_else(|| panic!("missing eliminator {name}"));
        assert!(!def.is_axiom, "{name} should now be a derived definition");
        assert_eq!(
            def.proof_status,
            ProofStatus::DerivedPending,
            "{name} should stay pending because the split-state predicates still depend on implementation assumptions"
        );
        let deps = def
            .dependencies
            .as_ref()
            .unwrap_or_else(|| panic!("{name} should record its dependencies"));
        assert!(
            deps.contains("KernelStateMatchesSpec"),
            "{name} should depend on KernelStateMatchesSpec, got {deps:?}"
        );
        assert!(
            deps.contains(expected_dep),
            "{name} should depend on {expected_dep}, got {deps:?}"
        );
    }
}

#[test]
fn test_summary_forward_simulation_wrappers_exist_and_are_derived() {
    let spec = build_spec_with_stack();

    // KernelCheckSound_summary is excluded: its axiom_deps expanded through
    // the decomposition, tested separately in test_check_type_decomposition_deps.
    // KernelWhnfSound_summary is excluded: its axiom_deps now expand through
    // the whnf trace decomposition.
    // KernelDefEqSound_summary is also excluded: its axiom_deps now expand through
    // the def_eq normalization + structural decomposition.
    {
        let (name, expected_raw_axiom) = (
            "KernelInferSound_summary",
            "kernel_infer_returns_well_typed",
        );
        let def = spec
            .definitions()
            .get(name)
            .unwrap_or_else(|| panic!("missing summary wrapper {name}"));
        assert!(
            !def.is_axiom,
            "{name} should be a derived definition, not an axiom"
        );
        assert_eq!(
            def.proof_status,
            ProofStatus::DerivedPending,
            "{name} should remain pending (delegates to pending forward contracts)"
        );
        let deps = def
            .dependencies
            .as_ref()
            .unwrap_or_else(|| panic!("{name} should record its dependencies"));
        assert!(
            deps.contains("KernelStateMatchesSpec.envValid")
                && deps.contains("KernelStateMatchesSpec.ctxWellFormed"),
            "{name} should use the constructive eliminators, got {deps:?}"
        );
        assert!(
            def.axiom_deps.contains(expected_raw_axiom),
            "{name} should transitively depend on {expected_raw_axiom}: {:?}",
            def.axiom_deps
        );
    }
}

#[test]
fn test_kernel_state_summary_alias_is_semireducible() {
    let spec = build_spec_with_stack();
    let info = spec
        .env()
        .get_const(&Name::from_string("KernelStateMatchesSpec"))
        .expect("KernelStateMatchesSpec should be registered");
    assert!(
        matches!(info.reducibility, Reducibility::Regular(_)),
        "KernelStateMatchesSpec should remain semireducible so AndType-based bridge proofs type-check, got {:?}",
        info.reducibility
    );
    assert!(
        !info.is_reducible,
        "KernelStateMatchesSpec should not become fully reducible"
    );
    assert_eq!(
        info.kind,
        ConstantKind::Definition,
        "KernelStateMatchesSpec should remain a regular definition alias"
    );
}
