// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>

use crate::spec::types::ProofStatus;
use crate::test_utils::build_spec_with_stack;
use crate::Specification;

fn build_env_preservation_spec_with_stack() -> Specification {
    build_spec_with_stack()
}

fn assert_deps_avoid_raw_add_decl_preservation(
    deps: &std::collections::HashSet<String>,
    theorem_name: &str,
) {
    for forbidden in [
        "KernelEnvValid",
        "KernelLocalCtxWellFormed",
        "kernel_add_decl_preserves_env_valid_raw",
        "kernel_add_decl_preserves_local_ctx_wf_raw",
    ] {
        assert!(
            !deps.contains(forbidden),
            "{theorem_name} should route through split-state wrappers/eliminators instead of {forbidden}, got {deps:?}"
        );
    }
}

fn assert_chain_simulation_wrapper(
    spec: &Specification,
    name: &str,
    summary: &str,
    input_surface: &str,
    expected_axiom_dep: &str,
) {
    let def = spec
        .definitions()
        .get(name)
        .unwrap_or_else(|| panic!("{name} should exist"));
    assert!(!def.is_axiom, "{name} should be a derived theorem");
    assert_eq!(
        def.proof_status,
        ProofStatus::DerivedPending,
        "{name} should remain pending while its structural leaves are pending"
    );
    let deps = def
        .dependencies
        .as_ref()
        .unwrap_or_else(|| panic!("{name} should record dependencies"));
    for expected in [
        "KernelAddDeclChain",
        "KernelAddDeclChainPreservesState",
        "KernelStateMatchesSpec",
        "EnvSound",
        summary,
        input_surface,
    ] {
        assert!(
            deps.contains(expected),
            "{name} should depend on {expected}: {deps:?}"
        );
    }
    assert_deps_avoid_raw_add_decl_preservation(deps, name);

    let value = def
        .value_src
        .as_ref()
        .unwrap_or_else(|| panic!("{name} should have a proof term"));
    for snippet in ["KernelAddDeclChainPreservesState", summary] {
        assert!(
            value.contains(snippet),
            "{name} proof should mention {snippet}: {value}"
        );
    }

    for expected in [
        "kernel_add_decl_extends_env",
        "KernelAddDeclAccepts",
        "EnvSound",
        expected_axiom_dep,
    ] {
        assert!(
            def.axiom_deps.contains(expected),
            "{name} axiom_deps should include {expected}: {:?}",
            def.axiom_deps
        );
    }
    assert!(
        !def.axiom_deps.contains("kernel_add_decl_raw_preservation"),
        "{name} must not retain the deleted consolidated raw axiom after the Rank-2 drain: {:?}",
        def.axiom_deps
    );
}

#[test]
fn test_kernel_add_decl_chain_sound_exists_and_is_derived() {
    let spec = build_env_preservation_spec_with_stack();
    let def = spec
        .definitions()
        .get("KernelAddDeclChainSound")
        .expect("KernelAddDeclChainSound should exist");
    assert!(
        !def.is_axiom,
        "KernelAddDeclChainSound should be a derived theorem"
    );
    assert_eq!(
        def.proof_status,
        ProofStatus::DerivedPending,
        "KernelAddDeclChainSound should remain pending until the add_decl soundness leaves are discharged"
    );
    assert!(
        def.value_src.is_some(),
        "KernelAddDeclChainSound should have a proof term"
    );
    assert!(
        def.type_src.contains("KernelAddDeclChain"),
        "KernelAddDeclChainSound should quantify over KernelAddDeclChain: {}",
        def.type_src
    );
    assert!(
        def.type_src.contains("ProdType"),
        "KernelAddDeclChainSound should return a ProdType of state validity and env soundness: {}",
        def.type_src
    );
}

#[test]
fn test_kernel_add_decl_chain_sound_uses_chain_recursor_and_step_theorem() {
    let spec = build_env_preservation_spec_with_stack();
    let def = spec
        .definitions()
        .get("KernelAddDeclChainSound")
        .expect("KernelAddDeclChainSound should exist");
    let deps = def
        .dependencies
        .as_ref()
        .expect("KernelAddDeclChainSound should record dependencies");

    for expected in [
        "KernelAddDeclChain",
        "KernelAddDeclChain.rec",
        "KernelAddDeclSound",
        "KernelStateMatchesSpec",
        "KernelAddDeclAccepts",
        "EnvSound",
        "ProdType.mk",
        "ProdType.fst",
        "ProdType.snd",
    ] {
        assert!(
            deps.contains(expected),
            "KernelAddDeclChainSound should depend on {expected}: {deps:?}"
        );
    }
    assert_deps_avoid_raw_add_decl_preservation(deps, "KernelAddDeclChainSound");

    let value = def
        .value_src
        .as_ref()
        .expect("KernelAddDeclChainSound should have a proof term");
    for snippet in [
        "KernelAddDeclChain.rec",
        "KernelAddDeclSound",
        "ProdType.mk",
        "ProdType.fst",
        "ProdType.snd",
    ] {
        assert!(
            value.contains(snippet),
            "KernelAddDeclChainSound proof should mention {snippet}: {value}"
        );
    }
}

#[test]
fn test_kernel_add_decl_chain_sound_axiom_deps_match_step_theorem() {
    let spec = build_env_preservation_spec_with_stack();
    let def = spec
        .definitions()
        .get("KernelAddDeclChainSound")
        .expect("KernelAddDeclChainSound should exist");

    for expected in [
        "kernel_add_decl_extends_env",
        "KernelAddDeclAccepts",
        "FreshDeclName",
        "StrictlyPositiveCtorDecls",
        "WellFormedCtorDecls",
        "EnvSound",
        "constant_extension_preserves_soundness",
        "inductive_extension_preserves_soundness",
    ] {
        assert!(
            def.axiom_deps.contains(expected),
            "KernelAddDeclChainSound axiom_deps should include {expected}: {:?}",
            def.axiom_deps
        );
    }
}

#[test]
fn test_kernel_add_decl_chain_preserves_state_is_projection() {
    let spec = build_env_preservation_spec_with_stack();
    let def = spec
        .definitions()
        .get("KernelAddDeclChainPreservesState")
        .expect("KernelAddDeclChainPreservesState should exist");
    assert!(
        !def.is_axiom,
        "KernelAddDeclChainPreservesState should be a derived theorem"
    );
    assert_eq!(
        def.proof_status,
        ProofStatus::DerivedPending,
        "KernelAddDeclChainPreservesState should remain pending until the add_decl chain leaves are discharged"
    );
    let deps = def
        .dependencies
        .as_ref()
        .expect("KernelAddDeclChainPreservesState should record dependencies");
    for expected in [
        "KernelAddDeclChain",
        "KernelAddDeclChainSound",
        "KernelStateMatchesSpec",
        "EnvSound",
        "ProdType.fst",
    ] {
        assert!(
            deps.contains(expected),
            "KernelAddDeclChainPreservesState should depend on {expected}: {deps:?}"
        );
    }
    let value = def
        .value_src
        .as_ref()
        .expect("KernelAddDeclChainPreservesState should have a proof term");
    for snippet in ["ProdType.fst", "KernelAddDeclChainSound"] {
        assert!(
            value.contains(snippet),
            "KernelAddDeclChainPreservesState proof should mention {snippet}: {value}"
        );
    }
    assert_deps_avoid_raw_add_decl_preservation(deps, "KernelAddDeclChainPreservesState");
}

#[test]
fn test_kernel_infer_sound_chain_exists_and_delegates() {
    let spec = build_env_preservation_spec_with_stack();
    assert_chain_simulation_wrapper(
        &spec,
        "KernelInferSound_chain",
        "KernelInferSound_summary",
        "KernelInferAccepts",
        "kernel_infer_returns_well_typed",
    );
}

#[test]
fn test_kernel_check_sound_chain_exists_and_delegates() {
    let spec = build_env_preservation_spec_with_stack();
    assert_chain_simulation_wrapper(
        &spec,
        "KernelCheckSound_chain",
        "KernelCheckSound_summary",
        "KernelCheckAccepts",
        // The defeq and infer-band skolems were all retired (KernelInferResult
        // un-Skolemization); the check band's residual leaf sentinel is now the
        // named DerivedPending infer dispatcher kernel_infer_returns_well_typed
        // (check_type calls infer).
        "kernel_infer_returns_well_typed",
    );
}

#[test]
fn test_kernel_whnf_sound_chain_exists_and_delegates() {
    let spec = build_env_preservation_spec_with_stack();
    // The whnf-specific obligation kernel_whnf_reduces_to_spec_whnf is now a
    // proved theorem (KernelWhnfAccepts is a faithful inductive), so it no longer
    // appears as an axiom leaf. KernelEnvValid was retired to a DerivedProved
    // lemma (:= EnvSound) and KernelLocalCtxWellFormed was retired to a faithful
    // nil/cons inductive, so neither is a leaf any more. The still-present leaf for
    // this wrapper is the add_decl env-extension obligation FreshDeclName (carried
    // through the constructive env-soundness path, the consolidated raw axiom having
    // been drained in Rank-2), used as the present-leaf sentinel.
    assert_chain_simulation_wrapper(
        &spec,
        "KernelWhnfSound_chain",
        "KernelWhnfSound_summary",
        "KernelWhnfAccepts",
        "FreshDeclName",
    );
}

#[test]
fn test_kernel_defeq_sound_chain_exists_and_delegates() {
    let spec = build_env_preservation_spec_with_stack();
    assert_chain_simulation_wrapper(
        &spec,
        "KernelDefEqSound_chain",
        "KernelDefEqSound_summary",
        "KernelDefEqAccepts",
        // The KernelDefEqNormalLeft/Right skolems were retired (KernelDefEqAccepts.mk
        // now concludes in the skolem-free DefEqJoinable packaged existential), so the
        // defeq chain has no defeq-specific residual leaf; use the add_decl env-extension
        // obligation FreshDeclName as the present-leaf sentinel (as the whnf chain does).
        "FreshDeclName",
    );
}
