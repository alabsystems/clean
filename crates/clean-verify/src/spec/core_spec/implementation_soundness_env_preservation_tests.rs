// Copyright 2026 Andrew Yates.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use crate::spec::types::{AxiomCategory, ProofStatus, TrustLevel};
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

/// After the Rank-2 drain the consolidated `kernel_add_decl_raw_preservation`
/// HelperAxiom is GONE: no consumer may still expand to it. Both raw halves are
/// now constructive, so consumers rest on the smaller bridge leaf set instead.
fn assert_axiom_deps_drop_consolidated_raw_preservation(
    deps: &std::collections::HashSet<String>,
    theorem_name: &str,
) {
    for forbidden in [
        "kernel_add_decl_raw_preservation",
        "KernelEnvValid",
        "KernelLocalCtxWellFormed",
        "kernel_add_decl_preserves_env_valid_raw",
        "kernel_add_decl_preserves_local_ctx_wf_raw",
    ] {
        assert!(
            !deps.contains(forbidden),
            "{theorem_name} should not retain {forbidden} in axiom_deps after the Rank-2 drain: {deps:?}"
        );
    }
    assert!(
        deps.contains("KernelAddDeclAccepts"),
        "{theorem_name} should rest on the KernelAddDeclAccepts leaf after the drain: {deps:?}"
    );
}

#[test]
fn test_env_preservation_definitions_exist() {
    let spec = build_env_preservation_spec_with_stack();
    for name in [
        "KernelAddDeclAccepts",
        "KernelAddDeclChain",
        "KernelAddDeclChain.refl",
        "KernelAddDeclChain.step",
        "KernelAddDeclChain.rec",
        "kernel_add_decl_extends_env",
        "kernel_add_decl_preserves_env_valid_raw",
        "KernelAddDeclPreservesEnvValid",
        "kernel_add_decl_preserves_local_ctx_wf_raw",
        "kernel_add_decl_preserves_local_ctx_wf",
        "KernelAddDeclPreservesEnvSound",
        "KernelAddDeclPreservesState",
        "KernelAddDeclSound",
        "KernelAddDeclChainSound",
    ] {
        assert!(
            spec.definitions().contains_key(name),
            "expected env-preservation definition {name} to be registered"
        );
    }
}

/// The KernelAddDeclChain family was formerly 4 hand-axiomatized
/// FoundationalRule axioms (type, refl, step, AND a hand-written recursor).
/// It is now a GENUINE inductive registered via `add_inductive`: the kernel
/// checks the constructors and GENERATES `KernelAddDeclChain.rec`, so none of
/// the 4 names may remain a kernel axiom. Pinned fail-closed by KERNEL GROUND
/// TRUTH (the env `ConstantKind`), not just the spec `is_axiom` flag.
#[test]
fn test_env_preservation_chain_family_is_a_genuine_inductive_not_axioms() {
    let spec = build_env_preservation_spec_with_stack();
    for name in [
        "KernelAddDeclChain",
        "KernelAddDeclChain.refl",
        "KernelAddDeclChain.step",
        "KernelAddDeclChain.rec",
    ] {
        let def = spec
            .definitions()
            .get(name)
            .unwrap_or_else(|| panic!("missing env-preservation chain definition {name}"));
        assert!(
            !def.is_axiom,
            "{name} must no longer be flagged as an axiom (genuine add_inductive drain)"
        );
        assert_eq!(
            def.category,
            AxiomCategory::FoundationalRule,
            "{name} should stay recorded as a FoundationalRule inductive component"
        );
        assert!(
            def.elaborated_type.is_some(),
            "{name} should carry the kernel-elaborated type (type_src is a placeholder after add_inductive)"
        );
        // KERNEL GROUND TRUTH: the live env constant must not be an axiom
        // (this is exactly the ConstantKind::Axiom census the ratchet keys on).
        let constant = spec
            .env()
            .get_const(&clean_kernel::Name::from_string(name))
            .unwrap_or_else(|| panic!("{name} should be a live env constant"));
        assert_ne!(
            constant.kind,
            clean_kernel::ConstantKind::Axiom,
            "{name} must not lower to a kernel axiom after the add_inductive conversion"
        );
    }

    // The generated recursor must mention both constructors (it is the real
    // eliminator, not a restated hand axiom); the promoted-parameter shape is
    // what KernelAddDeclChainSound's proof term is written against.
    let rec_ty = spec
        .definitions()
        .get("KernelAddDeclChain.rec")
        .and_then(|d| d.elaborated_type.as_ref())
        .expect("KernelAddDeclChain.rec should have an elaborated type")
        .to_string();
    for ctor in ["KernelAddDeclChain.refl", "KernelAddDeclChain.step"] {
        assert!(
            rec_ty.contains(ctor),
            "generated recursor type should mention {ctor}: {rec_ty}"
        );
    }
}

/// After the axiom-inductivization drains, the two former "helper axioms" of the
/// add_decl bridge are NO LONGER axioms (census 131->73 in this session):
///   - `KernelAddDeclAccepts` was an opaque `KEnv -> KEnv -> Type` HelperAxiom; it
///     is now a genuine 2-constructor inductive (`add_inductive`), so it lowers to
///     a live kernel constant that is NOT an Axiom and sits in the TrustedBase
///     (its spec category is `FoundationalRule`).
///   - `kernel_add_decl_extends_env` was the opaque bridge HelperAxiom; it is now a
///     `DerivedProved` definition (case analysis on the `KernelAddDeclAccepts`
///     inductive lifted through `DefinitionalExtension.const_/.inductive_`) with an
///     EMPTY helper-axiom closure.
#[test]
fn test_env_preservation_former_helper_axioms_are_now_inductivized() {
    let spec = build_env_preservation_spec_with_stack();

    // KernelAddDeclAccepts: opaque HelperAxiom -> genuine inductive.
    let accepts = spec
        .definitions()
        .get("KernelAddDeclAccepts")
        .expect("KernelAddDeclAccepts should exist");
    assert!(
        !accepts.is_axiom,
        "KernelAddDeclAccepts must no longer be flagged as an axiom (drained to a genuine add_inductive)"
    );
    assert_eq!(
        accepts.category,
        AxiomCategory::FoundationalRule,
        "KernelAddDeclAccepts should be recorded as a FoundationalRule inductive component"
    );
    assert_eq!(
        accepts.trust_level(),
        TrustLevel::TrustedBase,
        "KernelAddDeclAccepts should surface as trusted base (an inductive), not a pending assumption"
    );
    // KERNEL GROUND TRUTH: the live env constant must not be an axiom (this is the
    // same ConstantKind census the ratchet keys on, mirroring the chain-family test).
    let accepts_const = spec
        .env()
        .get_const(&clean_kernel::Name::from_string("KernelAddDeclAccepts"))
        .expect("KernelAddDeclAccepts should be a live env constant");
    assert_ne!(
        accepts_const.kind,
        clean_kernel::ConstantKind::Axiom,
        "KernelAddDeclAccepts must not lower to a kernel axiom after the add_inductive conversion"
    );

    // kernel_add_decl_extends_env: opaque bridge HelperAxiom -> DerivedProved bridge.
    let bridge = spec
        .definitions()
        .get("kernel_add_decl_extends_env")
        .expect("kernel_add_decl_extends_env should exist");
    assert!(
        !bridge.is_axiom,
        "kernel_add_decl_extends_env must no longer be an axiom (now a derived bridge)"
    );
    assert_eq!(
        bridge.category,
        AxiomCategory::DerivedLemma,
        "kernel_add_decl_extends_env should be a DerivedLemma"
    );
    assert_eq!(
        bridge.proof_status,
        ProofStatus::DerivedProved,
        "kernel_add_decl_extends_env should be DerivedProved (case analysis on KernelAddDeclAccepts)"
    );
    assert!(
        bridge.axiom_deps.is_empty(),
        "kernel_add_decl_extends_env should have an empty helper-axiom closure now: {:?}",
        bridge.axiom_deps
    );
    assert_eq!(
        bridge.trust_level(),
        TrustLevel::Derived,
        "kernel_add_decl_extends_env should surface as Derived, not pending"
    );
}

#[test]
fn test_env_preservation_derived_theorems_are_pending() {
    let spec = build_env_preservation_spec_with_stack();
    for name in [
        "kernel_add_decl_preserves_env_valid_raw",
        "KernelAddDeclPreservesEnvValid",
        "kernel_add_decl_preserves_local_ctx_wf_raw",
        "kernel_add_decl_preserves_local_ctx_wf",
        "KernelAddDeclPreservesEnvSound",
        "KernelAddDeclPreservesState",
        "KernelAddDeclSound",
        "KernelAddDeclChainSound",
    ] {
        let def = spec
            .definitions()
            .get(name)
            .unwrap_or_else(|| panic!("missing env-preservation theorem {name}"));
        assert!(
            !def.is_axiom,
            "{name} should be a derived lemma, not an axiom"
        );
        assert_eq!(
            def.proof_status,
            ProofStatus::DerivedPending,
            "{name} should remain pending until the raw implementation axioms are discharged"
        );
        assert_eq!(
            def.trust_level(),
            TrustLevel::AxiomPending,
            "{name} should surface as pending because it depends on pending implementation axioms"
        );
    }
}

#[test]
fn test_kernel_add_decl_extends_env_deps() {
    let spec = build_env_preservation_spec_with_stack();
    let def = spec
        .definitions()
        .get("kernel_add_decl_extends_env")
        .expect("kernel_add_decl_extends_env should exist");
    let deps = def
        .dependencies
        .as_ref()
        .expect("kernel_add_decl_extends_env should record dependencies");
    assert!(
        deps.contains("KernelAddDeclAccepts"),
        "should depend on KernelAddDeclAccepts, got {deps:?}"
    );
    assert!(
        deps.contains("DefinitionalExtension"),
        "should depend on DefinitionalExtension, got {deps:?}"
    );
    // DRAIN: kernel_add_decl_extends_env is now DerivedProved. Its proof cases on the
    // KernelAddDeclAccepts INDUCTIVE (no longer a HelperAxiom) and lifts each case
    // through the FoundationalRule DefinitionalExtension.const_/.inductive_
    // constructors, so its transitive helper-axiom closure is EMPTY — nothing in the
    // proof is an axiom. (KernelAddDeclAccepts stays a direct `dependencies` entry
    // above, but contributes no axiom debt because it is an inductive, not an axiom.)
    assert!(
        def.axiom_deps.is_empty(),
        "axiom_deps should be empty now that kernel_add_decl_extends_env is DerivedProved from the KernelAddDeclAccepts inductive: {:?}",
        def.axiom_deps
    );
}

#[test]
fn test_kernel_add_decl_raw_preservation_is_eliminated() {
    // RANK-2 DRAIN: the consolidated kernel_add_decl_raw_preservation HelperAxiom
    // has been ELIMINATED entirely. Both raw projections are now constructive
    // (env half via DefinitionalExtension.trans, local-context half via
    // KernelLocalCtxWellFormed.rec env-transport replay), so there is no longer
    // any preservation axiom to package the obligations. This is a genuine
    // -1 admitted-axiom drain from the live census.
    let spec = build_env_preservation_spec_with_stack();
    assert!(
        !spec
            .definitions()
            .contains_key("kernel_add_decl_raw_preservation"),
        "kernel_add_decl_raw_preservation must be gone after the Rank-2 drain"
    );
    // And it must not survive as a live kernel-env axiom either.
    assert!(
        spec.env()
            .get_const(&clean_kernel::Name::from_string(
                "kernel_add_decl_raw_preservation"
            ))
            .is_none(),
        "kernel_add_decl_raw_preservation must not remain a live env constant"
    );
}

#[test]
fn test_kernel_add_decl_preserves_env_valid_raw_is_projection() {
    let spec = build_env_preservation_spec_with_stack();
    let def = spec
        .definitions()
        .get("kernel_add_decl_preserves_env_valid_raw")
        .expect("kernel_add_decl_preserves_env_valid_raw should exist");
    let deps = def
        .dependencies
        .as_ref()
        .expect("kernel_add_decl_preserves_env_valid_raw should record dependencies");
    assert!(
        !def.is_axiom,
        "kernel_add_decl_preserves_env_valid_raw should now be a derived projection"
    );
    assert_eq!(
        def.proof_status,
        ProofStatus::DerivedPending,
        "kernel_add_decl_preserves_env_valid_raw should remain pending on the consolidated raw axiom"
    );
    assert!(
        def.value_src.is_some(),
        "kernel_add_decl_preserves_env_valid_raw should have a projection proof term"
    );
    assert!(
        deps.contains("kernel_add_decl_extends_env"),
        "kernel_add_decl_preserves_env_valid_raw now composes the impl-to-spec bridge kernel_add_decl_extends_env, got {deps:?}"
    );
    assert!(
        deps.contains("DefinitionalExtension.trans"),
        "kernel_add_decl_preserves_env_valid_raw should transport KernelEnvValid via DefinitionalExtension.trans, got {deps:?}"
    );
    assert!(
        !deps.contains("kernel_add_decl_raw_preservation"),
        "kernel_add_decl_preserves_env_valid_raw should no longer project off the consolidated raw axiom, got {deps:?}"
    );
    assert!(
        deps.contains("KernelEnvValid"),
        "kernel_add_decl_preserves_env_valid_raw should keep KernelEnvValid in its direct dependency surface, got {deps:?}"
    );
    assert!(
        deps.contains("KernelAddDeclAccepts"),
        "kernel_add_decl_preserves_env_valid_raw should keep KernelAddDeclAccepts in its direct dependency surface, got {deps:?}"
    );
    assert_eq!(
        def.axiom_deps,
        std::collections::HashSet::from([
            "kernel_add_decl_extends_env".to_string(),
            "KernelAddDeclAccepts".to_string(),
        ]),
        "kernel_add_decl_preserves_env_valid_raw should now rest on the kernel_add_decl_extends_env bridge HelperAxiom (and its KernelAddDeclAccepts leaf); the env-transport step DefinitionalExtension.trans is FOUNDATIONAL"
    );
}

#[test]
fn test_kernel_add_decl_preserves_env_valid_uses_state_indexed_predicates() {
    let spec = build_env_preservation_spec_with_stack();
    let def = spec
        .definitions()
        .get("KernelAddDeclPreservesEnvValid")
        .expect("KernelAddDeclPreservesEnvValid should exist");
    let deps = def
        .dependencies
        .as_ref()
        .expect("KernelAddDeclPreservesEnvValid should record dependencies");
    assert!(
        !def.is_axiom,
        "KernelAddDeclPreservesEnvValid should now be a derived wrapper"
    );
    assert_eq!(
        def.proof_status,
        ProofStatus::DerivedPending,
        "KernelAddDeclPreservesEnvValid should stay pending because the raw env-validity axiom remains open"
    );
    assert!(
        deps.contains("KernelStateEnvValid"),
        "should use state-indexed KernelStateEnvValid for structural compatibility, got {deps:?}"
    );
    assert!(
        deps.contains("kernel_add_decl_preserves_env_valid_raw"),
        "should delegate to the raw env-validity preservation axiom, got {deps:?}"
    );
    assert!(
        deps.contains("KernelAddDeclAccepts"),
        "wrapper should still mention KernelAddDeclAccepts in its type surface, got {deps:?}"
    );
    assert!(
        !deps.contains("KernelEnvValid"),
        "wrapper should not expose the raw env-validity predicate in its direct dependency surface, got {deps:?}"
    );
    assert!(
        !deps.contains("KernelStateMatchesSpec"),
        "wrapper should stay on the split state predicate, not the summary alias, got {deps:?}"
    );
    assert_axiom_deps_drop_consolidated_raw_preservation(
        &def.axiom_deps,
        "KernelAddDeclPreservesEnvValid",
    );
    assert!(
        def.axiom_deps.contains("kernel_add_decl_extends_env"),
        "KernelAddDeclPreservesEnvValid should now rest on the constructive env-half bridge kernel_add_decl_extends_env: {:?}",
        def.axiom_deps
    );
}

#[test]
fn test_kernel_add_decl_preserves_local_ctx_wf_raw_is_recursor_replay() {
    let spec = build_env_preservation_spec_with_stack();
    let def = spec
        .definitions()
        .get("kernel_add_decl_preserves_local_ctx_wf_raw")
        .expect("kernel_add_decl_preserves_local_ctx_wf_raw should exist");
    let deps = def
        .dependencies
        .as_ref()
        .expect("kernel_add_decl_preserves_local_ctx_wf_raw should record dependencies");
    assert!(
        !def.is_axiom,
        "kernel_add_decl_preserves_local_ctx_wf_raw should be a derived lemma"
    );
    assert_eq!(
        def.proof_status,
        ProofStatus::DerivedPending,
        "kernel_add_decl_preserves_local_ctx_wf_raw should remain pending on the KernelAddDeclAccepts leaf"
    );
    assert!(
        def.value_src.is_some(),
        "kernel_add_decl_preserves_local_ctx_wf_raw should have a constructive proof term"
    );
    // Rank-2: the consolidated raw axiom is gone; transport is a recursor replay.
    assert!(
        !deps.contains("kernel_add_decl_raw_preservation"),
        "kernel_add_decl_preserves_local_ctx_wf_raw must no longer project off the deleted raw axiom, got {deps:?}"
    );
    let value = def
        .value_src
        .as_ref()
        .expect("local-ctx-wf-raw should carry a value");
    assert!(
        value.contains("KernelLocalCtxWellFormed.rec"),
        "the proof should transport via KernelLocalCtxWellFormed.rec env-replay, got {value}"
    );
    for ctor in [
        "KernelLocalCtxWellFormed.nil",
        "KernelLocalCtxWellFormed.cons",
    ] {
        assert!(
            value.contains(ctor),
            "the recursor replay should rebuild witnesses with {ctor}, got {value}"
        );
        assert!(
            deps.contains(ctor),
            "{ctor} should be recorded in the dependency surface, got {deps:?}"
        );
    }
    assert!(
        deps.contains("KernelLocalCtxWellFormed"),
        "kernel_add_decl_preserves_local_ctx_wf_raw should keep KernelLocalCtxWellFormed in its direct dependency surface, got {deps:?}"
    );
    assert!(
        deps.contains("KernelAddDeclAccepts"),
        "kernel_add_decl_preserves_local_ctx_wf_raw should keep KernelAddDeclAccepts in its direct dependency surface, got {deps:?}"
    );
    assert_eq!(
        def.axiom_deps,
        std::collections::HashSet::from(["KernelAddDeclAccepts".to_string()]),
        "the recursor-replay transport rests only on the KernelAddDeclAccepts leaf (in its type), not on any preservation axiom"
    );
}

#[test]
fn test_kernel_add_decl_preserves_local_ctx_wrapper_uses_state_indexed_predicates() {
    let spec = build_env_preservation_spec_with_stack();
    let def = spec
        .definitions()
        .get("kernel_add_decl_preserves_local_ctx_wf")
        .expect("kernel_add_decl_preserves_local_ctx_wf should exist");
    let deps = def
        .dependencies
        .as_ref()
        .expect("kernel_add_decl_preserves_local_ctx_wf should record dependencies");
    assert!(
        !def.is_axiom,
        "kernel_add_decl_preserves_local_ctx_wf should now be a derived wrapper"
    );
    assert_eq!(
        def.proof_status,
        ProofStatus::DerivedPending,
        "kernel_add_decl_preserves_local_ctx_wf should stay pending because the raw local-context axiom remains open"
    );
    assert!(
        deps.contains("KernelStateLocalCtxWellFormed"),
        "wrapper should use state-indexed KernelStateLocalCtxWellFormed, got {deps:?}"
    );
    assert!(
        deps.contains("kernel_add_decl_preserves_local_ctx_wf_raw"),
        "wrapper should delegate to the raw local-context preservation axiom, got {deps:?}"
    );
    assert!(
        !deps.contains("KernelLocalCtxWellFormed"),
        "wrapper should not expose the raw local-context predicate in its direct dependency surface, got {deps:?}"
    );
    assert!(
        !deps.contains("KernelStateMatchesSpec"),
        "wrapper should stay on the split state predicate, not the summary alias, got {deps:?}"
    );
    assert_axiom_deps_drop_consolidated_raw_preservation(
        &def.axiom_deps,
        "kernel_add_decl_preserves_local_ctx_wf",
    );
    // The local-context half is now a pure recursor-replay transport: its only
    // leaf is KernelAddDeclAccepts (it does NOT touch the env-validity bridge).
    assert!(
        !def.axiom_deps.contains("kernel_add_decl_extends_env"),
        "the local-context wrapper transports KernelLocalCtxWellFormed structurally and must NOT pull in the env-validity bridge: {:?}",
        def.axiom_deps
    );
}

#[test]
fn test_kernel_add_decl_preserves_state_deps() {
    let spec = build_env_preservation_spec_with_stack();
    let def = spec
        .definitions()
        .get("KernelAddDeclPreservesState")
        .expect("KernelAddDeclPreservesState should exist");
    let deps = def
        .dependencies
        .as_ref()
        .expect("KernelAddDeclPreservesState should record dependencies");
    assert!(
        deps.contains("KernelStateMatchesSpec.mk"),
        "should use summary builder, got {deps:?}"
    );
    assert!(
        deps.contains("KernelStateMatchesSpec"),
        "should keep KernelStateMatchesSpec in the direct dependency surface because it appears in the theorem type, got {deps:?}"
    );
    assert!(
        deps.contains("KernelStateMatchesSpec.envValid"),
        "should use env-validity eliminator, got {deps:?}"
    );
    assert!(
        deps.contains("KernelStateMatchesSpec.ctxWellFormed"),
        "should use ctx-wf eliminator, got {deps:?}"
    );
    assert!(
        deps.contains("KernelAddDeclPreservesEnvValid"),
        "should depend on env-validity preservation, got {deps:?}"
    );
    assert!(
        deps.contains("kernel_add_decl_preserves_local_ctx_wf"),
        "should depend on local-ctx-wf preservation, got {deps:?}"
    );
    assert!(
        deps.contains("KernelAddDeclAccepts"),
        "should keep KernelAddDeclAccepts in the direct dependency surface because it appears in the theorem type, got {deps:?}"
    );
    assert_deps_avoid_raw_add_decl_preservation(deps, "KernelAddDeclPreservesState");
    assert_axiom_deps_drop_consolidated_raw_preservation(
        &def.axiom_deps,
        "KernelAddDeclPreservesState",
    );
    assert!(
        def.axiom_deps.contains("kernel_add_decl_extends_env"),
        "KernelAddDeclPreservesState unions the constructive env half, so it rests on kernel_add_decl_extends_env: {:?}",
        def.axiom_deps
    );
}

#[test]
fn test_kernel_add_decl_preserves_env_sound_deps() {
    let spec = build_env_preservation_spec_with_stack();
    let def = spec
        .definitions()
        .get("KernelAddDeclPreservesEnvSound")
        .expect("KernelAddDeclPreservesEnvSound should exist");
    let deps = def
        .dependencies
        .as_ref()
        .expect("KernelAddDeclPreservesEnvSound should record dependencies");
    assert!(
        deps.contains("EnvSound"),
        "should keep EnvSound in the direct dependency surface because it appears in the theorem type, got {deps:?}"
    );
    assert!(
        deps.contains("KernelAddDeclAccepts"),
        "should keep KernelAddDeclAccepts in the direct dependency surface because it appears in the theorem type, got {deps:?}"
    );
    assert!(
        deps.contains("definitional_extension_sound"),
        "should compose through definitional_extension_sound, got {deps:?}"
    );
    assert!(
        deps.contains("kernel_add_decl_extends_env"),
        "should use the impl-to-spec bridge, got {deps:?}"
    );

    for expected in [
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
            "axiom_deps should include {expected}: {:?}",
            def.axiom_deps
        );
    }
}

#[test]
fn test_kernel_add_decl_sound_exists_and_is_derived() {
    let spec = build_env_preservation_spec_with_stack();
    let def = spec
        .definitions()
        .get("KernelAddDeclSound")
        .expect("KernelAddDeclSound should exist");
    assert!(
        !def.is_axiom,
        "KernelAddDeclSound should be a derived theorem"
    );
    assert_eq!(
        def.proof_status,
        ProofStatus::DerivedPending,
        "KernelAddDeclSound should remain pending until its component axioms are discharged"
    );
    assert!(
        def.value_src.is_some(),
        "KernelAddDeclSound should have a proof term"
    );
    assert!(
        def.type_src.contains("ProdType"),
        "KernelAddDeclSound should return a ProdType of state validity and env soundness: {}",
        def.type_src
    );
}

#[test]
fn test_kernel_add_decl_sound_composes_both_components() {
    let spec = build_env_preservation_spec_with_stack();
    let def = spec
        .definitions()
        .get("KernelAddDeclSound")
        .expect("KernelAddDeclSound should exist");
    let deps = def
        .dependencies
        .as_ref()
        .expect("KernelAddDeclSound should record dependencies");

    assert!(
        deps.contains("KernelAddDeclPreservesState"),
        "should compose KernelAddDeclPreservesState for structural validity, got {deps:?}"
    );
    assert!(
        deps.contains("KernelAddDeclPreservesEnvSound"),
        "should compose KernelAddDeclPreservesEnvSound for semantic soundness, got {deps:?}"
    );
    assert!(
        deps.contains("KernelStateMatchesSpec"),
        "should reference KernelStateMatchesSpec in the type surface, got {deps:?}"
    );
    assert!(
        deps.contains("KernelAddDeclAccepts"),
        "should reference KernelAddDeclAccepts in the type surface, got {deps:?}"
    );
    assert!(
        deps.contains("EnvSound"),
        "should reference EnvSound in the type surface, got {deps:?}"
    );
}

#[test]
fn test_kernel_add_decl_sound_axiom_deps_are_union_of_components() {
    let spec = build_env_preservation_spec_with_stack();
    let def = spec
        .definitions()
        .get("KernelAddDeclSound")
        .expect("KernelAddDeclSound should exist");

    // From KernelAddDeclPreservesState (both halves now constructive; the env half
    // surfaces the kernel_add_decl_extends_env bridge instead of the deleted raw axiom):
    assert!(
        def.axiom_deps.contains("kernel_add_decl_extends_env"),
        "axiom_deps should include kernel_add_decl_extends_env (from state preservation): {:?}",
        def.axiom_deps
    );
    assert!(
        !def.axiom_deps.contains("kernel_add_decl_raw_preservation"),
        "the deleted consolidated raw axiom must not appear after the Rank-2 drain: {:?}",
        def.axiom_deps
    );
    // From KernelAddDeclPreservesEnvSound:
    for expected in [
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
            "axiom_deps should include {expected} (from env soundness preservation): {:?}",
            def.axiom_deps
        );
    }
    assert_deps_avoid_raw_add_decl_preservation(
        def.dependencies.as_ref().unwrap(),
        "KernelAddDeclSound",
    );
}
