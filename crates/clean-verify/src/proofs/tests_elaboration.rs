// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Elaboration tests for soundness proofs.
//!
//! Each test verifies that a proof term (from `ProofLibrary` or spec
//! `value_src`) elaborates and type-checks against the kernel.
//!
//! Split from `proofs/tests.rs` -- Part of #2765.

use super::*;
use crate::test_utils::build_spec_with_stack;
use crate::Specification;

/// Helper to verify a proof against the specification
fn verify_proof(proof_name: &str) -> Result<(), ProofError> {
    let spec = build_spec_with_stack();
    let lib = ProofLibrary::new();
    let proof = lib
        .get(proof_name)
        .ok_or_else(|| ProofError::UnknownProperty(proof_name.to_string()))?;
    proof.verify(&spec)
}

fn verify_definition_value(spec: &Specification, def_name: &str) -> Result<(), ProofError> {
    let def = spec
        .definitions()
        .get(def_name)
        .unwrap_or_else(|| panic!("{def_name} should be in spec"));
    let value_src = def
        .value_src
        .as_ref()
        .unwrap_or_else(|| panic!("{def_name} should have a value_src"));
    let proof = ProofTerm::new(def_name, value_src, "spec-embedded proof term");
    proof.verify(spec)
}

#[test]
fn test_type_preservation_elaborates() {
    let result = verify_proof("TypePreservation");
    assert!(
        result.is_ok(),
        "TypePreservation proof should elaborate and type-check: {:?}",
        result.err()
    );
}

#[test]
fn test_type_preservation_helper_elaborates() {
    let result = verify_proof("type_preservation_helper");
    assert!(
        result.is_ok(),
        "type_preservation_helper proof should elaborate and type-check: {:?}",
        result.err()
    );
}

#[test]
fn test_beta_type_preservation_elaborates() {
    let result = verify_proof("beta_type_preservation");
    assert!(
        result.is_ok(),
        "beta_type_preservation proof should elaborate and type-check: {:?}",
        result.err()
    );
}

/// Part of #464: Verify that the def_eq_typing_iff proof term (bidirectional
/// type preservation via DefEq.rec) elaborates correctly against the kernel.
/// This extracts the value_src from the spec definition and verifies it as a
/// ProofTerm, bridging the gap between the spec-embedded proof and the
/// ProofLibrary verification infrastructure.
#[test]
fn test_def_eq_typing_iff_elaborates() {
    let spec = build_spec_with_stack();
    let result = verify_definition_value(&spec, "def_eq_typing_iff");
    assert!(
        result.is_ok(),
        "def_eq_typing_iff proof should elaborate and type-check: {:?}",
        result.err()
    );
}

#[test]
fn test_substitution_bridge_definitions_elaborate() {
    let spec = build_spec_with_stack();
    for def_name in [
        "instantiate_at_sort",
        "instantiate_at_zero_commutes",
        "instantiate_app_lam_eq",
        "instantiate_subst_commutes_eq",
        // beta_subst_commutes now carries its spliced constructive proof term
        // (#2872): DefEq.beta on the unsubstituted redex transported through
        // def_eq_respects_subst, so the original typing premises suffice.
        "beta_subst_commutes",
    ] {
        let result = verify_definition_value(&spec, def_name);
        assert!(
            result.is_ok(),
            "{def_name} proof should elaborate and type-check: {:?}",
            result.err()
        );
    }
}

#[test]
fn test_substitution_def_eq_definitions_elaborate() {
    let spec = build_spec_with_stack();
    // beta_subst_commutes_at now carries its spliced constructive proof term
    // (#2872): DefEq.beta on the unsubstituted redex transported through
    // def_eq_respects_subst_at, breaking the same-bundle reference cycle.
    for def_name in [
        "instantiate_at_app_preserves_def_eq",
        "instantiate_at_lam_preserves_def_eq",
        "instantiate_at_pi_preserves_def_eq",
        "def_eq_respects_subst_at",
        "def_eq_respects_subst",
        "beta_subst_commutes_at",
    ] {
        let result = verify_definition_value(&spec, def_name);
        assert!(
            result.is_ok(),
            "{def_name} proof should elaborate and type-check: {:?}",
            result.err()
        );
    }
}

/// NO MASQUERADE for the CENTRAL recursive-checker-core lemmas — the `def_eq`
/// substitution-congruence family (app/lam/pi) and `whnf` idempotence.
///
/// The positive checks (`test_substitution_def_eq_definitions_elaborate`,
/// `test_impl_soundness_whnf_decomposition_*`, and `Specification::new()`'s own
/// `add_decl`) confirm each lemma's real proof term type-checks — but a kernel
/// that accepted EVERYTHING would pass that too. This is the discriminating
/// witness: for each lemma, a WELL-FORMED but WRONG-TYPED "proof" must be
/// kernel-REJECTED, and rejected at the TYPE-CHECK (`ProofError::TypeMismatch`),
/// so the rejection is the kernel discriminating on the goal — not a parse/elab
/// artifact.
///   * def_eq congruence (app/lam/pi): a refl-only proof that ignores the
///     congruence hypotheses and returns `DefEq.refl` on the LHS — conclusion
///     `DefEq (inst_at (K X Y)..) (inst_at (K X Y)..)`, NOT the goal
///     `... (inst_at (K X' Y')..)` (the primed vars are free and distinct).
///   * whnf idempotence: the "forgot to advance the endpoint" proof
///     `fun e e' (h : whnf_to e e') => h` — type `... -> whnf_to e e'`, NOT the
///     goal `... -> whnf_to e' e'`.
///
/// This is the same no-masquerade control the trust-certify checker-core lanes
/// enforce, run here in clean-verify's own suite (one shared spec build). It
/// covers two of the three central recursive-core operations (def_eq, whnf).
#[test]
fn test_checker_core_lemma_negative_controls_rejected() {
    let spec = build_spec_with_stack();
    let fakes = [
        (
            "instantiate_at_app_preserves_def_eq",
            "fun (f : KExpr) (f' : KExpr) (a : KExpr) (a' : KExpr) (val : KExpr) (depth : Nat) (hf : DefEq (instantiate_at f val depth) (instantiate_at f' val depth)) (ha : DefEq (instantiate_at a val depth) (instantiate_at a' val depth)) => DefEq.refl (instantiate_at (KExpr.app f a) val depth)",
        ),
        (
            "instantiate_at_lam_preserves_def_eq",
            "fun (A : KExpr) (A' : KExpr) (b : KExpr) (b' : KExpr) (val : KExpr) (depth : Nat) (hA : DefEq (instantiate_at A val depth) (instantiate_at A' val depth)) (hb : DefEq (instantiate_at b val (Nat.succ depth)) (instantiate_at b' val (Nat.succ depth))) => DefEq.refl (instantiate_at (KExpr.lam A b) val depth)",
        ),
        (
            "instantiate_at_pi_preserves_def_eq",
            "fun (A : KExpr) (A' : KExpr) (B : KExpr) (B' : KExpr) (val : KExpr) (depth : Nat) (hA : DefEq (instantiate_at A val depth) (instantiate_at A' val depth)) (hB : DefEq (instantiate_at B val (Nat.succ depth)) (instantiate_at B' val (Nat.succ depth))) => DefEq.refl (instantiate_at (KExpr.pi A B) val depth)",
        ),
        (
            // whnf idempotence: returns the input reduction `h : whnf_to e e'`
            // verbatim, whose type is NOT the goal `whnf_to e' e'`.
            "whnf_idempotent",
            "fun (e : KExpr) (e' : KExpr) (h : whnf_to e e') => h",
        ),
    ];
    for (name, fake) in fakes {
        let result = ProofTerm::new(
            name,
            fake,
            "well-formed wrong-typed fake; must be kernel-rejected",
        )
        .verify(&spec);
        assert!(
            matches!(result, Err(ProofError::TypeMismatch { .. })),
            "{name}: a well-formed but wrong-typed fake MUST be rejected at the type-check \
             (ProofError::TypeMismatch) — the fake elaborates, so a non-TypeMismatch result means \
             either the kernel accepted a vacuous proof (the positive check would then be \
             non-discriminating) or the fake failed to elaborate. Got: {result:?}"
        );
    }
}

#[test]
fn test_impl_state_matches_spec_bridge_proofs_elaborate() {
    for proof_name in [
        "impl_state_matches_spec_mk",
        "impl_state_matches_spec_env_valid",
        "impl_state_matches_spec_ctx_well_formed",
    ] {
        let result = verify_proof(proof_name);
        assert!(
            result.is_ok(),
            "{proof_name} proof should elaborate and type-check: {:?}",
            result.err()
        );
    }
}

#[test]
fn test_implementation_soundness_summary_wrappers_elaborate() {
    let spec = build_spec_with_stack();
    for def_name in [
        "KernelInferSound_summary",
        "KernelCheckSound_summary",
        "KernelWhnfSound_summary",
        "KernelDefEqSound_summary",
    ] {
        let result = verify_definition_value(&spec, def_name);
        assert!(
            result.is_ok(),
            "{def_name} proof should elaborate and type-check: {:?}",
            result.err()
        );
    }
}

#[test]
fn test_implementation_soundness_decomposition_definitions_elaborate() {
    let spec = build_spec_with_stack();
    for def_name in [
        "kernel_whnf_returns_def_eq",
        "def_eq_joinable_reflects",
        "kernel_def_eq_reflects_spec",
        "kernel_check_returns_well_typed",
        // Step 3: the master inversion over the faithful KernelInferAccepts
        // inductive and the six per-case infer lemmas derived from it, plus the
        // bvar-emptiness corollary — each must re-verify fail-closed.
        "kernel_infer_inversion",
        "kernel_infer_bvar_empty",
        "kernel_infer_sort_result",
        "kernel_infer_const_sound",
        "kernel_infer_app_decomposition",
        // kernel_infer_app_fun_type_admissible RETIRED (KernelInferResult
        // un-Skolemization): its guard evidence is recovered directly inside
        // kernel_infer_app_sound's AppInferDecomp elimination.
        "kernel_infer_lam_decomposition",
        "kernel_infer_pi_decomposition",
    ] {
        let result = verify_definition_value(&spec, def_name);
        assert!(
            result.is_ok(),
            "{def_name} proof should elaborate and type-check: {:?}",
            result.err()
        );
    }
}

#[test]
fn test_implementation_soundness_additional_simulation_definitions_elaborate() {
    let spec = build_spec_with_stack();
    for def_name in ["KernelCheckSound", "KernelWhnfPreservesTyping"] {
        let result = verify_definition_value(&spec, def_name);
        assert!(
            result.is_ok(),
            "{def_name} proof should elaborate and type-check: {:?}",
            result.err()
        );
    }
}

#[test]
fn test_implementation_soundness_env_preservation_definitions_elaborate() {
    let spec = build_spec_with_stack();
    for def_name in [
        "KernelAddDeclPreservesEnvValid",
        "kernel_add_decl_preserves_local_ctx_wf",
        "KernelAddDeclPreservesEnvSound",
        "KernelAddDeclPreservesState",
    ] {
        let result = verify_definition_value(&spec, def_name);
        assert!(
            result.is_ok(),
            "{def_name} proof should elaborate and type-check: {:?}",
            result.err()
        );
    }
}

#[test]
fn test_micro_verify_soundness_elaborates() {
    let result = verify_proof("micro_verify_soundness");
    assert!(
        result.is_ok(),
        "micro_verify_soundness proof should elaborate and type-check: {:?}",
        result.err()
    );
}

#[test]
fn test_micro_type_preservation_elaborates() {
    let result = verify_proof("micro_type_pres");
    assert!(
        result.is_ok(),
        "micro_type_pres proof should elaborate and type-check: {:?}",
        result.err()
    );
}

#[test]
fn test_trans_typing_elaborates() {
    let result = verify_proof("trans_typing");
    assert!(
        result.is_ok(),
        "trans_typing proof should elaborate and type-check: {:?}",
        result.err()
    );
}

// test_trans_def_eq_elaborates REMOVED (Brick 3 of the micro-band drain): the
// `trans_def_eq` proof forwarded to the FALSE `kernel_to_micro_def_eq` axiom,
// which was refuted-and-deleted (see tests/axiom_refutation_gate.rs for the
// machine-checked counterexample regression).

#[test]
fn test_def_eq_refl_elaborates() {
    let result = verify_proof("def_eq_refl");
    assert!(
        result.is_ok(),
        "def_eq_refl proof should elaborate and type-check: {:?}",
        result.err()
    );
}

#[test]
fn test_def_eq_symm_elaborates() {
    let result = verify_proof("def_eq_symm");
    assert!(
        result.is_ok(),
        "def_eq_symm proof should elaborate and type-check: {:?}",
        result.err()
    );
}

#[test]
fn test_def_eq_trans_elaborates() {
    let result = verify_proof("def_eq_trans");
    assert!(
        result.is_ok(),
        "def_eq_trans proof should elaborate and type-check: {:?}",
        result.err()
    );
}

#[test]
fn test_subst_typing_elaborates() {
    let result = verify_proof("subst_typing");
    assert!(
        result.is_ok(),
        "subst_typing proof should elaborate and type-check: {:?}",
        result.err()
    );
}

#[test]
fn test_type_conv_elaborates() {
    let result = verify_proof("type_conv");
    assert!(
        result.is_ok(),
        "type_conv proof should elaborate and type-check: {:?}",
        result.err()
    );
}

#[test]
fn test_app_cong_elaborates() {
    let result = verify_proof("app_cong");
    assert!(
        result.is_ok(),
        "app_cong proof should elaborate and type-check: {:?}",
        result.err()
    );
}

#[test]
fn test_lam_cong_elaborates() {
    let result = verify_proof("lam_cong");
    assert!(
        result.is_ok(),
        "lam_cong proof should elaborate and type-check: {:?}",
        result.err()
    );
}

#[test]
fn test_pi_cong_elaborates() {
    let result = verify_proof("pi_cong");
    assert!(
        result.is_ok(),
        "pi_cong proof should elaborate and type-check: {:?}",
        result.err()
    );
}

#[test]
fn test_definitional_extension_proofs_elaborate() {
    for proof_name in [
        "constant_extension_intro",
        "inductive_extension_intro",
        "constant_extension_soundness",
        "inductive_extension_soundness",
        "definitional_extension_soundness",
    ] {
        let result = verify_proof(proof_name);
        assert!(
            result.is_ok(),
            "{proof_name} proof should elaborate and type-check: {:?}",
            result.err()
        );
    }
}
