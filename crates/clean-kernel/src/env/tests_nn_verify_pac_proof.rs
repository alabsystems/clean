// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for C029 PAC-to-Proof formalization.
//!
//! Status after the 2026-04-27 hypothesis-wrapping pass: the three headline
//! C029 claims (`pac_certification_bound`, `volume_ratio_bound`,
//! `proof_lifting`) are `Declaration::Theorem` entries whose strengthened
//! statements carry the missing evidence locally. The three leaf carriers
//! (`coverage_volume`, `miss_probability`, `proof_certificate`) are
//! `Declaration::Opaque` with the same bodies as before — only the
//! declaration kind flipped. This closes the δ-reduction path that let
//! the pre-#3588 `Rat.le_refl` proofs type-check via alias-collapse
//! (MASQUERADE per `designs/2026-04-19-demasquerade-cxxx-pattern.md`
//! Rules M1 + M4).
//!
//! Part of #3588 (extends #3378, #3467, #3549, #3563).

use crate::env::types::ConstantKind;
use crate::env::Environment;
use crate::expr::{Expr, ExprKind};
use crate::name::Name;
use crate::tc::TypeChecker;

fn make_env() -> Environment {
    let mut env = Environment::new();
    env.init_nn_verify_pac_proof()
        .expect("init_nn_verify_pac_proof");
    env
}

// =============================================================================
// Registration tests
// =============================================================================

#[test]
fn test_pgd_search_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string("NNVerify.PacProof.pgd_search"))
        .is_some());
}

#[test]
fn test_lipschitz_bound_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string("NNVerify.PacProof.lipschitz_bound"))
        .is_some());
}

#[test]
fn test_hessian_bound_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string("NNVerify.PacProof.hessian_bound"))
        .is_some());
}

#[test]
fn test_utility_functions_registered() {
    let env = make_env();
    for name in &[
        "NNVerify.PacProof.nat_to_rat",
        "NNVerify.PacProof.coverage_volume",
        "NNVerify.PacProof.miss_probability",
        "NNVerify.PacProof.proof_certificate",
        "NNVerify.PacProof.pac_confidence",
    ] {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{} should be registered",
            name,
        );
    }
}

// =============================================================================
// 2026-04-27 guard tests — three claims are Theorems, three carriers Opaque
// =============================================================================

#[test]
fn test_c029_pac_certification_bound_is_hypothesis_wrapped_theorem() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string(
            "NNVerify.PacProof.pac_certification_bound",
        ))
        .expect("pac_certification_bound should be registered");
    assert_eq!(
        info.kind,
        ConstantKind::Theorem,
        "pac_certification_bound should be a hypothesis-wrapped Theorem, got {:?}",
        info.kind,
    );
    assert!(
        info.value.is_some(),
        "pac_certification_bound Theorem must carry a local-evidence proof value",
    );
    // `_core` backing Opaque was removed by #3588 — should no longer exist.
    assert!(
        env.get_const(&Name::from_string(
            "NNVerify.PacProof.pac_certification_bound_core"
        ))
        .is_none(),
        "pac_certification_bound_core backing Opaque should be removed after #3588",
    );
}

#[test]
fn test_c029_volume_ratio_bound_is_hypothesis_wrapped_theorem() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string("NNVerify.PacProof.volume_ratio_bound"))
        .expect("volume_ratio_bound should be registered");
    assert_eq!(
        info.kind,
        ConstantKind::Theorem,
        "volume_ratio_bound should be a hypothesis-wrapped Theorem, got {:?}",
        info.kind,
    );
    assert!(
        info.value.is_some(),
        "volume_ratio_bound Theorem must carry a local-evidence proof value",
    );
    assert!(
        env.get_const(&Name::from_string(
            "NNVerify.PacProof.volume_ratio_bound_core"
        ))
        .is_none(),
        "volume_ratio_bound_core backing Opaque should be removed after #3588",
    );
}

#[test]
fn test_c029_proof_lifting_is_hypothesis_wrapped_theorem() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string("NNVerify.PacProof.proof_lifting"))
        .expect("proof_lifting should be registered");
    assert_eq!(
        info.kind,
        ConstantKind::Theorem,
        "proof_lifting should be a hypothesis-wrapped Theorem, got {:?}",
        info.kind,
    );
    assert!(
        info.value.is_some(),
        "proof_lifting Theorem must carry a local-evidence proof value",
    );
    assert!(
        env.get_const(&Name::from_string("NNVerify.PacProof.proof_lifting_core"))
            .is_none(),
        "proof_lifting_core backing Opaque should be removed after #3588",
    );
}

/// After #3588 Branch A co-demotion, `coverage_volume` is an Opaque
/// (declaration kind flipped from reducible Definition; body unchanged).
/// `is_reducible` must be false so δ-reduction does not unfold the carrier
/// during `def_eq` — that was the mechanism behind the pre-#3588 MASQUERADE.
#[test]
fn test_c029_coverage_volume_is_opaque_non_reducible() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string("NNVerify.PacProof.coverage_volume"))
        .expect("coverage_volume should be registered");
    assert_eq!(
        info.kind,
        ConstantKind::Opaque,
        "coverage_volume should be Opaque after #3588 Branch A co-demotion, \
         got {:?}",
        info.kind,
    );
    assert!(
        !info.is_reducible,
        "coverage_volume must not be reducible after #3588 — reducibility \
         reopens the δ-reduction alias-collapse path that the demasquerade \
         closed",
    );
}

/// After #3588, `miss_probability` is an Opaque with `is_reducible=false`.
#[test]
fn test_c029_miss_probability_is_opaque_non_reducible() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string("NNVerify.PacProof.miss_probability"))
        .expect("miss_probability should be registered");
    assert_eq!(
        info.kind,
        ConstantKind::Opaque,
        "miss_probability should be Opaque after #3588 Branch A co-demotion, \
         got {:?}",
        info.kind,
    );
    assert!(
        !info.is_reducible,
        "miss_probability must not be reducible after #3588",
    );
}

/// After #3588, `proof_certificate` is an Opaque with `is_reducible=false`.
#[test]
fn test_c029_proof_certificate_is_opaque_non_reducible() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string("NNVerify.PacProof.proof_certificate"))
        .expect("proof_certificate should be registered");
    assert_eq!(
        info.kind,
        ConstantKind::Opaque,
        "proof_certificate should be Opaque after #3588 Branch A co-demotion, \
         got {:?}",
        info.kind,
    );
    assert!(
        !info.is_reducible,
        "proof_certificate must not be reducible after #3588",
    );
}

// =============================================================================
// Type-checking guards — axiom types still infer as Pi
// =============================================================================

#[test]
fn test_pgd_search_type_checks() {
    let env = make_env();
    let e = Expr::const_(Name::from_string("NNVerify.PacProof.pgd_search"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&e).expect("infer pgd_search type");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_pac_certification_bound_theorem_type_is_pi() {
    let env = make_env();
    let e = Expr::const_(
        Name::from_string("NNVerify.PacProof.pac_certification_bound"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&e)
        .expect("infer pac_certification_bound type");
    assert!(
        matches!(ty.kind(), ExprKind::Pi(..)),
        "pac_certification_bound theorem type should be Pi, got {:?}",
        ty.kind(),
    );
}

#[test]
fn test_volume_ratio_bound_theorem_type_is_pi() {
    let env = make_env();
    let e = Expr::const_(
        Name::from_string("NNVerify.PacProof.volume_ratio_bound"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&e).expect("infer volume_ratio_bound type");
    assert!(
        matches!(ty.kind(), ExprKind::Pi(..)),
        "volume_ratio_bound theorem type should be Pi, got {:?}",
        ty.kind(),
    );
}

#[test]
fn test_proof_lifting_theorem_type_is_pi() {
    let env = make_env();
    let e = Expr::const_(Name::from_string("NNVerify.PacProof.proof_lifting"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&e).expect("infer proof_lifting type");
    assert!(
        matches!(ty.kind(), ExprKind::Pi(..)),
        "proof_lifting theorem type should be Pi, got {:?}",
        ty.kind(),
    );
}

// =============================================================================
// Naming and idempotency
// =============================================================================

#[test]
fn test_idempotent() {
    let mut env = Environment::new();
    env.init_nn_verify_pac_proof().expect("first init");
    env.init_nn_verify_pac_proof().expect("second init");
}

/// Verify all declarations use the `NNVerify.PacProof.` prefix and no
/// stale `_core` or `_axiom` constants remain after #3588.
#[test]
fn test_nn_verify_pac_proof_naming_convention() {
    let env = make_env();
    let names = [
        "NNVerify.PacProof.pgd_search",
        "NNVerify.PacProof.lipschitz_bound",
        "NNVerify.PacProof.hessian_bound",
        "NNVerify.PacProof.nat_to_rat",
        "NNVerify.PacProof.coverage_volume",
        "NNVerify.PacProof.miss_probability",
        "NNVerify.PacProof.proof_certificate",
        "NNVerify.PacProof.pac_confidence",
        "NNVerify.PacProof.pac_certification_bound",
        "NNVerify.PacProof.volume_ratio_bound",
        "NNVerify.PacProof.proof_lifting",
    ];
    for name in &names {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{} should be registered",
            name,
        );
        assert!(
            name.starts_with("NNVerify.PacProof."),
            "{} must use NNVerify.PacProof. prefix",
            name,
        );
    }

    // No stale `_core` / `_axiom` shadows should remain.
    for stale in &[
        "NNVerify.PacProof.pac_certification_bound_core",
        "NNVerify.PacProof.volume_ratio_bound_core",
        "NNVerify.PacProof.proof_lifting_core",
        "NNVerify.PacProof.pac_certification_bound_axiom",
        "NNVerify.PacProof.volume_ratio_bound_axiom",
        "NNVerify.PacProof.proof_lifting_axiom",
    ] {
        assert!(
            env.get_const(&Name::from_string(stale)).is_none(),
            "{} must not exist after #3588 Branch A demasquerade",
            stale,
        );
    }
}

/// Count of domain axioms in C029 after hypothesis-wrapping: zero. The three
/// headline claims are Theorems, and the eight support/carrier declarations are
/// Opaques.
#[test]
fn test_c029_domain_axiom_count_is_zero_after_hypothesis_wrapping() {
    let env = make_env();
    let theorem_names = [
        "NNVerify.PacProof.pac_certification_bound",
        "NNVerify.PacProof.volume_ratio_bound",
        "NNVerify.PacProof.proof_lifting",
    ];
    for name in &theorem_names {
        let info = env
            .get_const(&Name::from_string(name))
            .unwrap_or_else(|| panic!("{} should be registered", name));
        assert_eq!(
            info.kind,
            ConstantKind::Theorem,
            "{} should be Theorem after hypothesis-wrapping",
            name,
        );
    }

    let non_axiom_names = [
        "NNVerify.PacProof.pgd_search",
        "NNVerify.PacProof.lipschitz_bound",
        "NNVerify.PacProof.hessian_bound",
        "NNVerify.PacProof.nat_to_rat",
        "NNVerify.PacProof.coverage_volume",
        "NNVerify.PacProof.miss_probability",
        "NNVerify.PacProof.proof_certificate",
        "NNVerify.PacProof.pac_confidence",
        "NNVerify.PacProof.pac_certification_bound",
        "NNVerify.PacProof.volume_ratio_bound",
        "NNVerify.PacProof.proof_lifting",
    ];
    for name in &non_axiom_names {
        let info = env
            .get_const(&Name::from_string(name))
            .unwrap_or_else(|| panic!("{} should be registered", name));
        assert_ne!(
            info.kind,
            ConstantKind::Axiom,
            "{} must not be an Axiom (it is a support/carrier Opaque)",
            name,
        );
    }
}
