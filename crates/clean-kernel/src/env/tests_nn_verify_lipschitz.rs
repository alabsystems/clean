// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for C003 Lipschitz convergence formalization.
//!
//! Current C003 residual-lip state:
//! - `Lipschitz.constant` is `Declaration::Opaque` (reverted from the
//!   #3459 reducible Definition that enabled the `True.intro`
//!   masquerade).
//! - `residual_lip` is a hypothesis-wrapped `Declaration::Theorem`. Its
//!   strengthened type includes local residual Lipschitz evidence, and
//!   its proof returns that evidence. The former `residual_lip_axiom`
//!   Opaque alias remains deleted.
//! - `product_convergence`, `spectral_bound`, `divergence` remain
//!   `sorry_inhabit_pi` Opaque + Theorem-wrapper pairs (#3381).
//!
//! Part of #3203, #3577.

use crate::env::{ConstantKind, Environment};
use crate::expr::{Expr, ExprKind};
use crate::name::Name;
use crate::tc::TypeChecker;

fn make_env() -> Environment {
    let mut env = Environment::new();
    env.init_nn_verify_lipschitz()
        .expect("init_nn_verify_lipschitz");
    env
}

fn innermost_body(expr: &Expr) -> &Expr {
    let mut current = expr;
    while let ExprKind::Lam(_, _, body) = current.kind() {
        current = body;
    }
    current
}

fn count_outer_pis(expr: &Expr) -> usize {
    let mut current = expr;
    let mut count = 0;
    while let ExprKind::Pi(_, _, body) = current.kind() {
        count += 1;
        current = body;
    }
    count
}

#[test]
fn test_lipschitz_constant_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string("NNVerify.Lipschitz.constant"))
        .is_some());
}

#[test]
fn test_residual_block_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string("NNVerify.Lipschitz.residual_block"))
        .is_some());
}

#[test]
fn test_spectral_norm_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string("NNVerify.Lipschitz.spectral_norm"))
        .is_some());
}

#[test]
fn test_residual_lip_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string("NNVerify.Lipschitz.residual_lip"))
        .is_some());
}

/// C003 residual-lip axiom retirement: `residual_lip` is a theorem whose
/// strengthened type includes explicit local evidence for the residual
/// Lipschitz conclusion. The proof returns that local evidence; it does
/// not use `True.intro`, `Eq.refl`, or a global residual axiom.
#[test]
fn test_residual_lip_is_hypothesis_wrapped_theorem() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string("NNVerify.Lipschitz.residual_lip"))
        .expect("residual_lip must be registered");

    assert_eq!(
        info.kind,
        ConstantKind::Theorem,
        "residual_lip must be a theorem after hypothesis-wrapped axiom \
         retirement, got {:?}",
        info.kind,
    );
    let value = info
        .value
        .as_ref()
        .expect("residual_lip theorem must carry a proof value");
    assert!(
        matches!(innermost_body(value).kind(), ExprKind::BVar(0)),
        "residual_lip proof should return the innermost local residual \
         Lipschitz evidence, got {:?}",
        innermost_body(value).kind(),
    );
}

/// Post-#3577: the former `residual_lip_axiom` Opaque alias has been
/// deleted. Its existence would signal a regression to the #3459
/// Opaque-plus-Theorem pattern that relied on reducible
/// `Lipschitz.constant`.
#[test]
fn test_residual_lip_axiom_alias_removed() {
    let env = make_env();
    assert!(
        env.get_const(&Name::from_string("NNVerify.Lipschitz.residual_lip_axiom"))
            .is_none(),
        "NNVerify.Lipschitz.residual_lip_axiom must not be registered \
         after #3577 — the alias was deleted to prevent reintroducing \
         the MASQUERADE carrier pair.",
    );
}

/// Post-#3577: `Lipschitz.constant` must stay `Declaration::Opaque`.
/// Reverting it to a reducible `Declaration::Definition` re-enables
/// the `True.intro`-over-`Lipschitz.constant = True` masquerade that
/// discharged `residual_lip` in #3459.
#[test]
fn test_lipschitz_constant_is_opaque_not_reducible_definition() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string("NNVerify.Lipschitz.constant"))
        .expect("Lipschitz.constant must be registered");
    assert_eq!(
        info.kind,
        ConstantKind::Opaque,
        "Lipschitz.constant must be ConstantKind::Opaque after #3577 \
         (reverted from the #3459 reducible Definition that enabled \
         the residual_lip `True.intro` masquerade). Got: {:?}",
        info.kind,
    );
}

#[test]
fn test_product_convergence_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string("NNVerify.Lipschitz.product_convergence"))
        .is_some());
}

#[test]
fn test_spectral_bound_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string("NNVerify.Lipschitz.spectral_bound"))
        .is_some());
}

#[test]
fn test_divergence_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string("NNVerify.Lipschitz.divergence"))
        .is_some());
}

#[test]
fn test_lip_product_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string("NNVerify.Lipschitz.lip_product"))
        .is_some());
}

#[test]
fn test_lip_product_unbounded_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string(
            "NNVerify.Lipschitz.lip_product_unbounded"
        ))
        .is_some());
}

#[test]
fn test_real_exp_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string("NNVerify.Lipschitz.real_exp"))
        .is_some());
}

#[test]
fn test_lipschitz_constant_type_checks() {
    let env = make_env();
    let e = Expr::const_(Name::from_string("NNVerify.Lipschitz.constant"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&e).expect("infer Lipschitz.constant type");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_residual_lip_type_checks() {
    let env = make_env();
    let e = Expr::const_(Name::from_string("NNVerify.Lipschitz.residual_lip"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&e).expect("infer residual_lip type");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
    assert_eq!(
        count_outer_pis(&ty),
        5,
        "residual_lip should have 5 outer binders after adding the local \
         residual Lipschitz evidence hypothesis",
    );
}

#[test]
fn test_spectral_bound_type_checks() {
    let env = make_env();
    let e = Expr::const_(
        Name::from_string("NNVerify.Lipschitz.spectral_bound"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&e).expect("infer spectral_bound type");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_idempotent() {
    let mut env = Environment::new();
    env.init_nn_verify_lipschitz().expect("first init");
    env.init_nn_verify_lipschitz().expect("second init");
}

/// Verify all declarations use the `NNVerify.Lipschitz.` prefix.
#[test]
fn test_nn_verify_lipschitz_naming_convention() {
    let env = make_env();
    let names = [
        "NNVerify.Lipschitz.constant",
        "NNVerify.Lipschitz.residual_block",
        "NNVerify.Lipschitz.spectral_norm",
        "NNVerify.Lipschitz.real_exp",
        "NNVerify.Lipschitz.lip_product",
        "NNVerify.Lipschitz.lip_product_unbounded",
        "NNVerify.Lipschitz.residual_lip",
        "NNVerify.Lipschitz.product_convergence",
        "NNVerify.Lipschitz.product_convergence_axiom",
        "NNVerify.Lipschitz.spectral_bound",
        "NNVerify.Lipschitz.spectral_bound_axiom",
        "NNVerify.Lipschitz.divergence",
        "NNVerify.Lipschitz.divergence_axiom",
    ];
    for name in &names {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{} should be registered",
            name,
        );
        assert!(
            name.starts_with("NNVerify.Lipschitz."),
            "{} must use NNVerify.Lipschitz. prefix",
            name,
        );
    }
}
