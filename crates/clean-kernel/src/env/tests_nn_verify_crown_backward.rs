// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for CROWN backward propagation theorems (T40-T42, Phase 3).

use crate::env::types::ConstantKind;
use crate::env::Environment;
use crate::expr::{Expr, ExprKind};
use crate::name::Name;
use crate::tc::TypeChecker;
use std::process::Command;

fn make_env() -> Environment {
    let mut env = Environment::new();
    env.init_nn_verify_crown_backward()
        .expect("init_nn_verify_crown_backward");
    env
}

fn opaque_value(env: &Environment, name: &str) -> Expr {
    let info = env
        .get_const(&Name::from_string(name))
        .unwrap_or_else(|| panic!("{name} must be registered"));
    assert_eq!(
        info.kind,
        ConstantKind::Opaque,
        "{name} must be ConstantKind::Opaque before inspecting its canonical synthetic sorryAx value, got {:?}",
        info.kind,
    );
    info.value
        .clone()
        .unwrap_or_else(|| panic!("{name} must be opaque and carry a value"))
}

fn peel_lams(expr: &Expr) -> &Expr {
    let mut curr = expr;
    while let ExprKind::Lam(_, _, body) = curr.kind() {
        curr = body;
    }
    curr
}

fn assert_canonical_synthetic_sorry_ax_body(name: &str, value: &Expr) {
    let body = peel_lams(value);
    assert!(
        body.is_synthetic_sorry(),
        "{name} opaque value body must be canonical synthetic sorryAx, got {body:?}",
    );
    assert!(
        !body.is_non_synthetic_sorry(),
        "{name} opaque value body must not be legacy bare sorry or explicit sorryAx",
    );

    match body.get_app_fn().kind() {
        ExprKind::Const(head, _) => assert_eq!(
            *head,
            Name::from_string("sorryAx"),
            "{name} opaque value body must be headed by sorryAx, got {head:?}",
        ),
        other => panic!("{name} opaque value body must be a sorryAx application, got {other:?}"),
    }

    let args = body.get_app_args();
    assert_eq!(
        args.len(),
        2,
        "{name} synthetic sorryAx body must have goal and synthetic-flag args",
    );
    match args[1].kind() {
        ExprKind::Const(flag, _) => assert!(
            *flag == Name::from_string("Bool.true") || *flag == Name::from_string("true"),
            "{name} synthetic sorryAx flag must be true, got {flag:?}",
        ),
        other => panic!("{name} synthetic sorryAx flag must be true, got {other:?}"),
    }
}

#[test]
fn test_affine_expr_registered() {
    let env = make_env();
    assert!(
        env.get_const(&Name::from_string("NNVerify.CROWN.AffineExpr"))
            .is_some(),
        "NNVerify.CROWN.AffineExpr should be registered",
    );
}

#[test]
fn test_affine_expr_eval_registered() {
    let env = make_env();
    assert!(
        env.get_const(&Name::from_string("NNVerify.CROWN.AffineExpr.eval"))
            .is_some(),
        "NNVerify.CROWN.AffineExpr.eval should be registered",
    );
}

#[test]
fn test_w_pos_neg_decomp_registered() {
    let env = make_env();
    assert!(
        env.get_const(&Name::from_string("NNVerify.CROWN.w_pos_neg_decomp"))
            .is_some(),
        "NNVerify.CROWN.w_pos_neg_decomp should be registered",
    );
}

#[test]
fn test_t40_crown_backward_linear_registered() {
    let env = make_env();
    assert!(
        env.get_const(&Name::from_string("NNVerify.CROWN.crown_backward_linear"))
            .is_some(),
        "T40: NNVerify.CROWN.crown_backward_linear should be registered",
    );
}

#[test]
fn test_t41_crown_backward_layernorm_registered() {
    let env = make_env();
    assert!(
        env.get_const(&Name::from_string(
            "NNVerify.CROWN.crown_backward_layernorm_is_ibp"
        ))
        .is_some(),
        "T41: NNVerify.CROWN.crown_backward_layernorm_is_ibp should be registered",
    );
}

/// MASQUERADE demotion guard (#3507) for T41
/// `NNVerify.CROWN.crown_backward_layernorm_is_ibp`.
///
/// T41 was previously `Declaration::Theorem` with proof term
/// `@Eq.refl (IB n) (CROWN.backward_layernorm n γ β ε B)`. Because
/// `CROWN.backward_layernorm` is a reducible `Declaration::Definition`
/// aliasing `IBP.forward_layernorm` (argument-discarding identity
/// `fun n _ _ _ B => B`), both sides of the equality delta-reduce to the
/// same normal form, so the Eq.refl was vacuous (MASQUERADE M1 + M2 + M4
/// per `designs/2026-04-19-demasquerade-cxxx-pattern.md`). T41 is now
/// `Declaration::Axiom`.
///
/// This guard pins the honest state: if a future commit re-promotes T41 to
/// `Theorem` without restating the claim against faithful CROWN / IBP /
/// LayerNorm carriers (Branch B), this test fails and the regression is
/// caught immediately. A non-None `value` on an Axiom would also indicate a
/// sorry-Opaque masquerade regression.
#[test]
fn test_t41_crown_backward_layernorm_is_ibp_is_axiom_honest_demotion() {
    let env = make_env();
    let name = Name::from_string("NNVerify.CROWN.crown_backward_layernorm_is_ibp");
    let info = env
        .get_const(&name)
        .expect("T41 crown_backward_layernorm_is_ibp must be registered");
    assert_eq!(
        info.kind,
        ConstantKind::Axiom,
        "T41 crown_backward_layernorm_is_ibp must be ConstantKind::Axiom \
         after the #3507 MASQUERADE demotion. A Theorem here almost \
         certainly re-introduces the Eq.refl-between-aliases masquerade: \
         CROWN.backward_layernorm is a reducible Definition aliasing \
         IBP.forward_layernorm, so both sides of the equality reduce to \
         the same term and any Eq.refl proof term is vacuous. See \
         designs/2026-04-19-demasquerade-cxxx-pattern.md and #3507. \
         Got: {:?}",
        info.kind,
    );
    assert!(
        info.value.is_none(),
        "T41 crown_backward_layernorm_is_ibp Axiom must not carry a value; \
         a non-None value suggests a masquerade wrapper (sorry-Opaque or \
         Eq.refl Theorem) was re-introduced. See #3507.",
    );
}

#[test]
fn test_t42_crown_ibp_ratio_one_registered() {
    let env = make_env();
    assert!(
        env.get_const(&Name::from_string("NNVerify.CROWN.crown_ibp_ratio_one"))
            .is_some(),
        "T42: NNVerify.CROWN.crown_ibp_ratio_one should be registered",
    );
}

#[test]
fn test_t40_t42_opaque_values_use_canonical_synthetic_sorry_ax() {
    let env = make_env();
    assert!(
        env.get_const(&Name::from_string("sorryAx")).is_some(),
        "CROWN backward init should run after Bool/sorryAx initialization",
    );

    for name in [
        "NNVerify.CROWN.crown_backward_linear",
        "NNVerify.CROWN.crown_ibp_ratio_one",
    ] {
        let value = opaque_value(&env, name);
        assert_canonical_synthetic_sorry_ax_body(name, &value);
    }
}

#[test]
fn deny_sorry_child_crown_backward_init() {
    if std::env::var("DENY_SORRY_GATE_CHILD").as_deref() != Ok("crown_backward_init") {
        return;
    }
    let mut env = Environment::new();
    let _ = env.init_nn_verify_crown_backward();
}

#[test]
fn test_deny_sorry_blocks_crown_backward_init() {
    let exe = std::env::current_exe().expect("cannot get current test exe path");
    let output = Command::new(&exe)
        .env("DENY_SORRY", "1")
        .env("DENY_SORRY_GATE_CHILD", "crown_backward_init")
        .arg("deny_sorry_child_crown_backward_init")
        .arg("--test-threads=1")
        .arg("--nocapture")
        .output()
        .expect("failed to exec DENY_SORRY child process");

    assert!(
        !output.status.success(),
        "init_nn_verify_crown_backward should panic under DENY_SORRY=1.\nstdout: {}\nstderr: {}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("DENY_SORRY mode enabled"),
        "panic should come from DENY_SORRY sorry creation guard, got stderr:\n{stderr}",
    );
}

#[test]
fn test_idempotent() {
    let mut env = Environment::new();
    env.init_nn_verify_crown_backward().expect("first init");
    env.init_nn_verify_crown_backward()
        .expect("second init should be idempotent");
}

#[test]
fn test_naming_convention() {
    let env = make_env();
    let names = [
        "NNVerify.CROWN.AffineExpr",
        "NNVerify.CROWN.AffineExpr.eval",
        "NNVerify.CROWN.w_pos_neg_decomp",
        "NNVerify.CROWN.crown_backward_linear",
        "NNVerify.CROWN.crown_backward_layernorm_is_ibp",
        "NNVerify.CROWN.crown_ibp_ratio_one",
    ];
    for name in &names {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{} should be registered",
            name,
        );
        assert!(
            name.starts_with("NNVerify."),
            "all names must start with NNVerify. prefix: {}",
            name,
        );
    }
}

#[test]
fn test_affine_expr_type_checks() {
    let env = make_env();
    let aff = Expr::const_(Name::from_string("NNVerify.CROWN.AffineExpr"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&aff).expect("infer AffineExpr type");
    assert!(
        matches!(ty.kind(), ExprKind::Pi(..)),
        "AffineExpr should have Pi type (Nat -> Nat -> Type)",
    );
}

#[test]
fn test_t40_type_checks() {
    let env = make_env();
    let theorem = Expr::const_(
        Name::from_string("NNVerify.CROWN.crown_backward_linear"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&theorem)
        .expect("infer crown_backward_linear type");
    assert!(
        matches!(ty.kind(), ExprKind::Pi(..)),
        "T40 should have Pi type (universally quantified)",
    );
}

#[test]
fn test_t41_type_checks() {
    let env = make_env();
    let theorem = Expr::const_(
        Name::from_string("NNVerify.CROWN.crown_backward_layernorm_is_ibp"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&theorem)
        .expect("infer crown_backward_layernorm_is_ibp type");
    assert!(
        matches!(ty.kind(), ExprKind::Pi(..)),
        "T41 should have Pi type (universally quantified)",
    );
}

#[test]
fn test_t42_type_checks() {
    let env = make_env();
    let theorem = Expr::const_(
        Name::from_string("NNVerify.CROWN.crown_ibp_ratio_one"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&theorem)
        .expect("infer crown_ibp_ratio_one type");
    assert!(
        matches!(ty.kind(), ExprKind::Pi(..)),
        "T42 should have Pi type (universally quantified)",
    );
}
