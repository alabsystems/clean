// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Value-behavior tests for heterogeneous projection declarations.
//!
//! Tests that `HAdd.hAdd`, `HSub.hSub`, `HMul.hMul` projections applied to
//! concrete Nat instances reduce to correct values through the full chain:
//!   projection → delta-unfold → Expr::proj → delta-unfold instance → Nat.op → reduce_nat
//!
//! Also tests projection body structure for all 9 families
//! (HAdd/HSub/HMul/HDiv/Div/HMod/Mod/HPow/Pow).
//!
//! Part of #1414

use super::*;

/// Build `Nat` type constant.
fn nat_const() -> Expr {
    Expr::const_(Name::from_string("Nat"), vec![])
}

/// Build a Nat literal expression.
fn nat(v: u64) -> Expr {
    Expr::nat_lit(v)
}

/// Build a fully-applied hetero projection call:
///   `<proj>.{0,0,0} Nat Nat Nat <inst> lhs rhs`
fn hetero_proj_nat_app(proj_name: &str, inst_name: &str, lhs: Expr, rhs: Expr) -> Expr {
    let proj = Expr::const_(
        Name::from_string(proj_name),
        vec![Level::zero(), Level::zero(), Level::zero()],
    );
    let nat_ty = nat_const();
    let inst = Expr::const_(Name::from_string(inst_name), vec![]);
    // Apply: proj Nat Nat Nat inst lhs rhs
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(Expr::app(proj, nat_ty.clone()), nat_ty.clone()),
                    nat_ty,
                ),
                inst,
            ),
            lhs,
        ),
        rhs,
    )
}

// =============================================================================
// HAdd.hAdd value reduction through Nat instance
// =============================================================================

#[test]
fn test_hadd_projection_reduces_nat_add() {
    let mut env = Environment::new();
    env.init_nat_hadd_inst().expect("init HAdd Nat inst");

    let tc = TypeChecker::new(&env);

    // HAdd.hAdd.{0,0,0} Nat Nat Nat instHAddNat 2 3  should reduce to 5
    let expr = hetero_proj_nat_app("HAdd.hAdd", "instHAddNat", nat(2), nat(3));
    let result = tc.whnf(&expr);
    assert!(
        tc.is_def_eq(&result, &nat(5)),
        "HAdd.hAdd Nat Nat Nat instHAddNat 2 3 should reduce to 5, got: {result:?}"
    );
}

#[test]
fn test_hadd_projection_reduces_nat_add_zero() {
    let mut env = Environment::new();
    env.init_nat_hadd_inst().expect("init HAdd Nat inst");

    let tc = TypeChecker::new(&env);

    let expr = hetero_proj_nat_app("HAdd.hAdd", "instHAddNat", nat(0), nat(0));
    let result = tc.whnf(&expr);
    assert!(
        tc.is_def_eq(&result, &nat(0)),
        "HAdd.hAdd applied to 0+0 should reduce to 0, got: {result:?}"
    );
}

#[test]
fn test_hadd_projection_reduces_nat_add_large() {
    let mut env = Environment::new();
    env.init_nat_hadd_inst().expect("init HAdd Nat inst");

    let tc = TypeChecker::new(&env);

    let expr = hetero_proj_nat_app("HAdd.hAdd", "instHAddNat", nat(100), nat(200));
    let result = tc.whnf(&expr);
    assert!(
        tc.is_def_eq(&result, &nat(300)),
        "HAdd.hAdd applied to 100+200 should reduce to 300, got: {result:?}"
    );
}

// =============================================================================
// HSub.hSub value reduction through Nat instance
// =============================================================================

#[test]
fn test_hsub_projection_reduces_nat_sub() {
    let mut env = Environment::new();
    env.init_nat_hsub_inst().expect("init HSub Nat inst");

    let tc = TypeChecker::new(&env);

    let expr = hetero_proj_nat_app("HSub.hSub", "instHSubNat", nat(7), nat(3));
    let result = tc.whnf(&expr);
    assert!(
        tc.is_def_eq(&result, &nat(4)),
        "HSub.hSub applied to 7-3 should reduce to 4, got: {result:?}"
    );
}

#[test]
fn test_hsub_projection_reduces_nat_sub_saturating() {
    let mut env = Environment::new();
    env.init_nat_hsub_inst().expect("init HSub Nat inst");

    let tc = TypeChecker::new(&env);

    let expr = hetero_proj_nat_app("HSub.hSub", "instHSubNat", nat(3), nat(7));
    let result = tc.whnf(&expr);
    assert!(
        tc.is_def_eq(&result, &nat(0)),
        "HSub.hSub applied to 3-7 should saturate to 0, got: {result:?}"
    );
}

// =============================================================================
// HMul.hMul value reduction through Nat instance
// =============================================================================

#[test]
fn test_hmul_projection_reduces_nat_mul() {
    let mut env = Environment::new();
    env.init_nat_hmul_inst().expect("init HMul Nat inst");

    let tc = TypeChecker::new(&env);

    let expr = hetero_proj_nat_app("HMul.hMul", "instHMulNat", nat(6), nat(7));
    let result = tc.whnf(&expr);
    assert!(
        tc.is_def_eq(&result, &nat(42)),
        "HMul.hMul applied to 6*7 should reduce to 42, got: {result:?}"
    );
}

#[test]
fn test_hmul_projection_reduces_nat_mul_zero() {
    let mut env = Environment::new();
    env.init_nat_hmul_inst().expect("init HMul Nat inst");

    let tc = TypeChecker::new(&env);

    let expr = hetero_proj_nat_app("HMul.hMul", "instHMulNat", nat(0), nat(99));
    let result = tc.whnf(&expr);
    assert!(
        tc.is_def_eq(&result, &nat(0)),
        "HMul.hMul applied to 0*99 should reduce to 0, got: {result:?}"
    );
}

#[test]
fn test_hmul_projection_reduces_nat_mul_identity() {
    let mut env = Environment::new();
    env.init_nat_hmul_inst().expect("init HMul Nat inst");

    let tc = TypeChecker::new(&env);

    let expr = hetero_proj_nat_app("HMul.hMul", "instHMulNat", nat(1), nat(42));
    let result = tc.whnf(&expr);
    assert!(
        tc.is_def_eq(&result, &nat(42)),
        "HMul.hMul applied to 1*42 should reduce to 42, got: {result:?}"
    );
}

// =============================================================================
// Cross-operation: HAdd.hAdd and HMul.hMul compose correctly
// =============================================================================

#[test]
fn test_hadd_hmul_cross_reduction() {
    let mut env = Environment::new();
    env.init_nat_hadd_inst().expect("init HAdd Nat inst");
    env.init_nat_hmul_inst().expect("init HMul Nat inst");

    let tc = TypeChecker::new(&env);

    // First reduce HMul.hMul(3, 4) → 12, then feed to HAdd
    // whnf doesn't recursively reduce nested applications through Nat.rec,
    // so pre-reduce the inner multiplication.
    let mul_expr = hetero_proj_nat_app("HMul.hMul", "instHMulNat", nat(3), nat(4));
    let mul_result = tc.whnf(&mul_expr);
    assert!(
        tc.is_def_eq(&mul_result, &nat(12)),
        "HMul.hMul(3,4) should reduce to 12, got: {mul_result:?}"
    );

    let add_expr = hetero_proj_nat_app("HAdd.hAdd", "instHAddNat", mul_result, nat(5));
    let result = tc.whnf(&add_expr);
    assert!(
        tc.is_def_eq(&result, &nat(17)),
        "HAdd(12, 5) should reduce to 17, got: {result:?}"
    );
}

// =============================================================================
// Projection body structure tests: verify Expr::proj index is correct
// =============================================================================

/// For each hetero projection, verify the definition value body contains
/// `Expr::proj(ClassName, 0, ...)` — the single-field projection at index 0.
fn assert_projection_body_has_proj(env: &Environment, proj_name: &str, class_name: &str) {
    let info = env
        .get_const(&Name::from_string(proj_name))
        .expect("projection should exist in environment");

    let value = info
        .value
        .as_ref()
        .expect("projection should have a definition value");

    // Walk through lambda binders to reach the body
    let mut expr = value.clone();
    while let ExprKind::Lam(_, _, body) = &expr.kind {
        expr = body.as_ref().clone();
    }

    // Body should be Expr::proj(class_name, 0, <bvar>)
    let expected_class = Name::from_string(class_name);
    assert!(
        matches!(&expr.kind, ExprKind::Proj(name, 0, _) if name == &expected_class),
        "{proj_name} body should be Proj({class_name}, 0, _), got: {:?}",
        expr.kind
    );
}

#[test]
fn test_hadd_projection_body_structure() {
    let mut env = Environment::new();
    env.init_hadd().expect("init HAdd");
    assert_projection_body_has_proj(&env, "HAdd.hAdd", "HAdd");
}

#[test]
fn test_hsub_projection_body_structure() {
    let mut env = Environment::new();
    env.init_hsub().expect("init HSub");
    assert_projection_body_has_proj(&env, "HSub.hSub", "HSub");
}

#[test]
fn test_hmul_projection_body_structure() {
    let mut env = Environment::new();
    env.init_hmul().expect("init HMul");
    assert_projection_body_has_proj(&env, "HMul.hMul", "HMul");
}

#[test]
fn test_hdiv_projection_body_structure() {
    let mut env = Environment::new();
    env.init_hdiv().expect("init HDiv");
    assert_projection_body_has_proj(&env, "HDiv.hDiv", "HDiv");
}

#[test]
fn test_div_projection_body_structure() {
    let mut env = Environment::new();
    env.init_div().expect("init Div");
    assert_projection_body_has_proj(&env, "Div.div", "Div");
}

#[test]
fn test_hmod_projection_body_structure() {
    let mut env = Environment::new();
    env.init_hmod().expect("init HMod");
    assert_projection_body_has_proj(&env, "HMod.hMod", "HMod");
}

#[test]
fn test_mod_projection_body_structure() {
    let mut env = Environment::new();
    env.init_mod().expect("init Mod");
    assert_projection_body_has_proj(&env, "Mod.mod", "Mod");
}

#[test]
fn test_hpow_projection_body_structure() {
    let mut env = Environment::new();
    env.init_hpow().expect("init HPow");
    assert_projection_body_has_proj(&env, "HPow.hPow", "HPow");
}

#[test]
fn test_pow_projection_body_structure() {
    let mut env = Environment::new();
    env.init_pow().expect("init Pow");
    assert_projection_body_has_proj(&env, "Pow.pow", "Pow");
}

// =============================================================================
// Lambda binder count verification for projection values
// =============================================================================

/// Count lambda binders in a projection definition value.
fn count_lam_binders(expr: &Expr) -> usize {
    let mut e = expr;
    let mut count = 0;
    while let ExprKind::Lam(_, _, body) = &e.kind {
        count += 1;
        e = body;
    }
    count
}

#[test]
fn test_hetero_projections_have_4_lambda_binders() {
    let mut env = Environment::new();
    env.init_hadd().expect("init HAdd");
    env.init_hsub().expect("init HSub");
    env.init_hmul().expect("init HMul");
    env.init_hdiv().expect("init HDiv");
    env.init_hmod().expect("init HMod");
    env.init_hpow().expect("init HPow");

    for proj_name in [
        "HAdd.hAdd",
        "HSub.hSub",
        "HMul.hMul",
        "HDiv.hDiv",
        "HMod.hMod",
        "HPow.hPow",
    ] {
        let info = env
            .get_const(&Name::from_string(proj_name))
            .expect("projection should exist");
        let value = info.value.as_ref().expect("should have value");
        let binders = count_lam_binders(value);
        assert_eq!(
            binders, 4,
            "{proj_name} should have 4 lambda binders, got {binders}"
        );
    }
}

#[test]
fn test_binary_projections_have_2_lambda_binders() {
    let mut env = Environment::new();
    env.init_div().expect("init Div");
    env.init_mod().expect("init Mod");

    for proj_name in ["Div.div", "Mod.mod"] {
        let info = env
            .get_const(&Name::from_string(proj_name))
            .expect("projection should exist");
        let value = info.value.as_ref().expect("should have value");
        let binders = count_lam_binders(value);
        assert_eq!(
            binders, 2,
            "{proj_name} should have 2 lambda binders, got {binders}"
        );
    }
}

#[test]
fn test_pow_projection_has_3_lambda_binders() {
    let mut env = Environment::new();
    env.init_pow().expect("init Pow");

    let info = env
        .get_const(&Name::from_string("Pow.pow"))
        .expect("Pow.pow should exist");
    let value = info.value.as_ref().expect("should have value");
    let binders = count_lam_binders(value);
    assert_eq!(
        binders, 3,
        "Pow.pow should have 3 lambda binders, got {binders}"
    );
}

// =============================================================================
// Partial application: projection applied to instance but not operands
// =============================================================================

#[test]
fn test_hadd_projection_partial_reduces_to_nat_add() {
    let mut env = Environment::new();
    env.init_nat_hadd_inst().expect("init HAdd Nat inst");

    let tc = TypeChecker::new(&env);

    let proj = Expr::const_(
        Name::from_string("HAdd.hAdd"),
        vec![Level::zero(), Level::zero(), Level::zero()],
    );
    let nat_ty = nat_const();
    let inst = Expr::const_(Name::from_string("instHAddNat"), vec![]);
    let partial = Expr::app(
        Expr::app(
            Expr::app(Expr::app(proj, nat_ty.clone()), nat_ty.clone()),
            nat_ty,
        ),
        inst,
    );

    // whnf reduces: delta(HAdd.hAdd) → beta × 4 → Proj(HAdd, 0, instHAddNat)
    //   → delta(instHAddNat) → proj on HAdd.mk(Nat,Nat,Nat,Nat.add) → Nat.add
    let result = tc.whnf(&partial);
    let nat_add = Expr::const_(Name::from_string("Nat.add"), vec![]);
    assert!(
        tc.is_def_eq(&result, &nat_add),
        "HAdd.hAdd Nat Nat Nat instHAddNat should whnf to Nat.add, got: {result:?}"
    );
}

#[test]
fn test_hsub_projection_partial_reduces_to_nat_sub() {
    let mut env = Environment::new();
    env.init_nat_hsub_inst().expect("init HSub Nat inst");

    let tc = TypeChecker::new(&env);

    let proj = Expr::const_(
        Name::from_string("HSub.hSub"),
        vec![Level::zero(), Level::zero(), Level::zero()],
    );
    let nat_ty = nat_const();
    let inst = Expr::const_(Name::from_string("instHSubNat"), vec![]);
    let partial = Expr::app(
        Expr::app(
            Expr::app(Expr::app(proj, nat_ty.clone()), nat_ty.clone()),
            nat_ty,
        ),
        inst,
    );

    let result = tc.whnf(&partial);
    let nat_sub = Expr::const_(Name::from_string("Nat.sub"), vec![]);
    assert!(
        tc.is_def_eq(&result, &nat_sub),
        "HSub.hSub Nat Nat Nat instHSubNat should whnf to Nat.sub, got: {result:?}"
    );
}

#[test]
fn test_hmul_projection_partial_reduces_to_nat_mul() {
    let mut env = Environment::new();
    env.init_nat_hmul_inst().expect("init HMul Nat inst");

    let tc = TypeChecker::new(&env);

    let proj = Expr::const_(
        Name::from_string("HMul.hMul"),
        vec![Level::zero(), Level::zero(), Level::zero()],
    );
    let nat_ty = nat_const();
    let inst = Expr::const_(Name::from_string("instHMulNat"), vec![]);
    let partial = Expr::app(
        Expr::app(
            Expr::app(Expr::app(proj, nat_ty.clone()), nat_ty.clone()),
            nat_ty,
        ),
        inst,
    );

    let result = tc.whnf(&partial);
    let nat_mul = Expr::const_(Name::from_string("Nat.mul"), vec![]);
    assert!(
        tc.is_def_eq(&result, &nat_mul),
        "HMul.hMul Nat Nat Nat instHMulNat should whnf to Nat.mul, got: {result:?}"
    );
}
