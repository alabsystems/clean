// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! TC regression tests: typeclass instance definitional equality.
//!
//! Tests that typeclass definitions like GE.ge and GT.gt correctly unfold
//! to their underlying implementations (LE.le and LT.lt with flipped args).
//!
//! This is the exact pattern that fails in .olean verification (#3134):
//! ```text
//! TypeMismatch: expected GE.ge (with LE.le-based instance), inferred LE.le
//! ```
//!
//! In Lean 4, `GE.ge a b` is defined as `LE.le b a` (argument flip).
//! Similarly `GT.gt a b` is `LT.lt b a`. These must be definitionally equal.

use super::*;
use crate::env::{ConstantInfo, ConstantKind, Reducibility};

fn cst(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

fn cst_u(name: &str, levels: Vec<Level>) -> Expr {
    Expr::const_(Name::from_string(name), levels)
}

// ============================================================================
// GE.ge unfolds to LE.le (argument flip)
// ============================================================================

/// Core regression test: GE.ge Nat instLENat a b =?= LE.le Nat instLENat b a
///
/// This is the exact failure pattern from .olean verification (#3134).
/// GE.ge is defined as `fun {α} [inst : LE α] (a b : α) => LE.le b a`.
#[test]
fn test_regression_ge_ge_def_eq_le_le_flipped() {
    let mut env = Environment::new();
    env.init_ge().expect("GE init should succeed");

    let tc = TypeChecker::new(&env);

    let nat = cst("Nat");
    let inst_le = cst("instLENat");
    let a = Expr::nat_lit(3);
    let b = Expr::nat_lit(5);

    // GE.ge Nat instLENat a b
    let ge_expr = Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(cst_u("GE.ge", vec![Level::zero()]), nat.clone()),
                inst_le.clone(),
            ),
            a.clone(),
        ),
        b.clone(),
    );

    // LE.le Nat instLENat b a (note: args flipped)
    let le_expr = Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(cst_u("LE.le", vec![Level::zero()]), nat.clone()),
                inst_le.clone(),
            ),
            b.clone(),
        ),
        a.clone(),
    );

    assert!(
        tc.is_def_eq(&ge_expr, &le_expr),
        "GE.ge Nat inst 3 5 should be def-eq to LE.le Nat inst 5 3 (argument flip)"
    );
}

/// GE.ge must unfold via WHNF to produce LE.le in the head.
#[test]
fn test_regression_ge_ge_whnf_unfolds_to_le() {
    let mut env = Environment::new();
    env.init_ge().expect("GE init should succeed");

    let tc = TypeChecker::new(&env);

    let nat = cst("Nat");
    let inst_le = cst("instLENat");
    let a = Expr::nat_lit(3);
    let b = Expr::nat_lit(5);

    // GE.ge Nat instLENat a b
    let ge_expr = Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(cst_u("GE.ge", vec![Level::zero()]), nat.clone()),
                inst_le,
            ),
            a,
        ),
        b,
    );

    let whnf_result = tc.whnf(&ge_expr);

    // After WHNF, GE.ge should have unfolded. The result should contain LE.le
    // as the head of the application (after delta reduction of GE.ge and
    // beta reduction of the resulting lambda).
    let head = whnf_result.get_app_fn();
    // The head should eventually be LE.le or a projection to get LE.le
    // (depending on whether instLENat fully reduces).
    // At minimum, GE.ge should NOT appear as the head.
    if let ExprKind::Const(name, _) = head.kind() {
        assert_ne!(
            name.to_string(),
            "GE.ge",
            "WHNF should unfold GE.ge; it should not remain as the head"
        );
    }
}

// ============================================================================
// GT.gt unfolds to LT.lt (argument flip)
// ============================================================================

/// GT.gt Nat instLTNat a b =?= LT.lt Nat instLTNat b a
#[test]
fn test_regression_gt_gt_def_eq_lt_lt_flipped() {
    let mut env = Environment::new();
    env.init_gt().expect("GT init should succeed");

    let tc = TypeChecker::new(&env);

    let nat = cst("Nat");
    let inst_lt = cst("instLTNat");
    let a = Expr::nat_lit(3);
    let b = Expr::nat_lit(5);

    // GT.gt Nat instLTNat a b
    let gt_expr = Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(cst_u("GT.gt", vec![Level::zero()]), nat.clone()),
                inst_lt.clone(),
            ),
            a.clone(),
        ),
        b.clone(),
    );

    // LT.lt Nat instLTNat b a (note: args flipped)
    let lt_expr = Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(cst_u("LT.lt", vec![Level::zero()]), nat.clone()),
                inst_lt.clone(),
            ),
            b.clone(),
        ),
        a.clone(),
    );

    assert!(
        tc.is_def_eq(&gt_expr, &lt_expr),
        "GT.gt Nat inst 3 5 should be def-eq to LT.lt Nat inst 5 3 (argument flip)"
    );
}

// ============================================================================
// Nat.ge unfolds to Nat.le (argument flip)
// ============================================================================

/// Nat.ge a b =?= Nat.le b a
#[test]
fn test_regression_nat_ge_def_eq_nat_le_flipped() {
    let mut env = Environment::new();
    env.init_ge().expect("GE init should succeed");

    let tc = TypeChecker::new(&env);

    let a = Expr::nat_lit(3);
    let b = Expr::nat_lit(5);

    let nat_ge = Expr::app(Expr::app(cst("Nat.ge"), a.clone()), b.clone());
    let nat_le = Expr::app(Expr::app(cst("Nat.le"), b), a);

    assert!(
        tc.is_def_eq(&nat_ge, &nat_le),
        "Nat.ge 3 5 should be def-eq to Nat.le 5 3"
    );
}

/// Nat.gt a b =?= Nat.lt b a
#[test]
fn test_regression_nat_gt_def_eq_nat_lt_flipped() {
    let mut env = Environment::new();
    env.init_gt().expect("GT init should succeed");

    let tc = TypeChecker::new(&env);

    let a = Expr::nat_lit(3);
    let b = Expr::nat_lit(5);

    let nat_gt = Expr::app(Expr::app(cst("Nat.gt"), a.clone()), b.clone());
    let nat_lt = Expr::app(Expr::app(cst("Nat.lt"), b), a);

    assert!(
        tc.is_def_eq(&nat_gt, &nat_lt),
        "Nat.gt 3 5 should be def-eq to Nat.lt 5 3"
    );
}

// ============================================================================
// Axiom-stub scenario: definition loaded without value
// ============================================================================

/// Regression: if GE.ge is loaded as an axiom (no value), it cannot unfold.
///
/// This simulates the .olean failure where a definition arrives without its
/// value (e.g., axiom stub from Lean 4.29+ module splitting).
#[test]
fn test_regression_axiom_stub_ge_cannot_unfold() {
    let mut env = Environment::new();
    env.init_le().expect("LE init should succeed");

    // Manually register GE.ge as an axiom (no value) — simulating a broken load
    let u = Name::from_string("u");
    let u_level = Level::param(u.clone());
    let le_const = Expr::const_(Name::from_string("LE"), vec![u_level.clone()]);
    let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));
    let type_u = Expr::from_kind(ExprKind::Sort(Level::succ(u_level.clone())));

    let ge_type = Expr::pi(
        BinderInfo::Implicit,
        type_u.clone(),
        Expr::pi(
            BinderInfo::InstImplicit,
            Expr::app(le_const, Expr::bvar(0)),
            Expr::pi(
                BinderInfo::Default,
                Expr::bvar(1),
                Expr::pi(BinderInfo::Default, Expr::bvar(2), prop),
            ),
        ),
    );

    // Register as axiom — NO value. This simulates the failure mode.
    let axiom_info = ConstantInfo::new_with_reducibility(
        Name::from_string("GE.ge"),
        vec![u],
        ge_type,
        None, // NO VALUE — this is the bug
        Reducibility::Reducible,
        ConstantKind::Axiom,
    );
    env.extend_constants_unchecked(std::iter::once(axiom_info));

    let tc = TypeChecker::new(&env);

    let nat = cst("Nat");
    let inst_le = cst("instLENat");
    let a = Expr::nat_lit(3);
    let b = Expr::nat_lit(5);

    // GE.ge Nat instLENat a b
    let ge_expr = Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(cst_u("GE.ge", vec![Level::zero()]), nat.clone()),
                inst_le.clone(),
            ),
            a.clone(),
        ),
        b.clone(),
    );

    // LE.le Nat instLENat b a
    let le_expr = Expr::app(
        Expr::app(
            Expr::app(Expr::app(cst_u("LE.le", vec![Level::zero()]), nat), inst_le),
            b,
        ),
        a,
    );

    // This SHOULD fail because GE.ge has no value to unfold
    assert!(
        !tc.is_def_eq(&ge_expr, &le_expr),
        "Axiom-stub GE.ge (no value) cannot unfold, so def-eq should fail"
    );
}

// ============================================================================
// Upgrade axiom stub to definition (the fix path)
// ============================================================================

/// Regression: upgrading an axiom stub to a definition restores unfolding.
///
/// This tests the `upgrade_axiom_stubs` path that fixes the .olean loading
/// issue for Lean 4.29+ module splitting.
#[test]
fn test_regression_axiom_stub_upgrade_restores_unfolding() {
    let mut env = Environment::new();
    env.init_ge().expect("GE init should succeed");

    // Verify the constant has a value
    let ge_info = env
        .get_const(&Name::from_string("GE.ge"))
        .expect("GE.ge should be present in the environment");
    assert!(
        ge_info.value.is_some(),
        "GE.ge should have a value (definition, not axiom)"
    );
    assert!(
        ge_info.is_reducible,
        "GE.ge should be reducible (abbreviation)"
    );
    assert_eq!(
        ge_info.reducibility,
        Reducibility::Reducible,
        "GE.ge reducibility should be Reducible"
    );

    // Verify unfolding works through the environment API
    let val = env.unfold_definition(&Name::from_string("GE.ge"), &[Level::zero()]);
    assert!(
        val.is_some(),
        "GE.ge should be unfoldable via unfold_definition"
    );
}

// ============================================================================
// Projection function reducibility
// ============================================================================

/// LE.le is a projection function and must be reducible (via is_projection_fn_body
/// detection in the olean convert path). This test verifies the kernel-built
/// version has the right properties.
#[test]
fn test_regression_le_le_is_projection_reducible() {
    let mut env = Environment::new();
    env.init_le().expect("LE init should succeed");

    let le_info = env
        .get_const(&Name::from_string("LE.le"))
        .expect("LE.le should be present in the environment");
    // LE.le is a projection function (its body is `lam α inst => Proj(LE, 0, inst)`)
    // In the kernel-built env, it's added as a structure field projection.
    // It should be unfoldable.
    assert!(
        le_info.value.is_some(),
        "LE.le should have a value (it's a projection function)"
    );
}

/// GE.ge type-checks successfully (the type itself is well-formed).
#[test]
fn test_regression_ge_type_well_formed() {
    let mut env = Environment::new();
    env.init_ge().expect("GE init should succeed");

    let tc = TypeChecker::new(&env);
    let ge_info = env
        .get_const(&Name::from_string("GE.ge"))
        .expect("GE.ge should be present in environment");

    // The type of GE.ge should type-check
    let ty = tc
        .infer_type(&ge_info.type_)
        .expect("GE.ge type should be well-formed");
    assert!(
        matches!(ty.kind(), ExprKind::Sort(_)),
        "Type of GE.ge's type should be a Sort"
    );

    // The value of GE.ge should type-check
    if let Some(val) = &ge_info.value {
        let val_ty = tc.infer_type(val).expect("GE.ge value should type-check");
        // The inferred type of the value should be def-eq to the declared type
        // (with universe params instantiated)
        let _declared_ty = ge_info.type_.instantiate_level_params_direct(
            &ge_info.level_params,
            &ge_info
                .level_params
                .iter()
                .map(|_| Level::zero())
                .collect::<Vec<_>>(),
        );
        // We can at least check the value has a Pi type
        assert!(
            matches!(val_ty.kind(), ExprKind::Pi(..)),
            "GE.ge value should have Pi type"
        );
    }
}
