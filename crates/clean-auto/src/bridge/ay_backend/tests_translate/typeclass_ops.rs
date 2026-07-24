// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! HSub/HDiv/HMod Nat semantics tests (#2254).

use super::support::{build_eq_expr, build_h_binop};
use super::*;
use clean_kernel::name::Name;
use clean_kernel::Expr;
use clean_kernel::MDataValue;

fn build_h_binop_with_ty(op_name: &str, ty: Expr, a: Expr, b: Expr) -> Expr {
    let inst = Expr::const_(Name::from_string("instMDataNat"), vec![]);
    let op = Expr::const_(Name::from_string(op_name), vec![]);
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(Expr::app(Expr::app(op, ty.clone()), ty.clone()), ty),
                inst,
            ),
            a,
        ),
        b,
    )
}

fn mdata_nat_type() -> Expr {
    Expr::mdata(
        vec![(Name::from_string("pp.universes"), MDataValue::Bool(true))],
        Expr::const_(Name::from_string("Nat"), vec![]),
    )
}

/// Test HSub.hSub with Nat uses monus semantics: HSub.hSub(Nat, 3, 5) = 0 (#2254)
///
/// In real .olean files, `a - b` where `a b : Nat` elaborates as
/// `@HSub.hSub Nat Nat Nat instHSubNat a b`, NOT `Nat.sub a b`.
/// This must translate with monus (truncated subtraction) semantics.
#[test]
fn test_hsub_nat_monus_underflow_equals_zero() {
    let mut backend = AyBackend::new(AyLogic::QfLia);
    let sub_expr = build_h_binop("HSub.hSub", "Nat", Expr::nat_lit(3), Expr::nat_lit(5));
    let goal = build_eq_expr(sub_expr, Expr::nat_lit(0));

    let result = backend.prove(&goal).expect("translation should succeed");
    assert!(
        result,
        "HSub.hSub(Nat, 3, 5) = 0 should be provable (monus semantics)"
    );
}

/// Test HSub.hSub with Nat: normal subtraction works (5 - 3 = 2)
#[test]
fn test_hsub_nat_monus_normal_subtraction() {
    let mut backend = AyBackend::new(AyLogic::QfLia);
    let sub_expr = build_h_binop("HSub.hSub", "Nat", Expr::nat_lit(5), Expr::nat_lit(3));
    let goal = build_eq_expr(sub_expr, Expr::nat_lit(2));

    let result = backend.prove(&goal).expect("translation should succeed");
    assert!(result, "HSub.hSub(Nat, 5, 3) = 2 should be provable");
}

/// Test HSub.hSub with Int is NOT monus (can go negative)
#[test]
fn test_hsub_int_not_monus() {
    let mut backend = AyBackend::new(AyLogic::QfLia);
    let sub_expr = build_h_binop("HSub.hSub", "Int", Expr::nat_lit(3), Expr::nat_lit(5));
    let goal = build_eq_expr(sub_expr, Expr::nat_lit(0));

    let result = backend.prove(&goal).expect("translation should succeed");
    assert!(
        !result,
        "HSub.hSub(Int, 3, 5) = 0 should NOT be provable (Int.sub yields -2)"
    );
}

/// Test HDiv.hDiv with Nat uses total division: HDiv.hDiv(Nat, 5, 0) = 0 (#2254)
#[test]
fn test_hdiv_nat_by_zero_equals_zero() {
    let mut backend = AyBackend::new(AyLogic::QfLia);
    let div_expr = build_h_binop("HDiv.hDiv", "Nat", Expr::nat_lit(5), Expr::nat_lit(0));
    let goal = build_eq_expr(div_expr, Expr::nat_lit(0));

    let result = backend.prove(&goal).expect("translation should succeed");
    assert!(
        result,
        "HDiv.hDiv(Nat, 5, 0) = 0 should be provable (total division)"
    );
}

/// Test HDiv.hDiv with Nat: normal division works (6 / 3 = 2)
#[test]
fn test_hdiv_nat_normal_division() {
    let mut backend = AyBackend::new(AyLogic::QfLia);
    let div_expr = build_h_binop("HDiv.hDiv", "Nat", Expr::nat_lit(6), Expr::nat_lit(3));
    let goal = build_eq_expr(div_expr, Expr::nat_lit(2));

    let result = backend.prove(&goal).expect("translation should succeed");
    assert!(result, "HDiv.hDiv(Nat, 6, 3) = 2 should be provable");
}

/// Test HMod.hMod with Nat uses total modulo: HMod.hMod(Nat, 5, 0) = 5 (#2254)
#[test]
fn test_hmod_nat_by_zero_equals_dividend() {
    let mut backend = AyBackend::new(AyLogic::QfLia);
    let mod_expr = build_h_binop("HMod.hMod", "Nat", Expr::nat_lit(5), Expr::nat_lit(0));
    let goal = build_eq_expr(mod_expr, Expr::nat_lit(5));

    let result = backend.prove(&goal).expect("translation should succeed");
    assert!(
        result,
        "HMod.hMod(Nat, 5, 0) = 5 should be provable (total modulo)"
    );
}

/// Test HMod.hMod with Nat: normal modulo works (7 % 3 = 1)
#[test]
fn test_hmod_nat_normal_modulo() {
    let mut backend = AyBackend::new(AyLogic::QfLia);
    let mod_expr = build_h_binop("HMod.hMod", "Nat", Expr::nat_lit(7), Expr::nat_lit(3));
    let goal = build_eq_expr(mod_expr, Expr::nat_lit(1));

    let result = backend.prove(&goal).expect("translation should succeed");
    assert!(result, "HMod.hMod(Nat, 7, 3) = 1 should be provable");
}

#[test]
fn test_hsub_mdata_nat_type_arg_monus_underflow_equals_zero() {
    let mut backend = AyBackend::new(AyLogic::QfLia);
    let sub_expr = build_h_binop_with_ty(
        "HSub.hSub",
        mdata_nat_type(),
        Expr::nat_lit(3),
        Expr::nat_lit(5),
    );
    let goal = build_eq_expr(sub_expr, Expr::nat_lit(0));

    let result = backend.prove(&goal).expect("translation should succeed");
    assert!(
        result,
        "HSub.hSub(MData Nat, 3, 5) = 0 should be provable (monus semantics)"
    );
}

#[test]
fn test_hdiv_mdata_nat_type_arg_by_zero_equals_zero() {
    let mut backend = AyBackend::new(AyLogic::QfLia);
    let div_expr = build_h_binop_with_ty(
        "HDiv.hDiv",
        mdata_nat_type(),
        Expr::nat_lit(5),
        Expr::nat_lit(0),
    );
    let goal = build_eq_expr(div_expr, Expr::nat_lit(0));

    let result = backend.prove(&goal).expect("translation should succeed");
    assert!(
        result,
        "HDiv.hDiv(MData Nat, 5, 0) = 0 should be provable (total division)"
    );
}

#[test]
fn test_hmod_mdata_nat_type_arg_by_zero_equals_dividend() {
    let mut backend = AyBackend::new(AyLogic::QfLia);
    let mod_expr = build_h_binop_with_ty(
        "HMod.hMod",
        mdata_nat_type(),
        Expr::nat_lit(5),
        Expr::nat_lit(0),
    );
    let goal = build_eq_expr(mod_expr, Expr::nat_lit(5));

    let result = backend.prove(&goal).expect("translation should succeed");
    assert!(
        result,
        "HMod.hMod(MData Nat, 5, 0) = 5 should be provable (total modulo)"
    );
}
