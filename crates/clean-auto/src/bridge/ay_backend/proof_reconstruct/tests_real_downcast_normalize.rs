// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Direct tests for `real_downcast_normalize` proof transport.

use super::super::expr_builders::mk_add;
use super::super::expr_builders_arith::CmpOp;
use super::super::real_downcast_normalize::normalize_real_cmp_proof_to_ofint;
use ay::Sort;
use clean_kernel::name::Name;
use clean_kernel::{Expr, ExprKind, FVarId};

fn mk_int_ofnat(n: u64) -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("Int.ofNat"), vec![]),
        Expr::nat_lit(n),
    )
}

fn mk_int_add(lhs: &Expr, rhs: &Expr) -> Expr {
    Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Int.add"), vec![]),
            lhs.clone(),
        ),
        rhs.clone(),
    )
}

fn mk_real_ofnat(n: u64) -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("Real.ofNat"), vec![]),
        Expr::nat_lit(n),
    )
}

fn mk_real_ofint(int_expr: Expr) -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("Real.ofInt"), vec![]),
        int_expr,
    )
}

fn mk_real_add(lhs: &Expr, rhs: &Expr) -> Expr {
    Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Real.add"), vec![]),
            lhs.clone(),
        ),
        rhs.clone(),
    )
}

fn mk_add_alias(lhs: &Expr, rhs: &Expr) -> Expr {
    Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Add.add"), vec![]),
            lhs.clone(),
        ),
        rhs.clone(),
    )
}

fn expr_contains_const(expr: &Expr, target: &str) -> bool {
    match expr.strip_mdata().kind() {
        ExprKind::Const(name, _) => name.to_string() == target,
        ExprKind::App(fun, arg) => {
            expr_contains_const(fun, target) || expr_contains_const(arg, target)
        }
        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
            expr_contains_const(ty, target) || expr_contains_const(body, target)
        }
        _ => false,
    }
}

#[test]
fn test_normalize_real_cmp_proof_to_ofint_normalizes_hadd_rhs_and_transports_proof() {
    let lhs = mk_real_ofnat(4);
    let x_int = Expr::const_(Name::from_string("testXI"), vec![]);
    let rhs = mk_add(
        &Sort::Real,
        &mk_real_ofint(x_int.clone()),
        &mk_real_ofnat(1),
    );
    let h_real = Expr::fvar(FVarId::new(90));

    let (lhs_norm, rhs_norm, h_norm) =
        normalize_real_cmp_proof_to_ofint(CmpOp::Le, &lhs, &rhs, &h_real)
            .expect("HAdd-backed Real comparison should normalize to Real.ofInt endpoints");

    assert_eq!(lhs_norm, mk_real_ofint(mk_int_ofnat(4)));
    assert_eq!(
        rhs_norm,
        mk_real_ofint(mk_int_add(&x_int, &mk_int_ofnat(1)))
    );
    assert!(
        expr_contains_const(&h_norm, "Eq.mp"),
        "comparison proof should transport via Eq.mp after endpoint normalization"
    );
    assert!(
        expr_contains_const(&h_norm, "Real.ofNat_eq_ofInt"),
        "normalization should rewrite Real.ofNat leaves through Real.ofNat_eq_ofInt"
    );
    assert!(
        expr_contains_const(&h_norm, "Real.ofInt_add"),
        "normalization should collapse additive endpoints through Real.ofInt_add"
    );
    assert!(
        expr_contains_const(&h_norm, "instLEReal"),
        "Le normalization should rebuild the Real comparison proposition"
    );
    assert!(
        !expr_contains_const(&h_norm, "trustedArith"),
        "endpoint normalization must stay in the kernel proof builders"
    );
}

#[test]
fn test_normalize_real_cmp_proof_to_ofint_handles_lt_on_canonical_real_add() {
    let lhs = mk_real_add(&mk_real_ofnat(2), &mk_real_ofnat(3));
    let y_int = Expr::const_(Name::from_string("testYI"), vec![]);
    let rhs = mk_real_ofint(y_int.clone());
    let h_real = Expr::fvar(FVarId::new(91));

    let (lhs_norm, rhs_norm, h_norm) =
        normalize_real_cmp_proof_to_ofint(CmpOp::Lt, &lhs, &rhs, &h_real)
            .expect("canonical Real.add Lt comparison should normalize");

    assert_eq!(
        lhs_norm,
        mk_real_ofint(mk_int_add(&mk_int_ofnat(2), &mk_int_ofnat(3)))
    );
    assert_eq!(rhs_norm, mk_real_ofint(y_int));
    assert!(
        expr_contains_const(&h_norm, "LT.lt"),
        "Lt normalization should rebuild an LT.lt proposition"
    );
    assert!(
        expr_contains_const(&h_norm, "instLTReal"),
        "Lt normalization should keep the Real lt instance in the transport proof"
    );
    assert!(
        expr_contains_const(&h_norm, "Eq.mp"),
        "Lt normalization should still transport the original proof via Eq.mp"
    );
    assert!(
        expr_contains_const(&h_norm, "Real.ofInt_add"),
        "Lt normalization should include additive endpoint rewriting"
    );
}

#[test]
fn test_normalize_real_cmp_proof_to_ofint_rejects_symbolic_real_leaf() {
    let lhs = Expr::const_(Name::from_string("testReal"), vec![]);
    let rhs = mk_real_ofnat(0);
    let h_real = Expr::fvar(FVarId::new(92));

    assert!(
        normalize_real_cmp_proof_to_ofint(CmpOp::Le, &lhs, &rhs, &h_real).is_none(),
        "unsupported symbolic Real leaves should fail closed instead of inventing a cast proof"
    );
}

/// Both endpoints already `Real.ofInt(_)` — normalization is identity.
///
/// The proof transport should use `Eq.refl` at each leaf (no `ofNat_eq_ofInt`
/// or `ofInt_add` needed) but still produce a valid `Eq.mp` wrapper because
/// both `mk_real_cmp_prop(original)` and `mk_real_cmp_prop(normalized)` are
/// structurally identical.
#[test]
fn test_normalize_identity_both_already_ofint() {
    let m = Expr::const_(Name::from_string("testM"), vec![]);
    let n = Expr::const_(Name::from_string("testN"), vec![]);
    let lhs = mk_real_ofint(m.clone());
    let rhs = mk_real_ofint(n.clone());
    let h_real = Expr::fvar(FVarId::new(93));

    let (lhs_norm, rhs_norm, h_norm) =
        normalize_real_cmp_proof_to_ofint(CmpOp::Le, &lhs, &rhs, &h_real)
            .expect("already-ofInt endpoints should normalize trivially");

    assert_eq!(lhs_norm, mk_real_ofint(m));
    assert_eq!(rhs_norm, mk_real_ofint(n));
    // No ofNat rewriting needed — leaves are already ofInt.
    assert!(
        !expr_contains_const(&h_norm, "Real.ofNat_eq_ofInt"),
        "identity normalization should not invoke ofNat-to-ofInt rewriting"
    );
    assert!(
        !expr_contains_const(&h_norm, "Real.ofInt_add"),
        "identity normalization should not invoke additive collapsing"
    );
}

/// Nested `Real.add(Real.add(ofNat(1), ofNat(2)), ofNat(3))` — tests that
/// the recursive normalization correctly descends into both sides of a
/// two-level additive tree.
#[test]
fn test_normalize_nested_real_add() {
    let inner_add = mk_real_add(&mk_real_ofnat(1), &mk_real_ofnat(2));
    let lhs = mk_real_add(&inner_add, &mk_real_ofnat(3));
    let rhs = mk_real_ofnat(6);
    let h_real = Expr::fvar(FVarId::new(94));

    let (lhs_norm, rhs_norm, h_norm) =
        normalize_real_cmp_proof_to_ofint(CmpOp::Le, &lhs, &rhs, &h_real)
            .expect("nested Real.add should normalize recursively");

    // LHS: Real.ofInt(Int.add(Int.add(ofNat(1), ofNat(2)), ofNat(3)))
    let inner_int_add = mk_int_add(&mk_int_ofnat(1), &mk_int_ofnat(2));
    let expected_lhs = mk_real_ofint(mk_int_add(&inner_int_add, &mk_int_ofnat(3)));
    assert_eq!(lhs_norm, expected_lhs);
    assert_eq!(rhs_norm, mk_real_ofint(mk_int_ofnat(6)));
    // Two levels of Real.add means two applications of ofInt_add.
    assert!(
        expr_contains_const(&h_norm, "Real.ofInt_add"),
        "nested normalization should use ofInt_add for collapsing additive tree"
    );
    assert!(
        expr_contains_const(&h_norm, "Real.ofNat_eq_ofInt"),
        "nested normalization should rewrite ofNat leaves"
    );
}

/// Mixed `Real.ofNat` + `Real.ofInt` operands in a `Real.add`.
///
/// Exercises the path where one leaf goes through `ofNat_eq_ofInt` and the
/// other goes through the identity `Eq.refl` path inside `normalize_real_endpoint_to_ofint`.
#[test]
fn test_normalize_mixed_ofnat_ofint_add() {
    let x_int = Expr::const_(Name::from_string("testXI"), vec![]);
    let lhs = mk_real_add(&mk_real_ofnat(5), &mk_real_ofint(x_int.clone()));
    let rhs = mk_real_ofnat(10);
    let h_real = Expr::fvar(FVarId::new(95));

    let (lhs_norm, rhs_norm, h_norm) =
        normalize_real_cmp_proof_to_ofint(CmpOp::Lt, &lhs, &rhs, &h_real)
            .expect("mixed ofNat+ofInt Real.add should normalize");

    assert_eq!(
        lhs_norm,
        mk_real_ofint(mk_int_add(&mk_int_ofnat(5), &x_int))
    );
    assert_eq!(rhs_norm, mk_real_ofint(mk_int_ofnat(10)));
    assert!(
        expr_contains_const(&h_norm, "Real.ofNat_eq_ofInt"),
        "ofNat leaf in mixed add should be rewritten through ofNat_eq_ofInt"
    );
    assert!(
        expr_contains_const(&h_norm, "Real.ofInt_add"),
        "mixed add should still use ofInt_add for collapsing"
    );
}

/// Rejection: right endpoint is a bare `Real.add` with a symbolic (non-ofInt,
/// non-ofNat) leaf, so normalization must fail closed.
#[test]
fn test_normalize_rejects_add_with_symbolic_leaf() {
    let lhs = mk_real_ofnat(1);
    let symbolic = Expr::const_(Name::from_string("symbolicReal"), vec![]);
    let rhs = mk_real_add(&symbolic, &mk_real_ofnat(2));
    let h_real = Expr::fvar(FVarId::new(96));

    assert!(
        normalize_real_cmp_proof_to_ofint(CmpOp::Le, &lhs, &rhs, &h_real).is_none(),
        "Real.add with a symbolic leaf should fail closed"
    );
}

#[test]
fn test_normalize_real_cmp_proof_to_ofint_handles_add_add_alias() {
    let x_int = Expr::const_(Name::from_string("testAliasXI"), vec![]);
    let lhs = mk_add_alias(&mk_real_ofnat(2), &mk_real_ofint(x_int.clone()));
    let rhs = mk_real_ofnat(9);
    let h_real = Expr::fvar(FVarId::new(97));

    let (lhs_norm, rhs_norm, h_norm) =
        normalize_real_cmp_proof_to_ofint(CmpOp::Le, &lhs, &rhs, &h_real)
            .expect("Add.add-backed Real comparison should normalize");

    assert_eq!(
        lhs_norm,
        mk_real_ofint(mk_int_add(&mk_int_ofnat(2), &x_int))
    );
    assert_eq!(rhs_norm, mk_real_ofint(mk_int_ofnat(9)));
    assert!(
        expr_contains_const(&h_norm, "Eq.mp"),
        "alias normalization should still transport the proof via Eq.mp"
    );
    assert!(
        expr_contains_const(&h_norm, "Real.ofInt_add"),
        "alias normalization should still collapse additive endpoints through Real.ofInt_add"
    );
}

/// Rejection: both endpoints are symbolic (neither ofInt nor ofNat nor add).
#[test]
fn test_normalize_rejects_both_symbolic() {
    let lhs = Expr::const_(Name::from_string("symA"), vec![]);
    let rhs = Expr::const_(Name::from_string("symB"), vec![]);
    let h_real = Expr::fvar(FVarId::new(97));

    assert!(
        normalize_real_cmp_proof_to_ofint(CmpOp::Lt, &lhs, &rhs, &h_real).is_none(),
        "both symbolic endpoints should fail closed"
    );
}
