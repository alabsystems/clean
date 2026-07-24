// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;
use clean_kernel::{BinderInfo, Level};
use std::collections::HashMap;

/// Build `@Eq Nat lhs rhs`.
fn mk_eq(lhs: Expr, rhs: Expr) -> Expr {
    Expr::apps(
        Expr::const_str_levels("Eq", vec![Level::succ(Level::zero())]),
        [Expr::const_str("Nat"), lhs, rhs],
    )
}

/// Wrap `body` in `n` `forall (_ : Nat),` binders.
fn forall_nat(n: u32, body: Expr) -> Expr {
    let mut stmt = body;
    for _ in 0..n {
        stmt = Expr::pi(BinderInfo::Default, Expr::const_str("Nat"), stmt);
    }
    stmt
}

fn nat_add(a: Expr, b: Expr) -> Expr {
    Expr::apps(Expr::const_str("Nat.add"), [a, b])
}

fn nat_mul(a: Expr, b: Expr) -> Expr {
    Expr::apps(Expr::const_str("Nat.mul"), [a, b])
}

fn bindings(pairs: &[(u32, u64)]) -> NatBinding {
    let mut m = HashMap::new();
    for &(k, v) in pairs {
        m.insert(k, v);
    }
    m
}

// --- eval_nat_expr ---

#[test]
fn test_eval_nat_expr_literal_returns_value() {
    let e = Expr::nat_lit(42);
    assert_eq!(eval_nat_expr(&e, &bindings(&[])), Some(42));
}

#[test]
fn test_eval_nat_expr_bound_var_uses_binding() {
    let e = Expr::bvar(0);
    assert_eq!(eval_nat_expr(&e, &bindings(&[(0, 7)])), Some(7));
}

#[test]
fn test_eval_nat_expr_unbound_var_returns_none() {
    let e = Expr::bvar(3);
    assert_eq!(eval_nat_expr(&e, &bindings(&[(0, 1)])), None);
}

#[test]
fn test_eval_nat_expr_add_mirrors_lean() {
    let e = nat_add(Expr::bvar(0), Expr::bvar(1));
    assert_eq!(eval_nat_expr(&e, &bindings(&[(0, 2), (1, 5)])), Some(7));
}

#[test]
fn test_eval_nat_expr_sub_saturates() {
    let e = Expr::apps(Expr::const_str("Nat.sub"), [Expr::bvar(0), Expr::bvar(1)]);
    // 3 - 10 saturates to 0 in Lean Nat.
    assert_eq!(eval_nat_expr(&e, &bindings(&[(0, 3), (1, 10)])), Some(0));
}

#[test]
fn test_eval_nat_expr_div_by_zero_is_zero() {
    let e = Expr::apps(
        Expr::const_str("Nat.div"),
        [Expr::nat_lit(5), Expr::nat_lit(0)],
    );
    assert_eq!(eval_nat_expr(&e, &bindings(&[])), Some(0));
}

#[test]
fn test_eval_nat_expr_mod_by_zero_is_dividend() {
    let e = Expr::apps(
        Expr::const_str("Nat.mod"),
        [Expr::nat_lit(5), Expr::nat_lit(0)],
    );
    assert_eq!(eval_nat_expr(&e, &bindings(&[])), Some(5));
}

#[test]
fn test_eval_nat_expr_pow_zero_is_one() {
    let e = Expr::apps(
        Expr::const_str("Nat.pow"),
        [Expr::nat_lit(0), Expr::nat_lit(0)],
    );
    assert_eq!(eval_nat_expr(&e, &bindings(&[])), Some(1));
}

#[test]
fn test_eval_nat_expr_add_overflow_declines() {
    let e = nat_add(Expr::bvar(0), Expr::bvar(1));
    // u64::MAX + 1 overflows: evaluator must decline (None), never wrap.
    assert_eq!(eval_nat_expr(&e, &bindings(&[(0, u64::MAX), (1, 1)])), None);
}

#[test]
fn test_eval_nat_expr_mul_overflow_declines() {
    let e = nat_mul(Expr::bvar(0), Expr::bvar(1));
    assert_eq!(eval_nat_expr(&e, &bindings(&[(0, u64::MAX), (1, 2)])), None);
}

#[test]
fn test_eval_nat_expr_unknown_op_returns_none() {
    let e = Expr::apps(
        Expr::const_str("Nat.gcd"),
        [Expr::nat_lit(6), Expr::nat_lit(4)],
    );
    assert_eq!(eval_nat_expr(&e, &bindings(&[])), None);
}

#[test]
fn test_eval_nat_expr_lambda_returns_none() {
    // A lambda is not a closed Nat term: fail closed.
    let e = Expr::lam(BinderInfo::Default, Expr::const_str("Nat"), Expr::bvar(0));
    assert_eq!(eval_nat_expr(&e, &bindings(&[(0, 1)])), None);
}

#[test]
fn test_eval_nat_expr_sort_returns_none() {
    assert_eq!(eval_nat_expr(&Expr::prop(), &bindings(&[])), None);
}

#[test]
fn test_eval_nat_expr_wrong_arity_returns_none() {
    // Nat.add applied to a single argument.
    let e = Expr::app(Expr::const_str("Nat.add"), Expr::nat_lit(1));
    assert_eq!(eval_nat_expr(&e, &bindings(&[])), None);
}

// --- extract_eq_body ---

#[test]
fn test_extract_eq_body_commutativity_shape() {
    // forall (a b : Nat), add(a,b) = add(b,a)
    let body = mk_eq(
        nat_add(Expr::bvar(1), Expr::bvar(0)),
        nat_add(Expr::bvar(0), Expr::bvar(1)),
    );
    let stmt = forall_nat(2, body);
    let (n, _lhs, _rhs) = extract_eq_body(&stmt).expect("should extract Eq body");
    assert_eq!(n, 2);
}

#[test]
fn test_extract_eq_body_non_eq_returns_none() {
    // A bare Prop is not a universally quantified equality.
    assert!(extract_eq_body(&Expr::prop()).is_none());
}

// --- test_equation ---

#[test]
fn test_test_equation_commutativity_no_counterexample() {
    // forall a b, add(a,b) = add(b,a)
    let lhs = nat_add(Expr::bvar(1), Expr::bvar(0));
    let rhs = nat_add(Expr::bvar(0), Expr::bvar(1));
    let stmt = forall_nat(2, mk_eq(lhs.clone(), rhs.clone()));
    let seed = deterministic_seed(&stmt, &["Nat.add".to_string()]);
    assert_eq!(
        test_equation(&lhs, &rhs, 2, 100, seed),
        EquationVerdict::NoCounterexample,
    );
}

#[test]
fn test_test_equation_idempotent_add_counterexample() {
    // forall a, add(a,a) = a is false (a=1 gives 2 != 1).
    let lhs = nat_add(Expr::bvar(0), Expr::bvar(0));
    let rhs = Expr::bvar(0);
    let stmt = forall_nat(1, mk_eq(lhs.clone(), rhs.clone()));
    let seed = deterministic_seed(&stmt, &["Nat.add".to_string()]);
    assert_eq!(
        test_equation(&lhs, &rhs, 1, 100, seed),
        EquationVerdict::Counterexample,
    );
}

#[test]
fn test_test_equation_unevaluable_is_inconclusive() {
    // gcd is not modelled => inconclusive (never a counterexample).
    let lhs = Expr::apps(Expr::const_str("Nat.gcd"), [Expr::bvar(0), Expr::bvar(1)]);
    let rhs = Expr::apps(Expr::const_str("Nat.gcd"), [Expr::bvar(1), Expr::bvar(0)]);
    let stmt = forall_nat(2, mk_eq(lhs.clone(), rhs.clone()));
    let seed = deterministic_seed(&stmt, &["Nat.gcd".to_string()]);
    assert_eq!(
        test_equation(&lhs, &rhs, 2, 50, seed),
        EquationVerdict::Inconclusive,
    );
}

#[test]
fn test_test_equation_deterministic_same_seed() {
    let lhs = nat_add(Expr::bvar(0), Expr::bvar(0));
    let rhs = Expr::bvar(0);
    let stmt = forall_nat(1, mk_eq(lhs.clone(), rhs.clone()));
    let seed = deterministic_seed(&stmt, &["Nat.add".to_string()]);
    let v1 = test_equation(&lhs, &rhs, 1, 100, seed);
    let v2 = test_equation(&lhs, &rhs, 1, 100, seed);
    assert_eq!(v1, v2, "same seed must yield same verdict");
}

#[test]
fn test_deterministic_seed_is_stable() {
    let stmt = forall_nat(
        2,
        mk_eq(
            nat_add(Expr::bvar(1), Expr::bvar(0)),
            nat_add(Expr::bvar(0), Expr::bvar(1)),
        ),
    );
    let names = vec!["Nat.add".to_string()];
    assert_eq!(
        deterministic_seed(&stmt, &names),
        deterministic_seed(&stmt, &names),
    );
}
