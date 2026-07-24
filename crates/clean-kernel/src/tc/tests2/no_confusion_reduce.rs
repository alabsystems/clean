// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! noConfusion reduction tests: verifies that the definition-based noConfusion
//! value body (Eq.ndrec + casesOn) reduces correctly through WHNF.
//!
//! Exercises the full chain: delta(noConfusion) → beta → delta(Eq.ndrec) →
//! K-reduce(Eq.rec + Eq.refl) → iota(casesOn). (#2162)

use super::support::make_nat_env_with_eq;
use super::*;

/// Helper: assert a definition's value typechecks against its declared type.
fn assert_def_typechecks(env: &Environment, name: &str) {
    let tc = TypeChecker::new(env);
    let msg = format!("{name} should exist in environment");
    let c = env.get_const(&Name::from_string(name)).expect(&msg);
    let msg = format!("{name} should have a value body");
    let value = c.value.as_ref().expect(&msg);
    let msg = format!("{name} value should type-check");
    tc.check_type(value, &c.type_).expect(&msg);
}

/// Sigma.noConfusion value typechecks (dependent fields use HEq)
#[test]
fn test_sigma_no_confusion_value_typechecks() {
    let env = Environment::with_prelude();
    assert_def_typechecks(&env, "Sigma.noConfusion");
}

/// noConfusion reduction: same constructor, zero fields.
///
/// @Nat.noConfusion.{1} (Type 0) zero zero (Eq.refl.{1} Nat zero)
///   : Nat.noConfusionType.{1} (Type 0) zero zero
///   = (Type 0) → (Type 0)
///
/// Should reduce to `fun (k : Type 0) => k` (identity on P).
#[test]
fn test_no_confusion_zero_zero_reduces() {
    let env = make_nat_env_with_eq();
    let tc = TypeChecker::new(&env);

    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);

    // Build: @Eq.refl.{1} Nat zero : @Eq Nat zero zero
    let eq_refl = Expr::const_(
        Name::from_string("Eq.refl"),
        vec![Level::succ(Level::zero())],
    );
    let h = Expr::app(Expr::app(eq_refl, nat), zero.clone());

    // Build: @Nat.noConfusion.{1} (Type 0) zero zero h
    let nc = Expr::const_(
        Name::from_string("Nat.noConfusion"),
        vec![Level::succ(Level::zero())],
    );
    let app = Expr::app(
        Expr::app(Expr::app(Expr::app(nc, Expr::type_()), zero.clone()), zero),
        h,
    );

    // WHNF should reduce to a lambda (identity: fun k:P => k)
    let result = tc.whnf(&app);

    // Result should be a lambda (fun k => k) or equivalent
    assert!(
        matches!(&result.kind, ExprKind::Lam(..)),
        "Expected lambda (identity) for noConfusion zero/zero, got: {result:?}"
    );
    let ExprKind::Lam(_, domain, body) = &result.kind else {
        unreachable!();
    };
    // domain should be P = Type 0
    assert!(
        matches!(&domain.as_ref().kind, ExprKind::Sort(_)),
        "Lambda domain should be Sort (P=Type 0), got: {domain:?}"
    );
    // body should be BVar(0) (k)
    assert_eq!(
        body.as_ref(),
        &Expr::bvar(0),
        "Lambda body should be BVar(0) (identity), got: {body:?}"
    );
}

/// noConfusion reduction: same constructor, one field (injection).
///
/// @Nat.noConfusion.{1} (Type 0) (succ zero) (succ zero) (Eq.refl.{1} Nat (succ zero))
///   : Nat.noConfusionType.{1} (Type 0) (succ zero) (succ zero)
///   = (@Eq.{1} Nat zero zero → (Type 0)) → (Type 0)
///
/// Should reduce to `fun (k : Eq Nat zero zero → Type 0) => k (Eq.refl.{1} Nat zero)`.
#[test]
fn test_no_confusion_succ_succ_reduces() {
    let env = make_nat_env_with_eq();
    let tc = TypeChecker::new(&env);

    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
    let succ_zero = Expr::app(succ, zero.clone());

    // Build: @Eq.refl.{1} Nat (succ zero) : @Eq Nat (succ zero) (succ zero)
    let eq_refl = Expr::const_(
        Name::from_string("Eq.refl"),
        vec![Level::succ(Level::zero())],
    );
    let h = Expr::app(Expr::app(eq_refl, nat), succ_zero.clone());

    // Build: @Nat.noConfusion.{1} (Type 0) (succ zero) (succ zero) h
    let nc = Expr::const_(
        Name::from_string("Nat.noConfusion"),
        vec![Level::succ(Level::zero())],
    );
    let app = Expr::app(
        Expr::app(
            Expr::app(Expr::app(nc, Expr::type_()), succ_zero.clone()),
            succ_zero,
        ),
        h,
    );

    // WHNF should reduce to a lambda: fun k => k (Eq.refl zero)
    let result = tc.whnf(&app);

    // Result should be a lambda
    assert!(
        matches!(&result.kind, ExprKind::Lam(..)),
        "Expected lambda for noConfusion succ/succ, got: {result:?}"
    );
    let ExprKind::Lam(_, _domain, body) = &result.kind else {
        unreachable!();
    };
    // The body should be an App: k applied to (Eq.refl zero)
    assert!(
        matches!(&body.as_ref().kind, ExprKind::App(..)),
        "Expected App (k applied to refl) in lambda body, got: {body:?}"
    );
    let ExprKind::App(f, _arg) = &body.as_ref().kind else {
        unreachable!();
    };
    // f should be BVar(0) (k)
    assert_eq!(
        f.as_ref(),
        &Expr::bvar(0),
        "Body should apply k=BVar(0), got: {f:?}"
    );
}
