// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the `requires_lossy_guard` trust boundary and end-to-end lossy
//! atom tracking through `prop_to_literal` and `translate_term`.
//!
//! `requires_lossy_guard` is the single decision point that determines whether
//! an opaque proposition is treated as a stable uninterpreted atom (safe) or as
//! a lossy placeholder that forces SMT results to degrade to Unknown. This is
//! the core soundness boundary of the SMT bridge.

use super::*;
use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Expr, FVarId, Level};

// ========================================================================
// Unit tests for requires_lossy_guard classification boundary
// ========================================================================

#[test]
fn test_lossy_guard_const_is_safe() {
    let expr = Expr::const_(Name::from_string("p"), vec![]);
    assert!(
        !SmtBridge::requires_lossy_guard(&expr),
        "bare Const should not require lossy guard"
    );
}

#[test]
fn test_lossy_guard_fvar_is_safe() {
    let expr = Expr::fvar(FVarId::new(42));
    assert!(
        !SmtBridge::requires_lossy_guard(&expr),
        "bare FVar should not require lossy guard"
    );
}

#[test]
fn test_lossy_guard_const_headed_app_is_safe() {
    let expr = Expr::app(
        Expr::const_(Name::from_string("f"), vec![]),
        Expr::const_(Name::from_string("a"), vec![]),
    );
    assert!(
        !SmtBridge::requires_lossy_guard(&expr),
        "Const-headed application should not require lossy guard"
    );
}

#[test]
fn test_lossy_guard_fvar_headed_app_is_safe() {
    let expr = Expr::app(
        Expr::fvar(FVarId::new(1)),
        Expr::const_(Name::from_string("a"), vec![]),
    );
    assert!(
        !SmtBridge::requires_lossy_guard(&expr),
        "FVar-headed application should not require lossy guard"
    );
}

#[test]
fn test_lossy_guard_lambda_headed_app_is_lossy() {
    // (fun x => x) a — lambda-headed application
    let lam = Expr::lam(BinderInfo::Default, Expr::prop(), Expr::bvar(0));
    let expr = Expr::app(lam, Expr::const_(Name::from_string("a"), vec![]));
    assert!(
        SmtBridge::requires_lossy_guard(&expr),
        "lambda-headed application should require lossy guard"
    );
}

#[test]
fn test_lossy_guard_let_is_lossy() {
    let expr = Expr::let_named(
        Name::anon(),
        Expr::prop(),
        Expr::const_(Name::from_string("True"), vec![]),
        Expr::bvar(0),
        false,
    );
    assert!(
        SmtBridge::requires_lossy_guard(&expr),
        "Let expression should require lossy guard"
    );
}

#[test]
fn test_lossy_guard_proj_is_lossy() {
    let expr = Expr::proj(
        Name::from_string("Prod"),
        0,
        Expr::const_(Name::from_string("x"), vec![]),
    );
    assert!(
        SmtBridge::requires_lossy_guard(&expr),
        "Proj expression should require lossy guard"
    );
}

#[test]
fn test_lossy_guard_sort_is_lossy() {
    let expr = Expr::sort(Level::zero());
    assert!(
        SmtBridge::requires_lossy_guard(&expr),
        "Sort expression should require lossy guard"
    );
}

#[test]
fn test_lossy_guard_bvar_is_lossy() {
    let expr = Expr::bvar(0);
    assert!(
        SmtBridge::requires_lossy_guard(&expr),
        "BVar expression should require lossy guard"
    );
}

#[test]
fn test_lossy_guard_nat_lit_is_lossy() {
    let expr = Expr::nat_lit(42);
    assert!(
        SmtBridge::requires_lossy_guard(&expr),
        "Nat literal should require lossy guard"
    );
}

#[test]
fn test_lossy_guard_lam_is_lossy() {
    let expr = Expr::lam(BinderInfo::Default, Expr::prop(), Expr::bvar(0));
    assert!(
        SmtBridge::requires_lossy_guard(&expr),
        "Lambda expression should require lossy guard"
    );
}

#[test]
fn test_lossy_guard_pi_is_lossy() {
    let expr = Expr::pi(BinderInfo::Default, Expr::prop(), Expr::bvar(0));
    assert!(
        SmtBridge::requires_lossy_guard(&expr),
        "Pi expression should require lossy guard"
    );
}

#[test]
fn test_lossy_guard_mdata_unwraps_to_inner() {
    // MData wrapping a safe Const — should be safe after strip_mdata
    let inner = Expr::const_(Name::from_string("p"), vec![]);
    let expr = Expr::mdata(vec![], inner);
    assert!(
        !SmtBridge::requires_lossy_guard(&expr),
        "MData-wrapped Const should be safe (strip_mdata unwraps)"
    );
}

#[test]
fn test_lossy_guard_mdata_wrapping_lossy_is_lossy() {
    // MData wrapping a Let — should still be lossy
    let inner = Expr::let_named(
        Name::anon(),
        Expr::prop(),
        Expr::const_(Name::from_string("True"), vec![]),
        Expr::bvar(0),
        false,
    );
    let expr = Expr::mdata(vec![], inner);
    assert!(
        SmtBridge::requires_lossy_guard(&expr),
        "MData-wrapped Let should still be lossy"
    );
}

#[test]
fn test_lossy_guard_nested_const_app_is_safe() {
    // Multi-arg Const-headed app: f a b = App(App(f, a), b)
    // Head of the outer App is App(f, a), which itself has head f (Const).
    // get_app_fn traverses the spine to find the true head.
    let expr = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("f"), vec![]),
            Expr::const_(Name::from_string("a"), vec![]),
        ),
        Expr::const_(Name::from_string("b"), vec![]),
    );
    assert!(
        !SmtBridge::requires_lossy_guard(&expr),
        "multi-arg Const-headed application should not require lossy guard"
    );
}

// ========================================================================
// End-to-end: Atom branch records lossy for lossy atoms
// ========================================================================

#[test]
fn test_prop_to_literal_atom_with_proj_records_lossy() {
    let env = Environment::new();
    let mut bridge = SmtBridge::new(&env);

    // A Proj expression classified as Atom should trigger record_lossy_expr
    let proj_atom = Expr::proj(
        Name::from_string("Prod"),
        0,
        Expr::const_(Name::from_string("h"), vec![]),
    );

    let result = bridge.prop_to_literal(&proj_atom, true);
    assert!(result.is_ok(), "prop_to_literal should succeed for Atom");
    assert!(
        !bridge.lossy_atoms.is_empty(),
        "Proj atom should be recorded as lossy"
    );
}

#[test]
fn test_prop_to_literal_atom_with_let_records_lossy() {
    let env = Environment::new();
    let mut bridge = SmtBridge::new(&env);

    let let_atom = Expr::let_named(
        Name::anon(),
        Expr::prop(),
        Expr::const_(Name::from_string("True"), vec![]),
        Expr::bvar(0),
        false,
    );

    let result = bridge.prop_to_literal(&let_atom, true);
    assert!(result.is_ok(), "prop_to_literal should succeed for Atom");
    assert!(
        !bridge.lossy_atoms.is_empty(),
        "Let atom should be recorded as lossy"
    );
}

#[test]
fn test_prop_to_literal_atom_with_const_does_not_record_lossy() {
    let env = Environment::new();
    let mut bridge = SmtBridge::new(&env);

    let const_atom = Expr::const_(Name::from_string("P"), vec![]);

    let result = bridge.prop_to_literal(&const_atom, true);
    assert!(result.is_ok(), "prop_to_literal should succeed for Atom");
    assert!(
        bridge.lossy_atoms.is_empty(),
        "Const atom should NOT be recorded as lossy"
    );
}

#[test]
fn test_prop_to_literal_atom_with_fvar_app_does_not_record_lossy() {
    let env = Environment::new();
    let mut bridge = SmtBridge::new(&env);

    // FVar-headed application: h(a) where h is a free variable
    let fvar_app = Expr::app(
        Expr::fvar(FVarId::new(1)),
        Expr::const_(Name::from_string("a"), vec![]),
    );

    let result = bridge.prop_to_literal(&fvar_app, true);
    assert!(result.is_ok(), "prop_to_literal should succeed for Atom");
    assert!(
        bridge.lossy_atoms.is_empty(),
        "FVar-headed app atom should NOT be recorded as lossy"
    );
}

// ========================================================================
// End-to-end: Complex-headed app in translate_term records lossy
// ========================================================================

#[test]
fn test_translate_term_lambda_headed_app_records_lossy() {
    let env = Environment::new();
    let mut bridge = SmtBridge::new(&env);

    // (fun x => x) a — lambda-headed application
    let lam = Expr::lam(BinderInfo::Default, Expr::type_(), Expr::bvar(0));
    let lambda_app = Expr::app(lam, Expr::const_(Name::from_string("a"), vec![]));

    let result = bridge.translate_term(&lambda_app);
    assert!(
        result.is_ok(),
        "translate_term should succeed for lambda-headed app (lossy fallback)"
    );
    assert!(
        !bridge.lossy_atoms.is_empty(),
        "lambda-headed app should be recorded as lossy in translate_term"
    );
}

#[test]
fn test_prove_lambda_headed_app_goal_returns_unknown() {
    let env = Environment::new();
    let mut bridge = SmtBridge::new(&env);

    // Goal: (fun x => x) a = (fun x => x) a
    // This exercises: translate_term sees lambda-headed app → records lossy
    // → prove returns Unknown instead of Verified/Unverified
    let lam = Expr::lam(BinderInfo::Default, Expr::type_(), Expr::bvar(0));
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let lambda_app = Expr::app(lam, a);

    let eq = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                Expr::type_(),
            ),
            lambda_app.clone(),
        ),
        lambda_app,
    );

    let result = bridge.prove(&eq);
    match result {
        Ok(SmtVerificationResult::Unknown(reason)) => {
            assert!(
                reason.contains(
                    "lossy translation: SAT result may be spurious due to unconstrained atoms"
                ),
                "Unknown reason should preserve the SAT lossy prefix, got: {reason}"
            );
            assert!(
                reason.contains("4 lossy expressions"),
                "Unknown reason should report the lossy count, got: {reason}"
            );
            assert!(
                reason.contains("App(Lam head)"),
                "Unknown reason should summarize lambda-headed applications stably, got: {reason}"
            );
        }
        other => panic!("prove with lossy lambda-headed app should return Unknown, got: {other:?}"),
    }
}
