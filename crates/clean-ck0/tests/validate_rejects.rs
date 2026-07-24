// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! The chokepoint rejects ill-formed RawExpr: open var, wrong arity,
//! out-of-range level param. Canonical levels come out of validation.

use clean_ck0::{Level, MinimalEnv, Name, RawExpr, RawLevel, Term, ValidateError};

#[test]
fn test_open_var_rejected() {
    let env = MinimalEnv::new();
    let r = Term::validate_closed(&env, &RawExpr::BVar(3));
    assert!(matches!(
        r,
        Err(ValidateError::OpenVar { index: 3, depth: 0 })
    ));
}

#[test]
fn test_open_var_under_binder_boundary() {
    // Under one λ binder, BVar(0) is bound (ok), BVar(1) is open (reject).
    let env = MinimalEnv::new();
    let bound = RawExpr::Lam(
        Default::default(),
        Box::new(RawExpr::Sort(RawLevel::Zero)),
        Box::new(RawExpr::BVar(0)),
    );
    assert!(Term::validate_closed(&env, &bound).is_ok());

    let open = RawExpr::Lam(
        Default::default(),
        Box::new(RawExpr::Sort(RawLevel::Zero)),
        Box::new(RawExpr::BVar(1)),
    );
    assert!(matches!(
        Term::validate_closed(&env, &open),
        Err(ValidateError::OpenVar { index: 1, depth: 1 })
    ));
}

#[test]
fn test_out_of_range_level_param_rejected() {
    let env = MinimalEnv::new();
    // arity 0: any Param is out of range.
    let raw = RawExpr::Sort(RawLevel::Param(0));
    assert!(matches!(
        Term::validate(&env, &raw, 0, 0),
        Err(ValidateError::LevelParam { index: 0, arity: 0 })
    ));
    // arity 1: Param(0) ok, Param(1) rejected.
    assert!(Term::validate(&env, &RawExpr::Sort(RawLevel::Param(0)), 0, 1).is_ok());
    assert!(Term::validate(&env, &RawExpr::Sort(RawLevel::Param(1)), 0, 1).is_err());
}

#[test]
fn test_validation_produces_canonical_levels() {
    // A non-canonical RawLevel (imax(_, 0)) must come out canonicalized to Zero.
    let env = MinimalEnv::new();
    let raw = RawExpr::Sort(RawLevel::IMax(
        Box::new(RawLevel::Param(0)),
        Box::new(RawLevel::Zero),
    ));
    let t = Term::validate(&env, &raw, 0, 1).expect("validates");
    match t.kind() {
        clean_ck0::term::TermKind::Sort(l) => {
            assert_eq!(*l, Level::zero(), "imax(_, 0) canonicalizes to 0");
        }
        other => panic!("expected Sort, got {other:?}"),
    }
}

#[test]
fn test_wrong_const_arity_through_chokepoint() {
    let env = MinimalEnv::new().with_const(Name::from_dotted("Foo"), 2);
    let raw = RawExpr::Const(Name::from_dotted("Foo"), vec![RawLevel::Zero]);
    assert!(Term::validate_closed(&env, &raw).is_err());
}

#[test]
fn test_recursor_name_as_const_rejected() {
    // Codex A3: a recursor/eliminator name in Const position is rejected — it
    // must be lowered to RawExpr::Elim. This holds even if the env "knows" the
    // name, so the ElimRef level-derivation kill cannot be bypassed.
    let env = MinimalEnv::new()
        .with_const(Name::from_dotted("Nat.rec"), 1)
        .with_const(Name::from_dotted("List.casesOn"), 1)
        .with_const(Name::from_dotted("Nat.brecOn"), 1);
    for n in ["Nat.rec", "List.casesOn", "Nat.brecOn"] {
        let raw = RawExpr::Const(Name::from_dotted(n), vec![RawLevel::Zero]);
        assert!(
            matches!(
                Term::validate_closed(&env, &raw),
                Err(ValidateError::RecursorAsConst { .. })
            ),
            "{n} must be rejected as a plain Const"
        );
    }
    // An ordinary constant whose final component is not a reserved eliminator
    // suffix validates normally (with matching arity).
    let env = env.with_const(Name::from_dotted("Nat.add"), 0);
    let ok = RawExpr::Const(Name::from_dotted("Nat.add"), vec![]);
    assert!(Term::validate_closed(&env, &ok).is_ok());
}

#[test]
fn test_nested_open_var_in_app_rejected() {
    // App(λx.x, BVar(0)) — the argument BVar(0) is open at depth 0.
    let env = MinimalEnv::new();
    let raw = RawExpr::App(
        Box::new(RawExpr::Lam(
            Default::default(),
            Box::new(RawExpr::Sort(RawLevel::Zero)),
            Box::new(RawExpr::BVar(0)),
        )),
        Box::new(RawExpr::BVar(0)),
    );
    assert!(Term::validate_closed(&env, &raw).is_err());
}
