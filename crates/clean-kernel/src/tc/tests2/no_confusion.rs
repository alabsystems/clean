// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for noConfusionType and noConfusion.
//!
//! Both noConfusionType and noConfusion are stored as **reducible definitions**
//! (constants with values), not as recursors. They reduce via delta/beta/iota.
//! noConfusion's value body uses Eq.ndrec and T.casesOn (#2162).

use super::support::make_nat_env_with_eq;
use super::*;
use crate::inductive::{Constructor, InductiveDecl, InductiveType};

#[test]
fn test_no_confusion_type_exists() {
    // noConfusionType is a definition (constant), not a recursor
    let env = make_nat_env_with_eq();

    let nct = env
        .get_const(&Name::from_string("Nat.noConfusionType"))
        .expect("Nat.noConfusionType should exist as a constant");

    // It should have a value (it's a definition, not an opaque constant)
    assert!(
        nct.value.is_some(),
        "Nat.noConfusionType should have a value"
    );

    // It should NOT be in the recursor table
    assert!(
        env.get_recursor(&Name::from_string("Nat.noConfusionType"))
            .is_none(),
        "Nat.noConfusionType should not be a recursor"
    );
}

#[test]
fn test_no_confusion_exists() {
    // #2162: noConfusion is a reducible definition (like Lean 4), not a recursor
    let env = make_nat_env_with_eq();

    let no_conf = env
        .get_const(&Name::from_string("Nat.noConfusion"))
        .expect("Nat.noConfusion should exist as a constant");

    assert!(
        no_conf.value.is_some(),
        "Nat.noConfusion should have a value (definition body with Eq.ndrec + casesOn)"
    );

    assert!(no_conf.is_reducible, "Nat.noConfusion should be reducible");

    // Should NOT be in the recursor table
    assert!(
        env.get_recursor(&Name::from_string("Nat.noConfusion"))
            .is_none(),
        "Nat.noConfusion should not be a recursor (#2162)"
    );
}

#[test]
fn test_no_confusion_type_structure() {
    // Nat.noConfusionType : Sort u → Nat → Nat → Sort u
    let env = make_nat_env_with_eq();

    let nct = env
        .get_const(&Name::from_string("Nat.noConfusionType"))
        .expect("Nat.noConfusionType should exist");

    let ty = &nct.type_;

    // First arg: Sort u (the result type parameter P)
    if let ExprKind::Pi(_, domain, _) = &ty.kind {
        if let ExprKind::Sort(_) = &domain.as_ref().kind {
            // OK - first arg is Sort u
        } else {
            panic!("Expected first arg to be Sort u, got: {domain:?}");
        }
    } else {
        panic!("Expected Pi type, got: {ty:?}");
    }
}

#[test]
fn test_no_confusion_for_enum() {
    // Verify noConfusion is generated for enum types (no fields)
    let mut env = Environment::new();
    env.init_punit()
        .expect("PUnit is required by noConfusionType");
    env.init_eq()
        .expect("Eq is required before noConfusion can be authoritative");

    let bool_ty = Name::from_string("MyBool");
    let bool_ref = Expr::const_(bool_ty.clone(), vec![]);

    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: bool_ty.clone(),
            type_: Expr::type_(),
            constructors: vec![
                Constructor {
                    name: Name::from_string("MyBool.false"),
                    type_: bool_ref.clone(),
                },
                Constructor {
                    name: Name::from_string("MyBool.true"),
                    type_: bool_ref.clone(),
                },
            ],
        }],
    };

    env.add_inductive(decl).unwrap();

    // noConfusionType is a definition
    assert!(
        env.get_const(&Name::from_string("MyBool.noConfusionType"))
            .is_some(),
        "MyBool.noConfusionType should exist as a constant"
    );

    // #2162: noConfusion is a definition, not a recursor
    let no_conf = env
        .get_const(&Name::from_string("MyBool.noConfusion"))
        .expect("MyBool.noConfusion should exist as a constant");
    assert!(
        no_conf.value.is_some(),
        "MyBool.noConfusion should have a value (definition)"
    );
}

#[test]
fn test_no_confusion_for_parametric_type() {
    // Verify noConfusion is generated for parametric types
    let mut env = Environment::new();
    // The v4.30 heterogeneous noConfusion of a parameterized inductive
    // references HEq/HEq.refl/eq_of_heq (per-dependent-param + major premises),
    // exactly as it is available in the real prelude (init_heq runs right after
    // init_eq). Seed it here so generation exercises the real path rather than
    // being skipped (build_no_confusion_*_hetero's require_heq guard).
    env.init_heq().expect("init_heq (auto-seeds init_eq)");

    let u = Name::from_string("u");
    let opt = Name::from_string("MyOption");

    // MyOption : Type u → Type u
    let opt_type = Expr::pi(
        BinderInfo::Default,
        Expr::from_kind(ExprKind::Sort(Level::succ(Level::param(u.clone())))),
        Expr::from_kind(ExprKind::Sort(Level::succ(Level::param(u.clone())))),
    );

    // MyOption A
    let opt_a = Expr::app(
        Expr::const_(opt.clone(), vec![Level::param(u.clone())]),
        Expr::bvar(0),
    );

    // none : (A : Type u) → MyOption A
    let none_type = Expr::pi(
        BinderInfo::Default,
        Expr::from_kind(ExprKind::Sort(Level::succ(Level::param(u.clone())))),
        opt_a.clone(),
    );

    // some : (A : Type u) → A → MyOption A
    let some_type = Expr::pi(
        BinderInfo::Default,
        Expr::from_kind(ExprKind::Sort(Level::succ(Level::param(u.clone())))),
        Expr::pi(
            BinderInfo::Default,
            Expr::bvar(0), // A
            Expr::app(
                Expr::const_(opt.clone(), vec![Level::param(u.clone())]),
                Expr::bvar(1), // A (at depth 1)
            ),
        ),
    );

    let decl = InductiveDecl {
        level_params: vec![u.clone()],
        num_params: 1,
        types: vec![InductiveType {
            name: opt.clone(),
            type_: opt_type,
            constructors: vec![
                Constructor {
                    name: Name::from_string("MyOption.none"),
                    type_: none_type,
                },
                Constructor {
                    name: Name::from_string("MyOption.some"),
                    type_: some_type,
                },
            ],
        }],
    };

    env.add_inductive(decl).unwrap();

    // noConfusionType is a definition
    let nct = env
        .get_const(&Name::from_string("MyOption.noConfusionType"))
        .expect("MyOption.noConfusionType should exist");
    nct.value
        .as_ref()
        .expect("noConfusionType should have a value");

    // #2162: noConfusion is a definition, not a recursor
    let no_conf = env
        .get_const(&Name::from_string("MyOption.noConfusion"))
        .expect("MyOption.noConfusion should exist as a constant");
    assert!(
        no_conf.value.is_some(),
        "MyOption.noConfusion should have a value (definition)"
    );
}

// =============================================================================
// Regression tests for #1788: noConfusionType reduction behavior
// =============================================================================

/// Test: Nat.noConfusionType Prop (succ n) (succ m) reduces to (n = m → Prop) → Prop
///
/// This is the key same-constructor diagonal case. The result should contain
/// an equality arrow for each field, ending with P, wrapped in another → P.
#[test]
fn test_no_confusion_type_succ_succ_reduces_to_eq_arrow() {
    let env = make_nat_env_with_eq();
    let tc = TypeChecker::new(&env);

    // Build: Nat.noConfusionType.{0} Prop (Nat.succ n) (Nat.succ m)
    // where n and m are free variables represented as BVar under a lambda context.
    //
    // We use closed expressions: Nat.succ Nat.zero for both n and m,
    // then check the WHNF reduction structure.
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
    let succ_zero = Expr::app(succ.clone(), zero.clone());

    // Nat.noConfusionType.{1} (Sort 0 = Prop) (succ zero) (succ zero)
    let nct_const = Expr::const_(
        Name::from_string("Nat.noConfusionType"),
        vec![Level::succ(Level::zero())], // u = 1 so Sort u = Type 0
    );

    let app = Expr::app(
        Expr::app(
            Expr::app(nct_const, Expr::type_()), // P = Type 0
            succ_zero.clone(),                   // a = succ zero
        ),
        succ_zero, // b = succ zero
    );

    // WHNF should reduce to something of the form: (Eq Nat zero zero → Type 0) → Type 0
    let result = tc.whnf(&app);

    // The result should be a Pi type (outermost arrow):
    //   (eq_chain → P) → P
    // where eq_chain = (Eq Nat zero zero → Type 0)
    match &result.kind {
        ExprKind::Pi(_, domain, codomain) => {
            // domain should be: Eq Nat zero zero → Type 0
            // (a Pi with Eq as domain and Type 0 as codomain)
            match &domain.as_ref().kind {
                ExprKind::Pi(_, eq_domain, inner_codomain) => {
                    // eq_domain should be an Eq application
                    assert!(
                        matches_eq_app(eq_domain),
                        "Expected Eq application in domain, got: {eq_domain:?}"
                    );
                    // inner_codomain should be Type 0 (the P)
                    assert!(
                        matches!(&inner_codomain.as_ref().kind, ExprKind::Sort(_)),
                        "Expected Sort in inner codomain, got: {inner_codomain:?}"
                    );
                }
                _ => panic!(
                    "Expected Pi type (eq → P) in outer domain, got: {:?}",
                    domain
                ),
            }
            // codomain should be Type 0 (P, shifted by 1 due to the Pi binder)
            assert!(
                matches!(&codomain.as_ref().kind, ExprKind::Sort(_)),
                "Expected Sort in codomain, got: {codomain:?}"
            );
        }
        _ => panic!("Expected Pi type for same-constructor noConfusionType, got: {result:?}"),
    }

    // Also verify the result is well-typed
    let result_ty = tc
        .infer_type(&result)
        .expect("Reduced noConfusionType should be well-typed");
    assert!(
        matches!(&result_ty.kind, ExprKind::Sort(_)),
        "Type of reduced noConfusionType should be a Sort, got: {result_ty:?}"
    );
}

/// Test: Nat.noConfusionType Prop zero (succ n) reduces to Prop
///
/// Different-constructor case: should return just P.
#[test]
fn test_no_confusion_type_zero_succ_reduces_to_p() {
    let env = make_nat_env_with_eq();
    let tc = TypeChecker::new(&env);

    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
    let succ_zero = Expr::app(succ, zero.clone());

    // Nat.noConfusionType.{1} (Type 0) zero (succ zero)
    let nct_const = Expr::const_(
        Name::from_string("Nat.noConfusionType"),
        vec![Level::succ(Level::zero())],
    );

    let app = Expr::app(
        Expr::app(
            Expr::app(nct_const, Expr::type_()), // P = Type 0
            zero,                                // a = zero
        ),
        succ_zero, // b = succ zero
    );

    let result = tc.whnf(&app);

    // Different constructor → result should be P = Type 0
    assert!(
        matches!(&result.kind, ExprKind::Sort(_)),
        "Expected Sort (P) for different-constructor case, got: {result:?}"
    );
}

/// Test: Nat.noConfusionType Prop zero zero reduces to (P → P)
///
/// Same constructor, zero fields: should return P → P.
#[test]
fn test_no_confusion_type_zero_zero_reduces_to_p_arrow_p() {
    let env = make_nat_env_with_eq();
    let tc = TypeChecker::new(&env);

    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);

    // Nat.noConfusionType.{1} (Type 0) zero zero
    let nct_const = Expr::const_(
        Name::from_string("Nat.noConfusionType"),
        vec![Level::succ(Level::zero())],
    );

    let app = Expr::app(
        Expr::app(
            Expr::app(nct_const, Expr::type_()), // P = Type 0
            zero.clone(),                        // a = zero
        ),
        zero, // b = zero
    );

    let result = tc.whnf(&app);

    // Same constructor, 0 fields → result should be P → P
    match &result.kind {
        ExprKind::Pi(_, domain, codomain) => {
            // domain = P = Type 0
            assert!(
                matches!(&domain.as_ref().kind, ExprKind::Sort(_)),
                "Expected Sort in domain (P → P), got: {domain:?}"
            );
            // codomain = P = Type 0
            assert!(
                matches!(&codomain.as_ref().kind, ExprKind::Sort(_)),
                "Expected Sort in codomain (P → P), got: {codomain:?}"
            );
        }
        _ => panic!("Expected Pi type (P → P) for zero/zero case, got: {result:?}"),
    }
}

/// Test: Nat.noConfusionType Prop (succ zero) zero reduces to P (different ctors)
#[test]
fn test_no_confusion_type_succ_zero_reduces_to_p() {
    let env = make_nat_env_with_eq();
    let tc = TypeChecker::new(&env);

    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
    let succ_zero = Expr::app(succ, zero.clone());

    // Nat.noConfusionType.{1} (Type 0) (succ zero) zero
    let nct_const = Expr::const_(
        Name::from_string("Nat.noConfusionType"),
        vec![Level::succ(Level::zero())],
    );

    let app = Expr::app(
        Expr::app(
            Expr::app(nct_const, Expr::type_()), // P = Type 0
            succ_zero,                           // a = succ zero
        ),
        zero, // b = zero
    );

    let result = tc.whnf(&app);

    // Different constructor → result should be P = Type 0
    assert!(
        matches!(&result.kind, ExprKind::Sort(_)),
        "Expected Sort (P) for succ/zero case, got: {result:?}"
    );
}

/// Helper: assert a definition's value typechecks against its declared type.
fn assert_def_typechecks(env: &Environment, name: &str) {
    let tc = TypeChecker::new(env);
    let c = env
        .get_const(&Name::from_string(name))
        .unwrap_or_else(|| panic!("{name} missing"));
    let value = c
        .value
        .as_ref()
        .unwrap_or_else(|| panic!("{name} has no value"));
    tc.check_type(value, &c.type_)
        .unwrap_or_else(|e| panic!("{name} value failed type check: {e:?}"));
}

#[test]
fn test_no_confusion_type_value_typechecks_def() {
    let env = make_nat_env_with_eq();
    assert_def_typechecks(&env, "Nat.noConfusionType");
}

/// noConfusion value typechecks (#2162)
#[test]
fn test_no_confusion_value_typechecks() {
    let env = make_nat_env_with_eq();
    assert_def_typechecks(&env, "Nat.noConfusion");
}

/// Helper: check if an expression is an Eq application (Eq _ _ _).
fn matches_eq_app(e: &Expr) -> bool {
    // Eq is applied to 3 args: Eq.{u} α a b
    // App(App(App(Const(Eq, [u]), α), a), b)
    if let ExprKind::App(f, _b) = &e.kind {
        if let ExprKind::App(f2, _a) = &f.as_ref().kind {
            if let ExprKind::App(f3, _alpha) = &f2.as_ref().kind {
                if let ExprKind::Const(name, _) = &f3.as_ref().kind {
                    return name.to_string() == "Eq";
                }
            }
        }
    }
    false
}
