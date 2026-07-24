// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Value-behavior tests for ordering projection declarations.
//!
//! Tests that `Ord.compare`, `LE.le`, `LT.lt` projections applied to
//! concrete Nat instances reduce to the correct underlying operations
//! through the full chain:
//!   projection → delta-unfold → beta → Expr::proj → delta-unfold instance → Nat.op
//!
//! Unlike hetero projections (body = Proj(Class, 0, inst)), ordering projections
//! have body = App(App(Proj(Class, 0, inst), a), b) because the projection result
//! is a binary function that gets applied to the operand bvars.
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

// =============================================================================
// Ordering projection body structure tests
// =============================================================================

/// Assert that a projection body contains `Proj(class_name, 0, _)` as the
/// head of an application spine after peeling all lambda binders.
fn assert_projection_body_contains_proj(env: &Environment, proj_name: &str, class_name: &str) {
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

    // Walk through App nodes to find the head
    let mut head = &expr;
    while let ExprKind::App(f, _) = &head.kind {
        head = f;
    }

    let expected_class = Name::from_string(class_name);
    assert!(
        matches!(&head.kind, ExprKind::Proj(name, 0, _) if name == &expected_class),
        "{proj_name} body head should be Proj({class_name}, 0, _), got: {:?}",
        head.kind
    );
}

#[test]
fn test_ord_compare_projection_body_structure() {
    let mut env = Environment::new();
    env.init_ord().expect("init Ord");
    assert_projection_body_contains_proj(&env, "Ord.compare", "Ord");
}

#[test]
fn test_le_projection_body_structure() {
    let mut env = Environment::new();
    env.init_le().expect("init LE");
    assert_projection_body_contains_proj(&env, "LE.le", "LE");
}

#[test]
fn test_lt_projection_body_structure() {
    let mut env = Environment::new();
    env.init_lt().expect("init LT");
    assert_projection_body_contains_proj(&env, "LT.lt", "LT");
}

// =============================================================================
// Ordering projection lambda binder count
// =============================================================================

#[test]
fn test_ordering_projections_have_4_lambda_binders() {
    let mut env = Environment::new();
    env.init_ord().expect("init Ord");
    env.init_le().expect("init LE");
    env.init_lt().expect("init LT");

    for proj_name in ["Ord.compare", "LE.le", "LT.lt"] {
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

// =============================================================================
// Ordering projection full application reduces through instance
//
// Full application (4 args) triggers beta-reduction through all binders,
// then whnf reduces the Proj and applies the underlying function.
// =============================================================================

/// Build a fully-applied ordering projection call:
///   `<proj>.{0} Nat <inst> lhs rhs`
fn ordering_proj_nat_app(proj_name: &str, inst_name: &str, lhs: Expr, rhs: Expr) -> Expr {
    let proj = Expr::const_(Name::from_string(proj_name), vec![Level::zero()]);
    let nat_ty = nat_const();
    let inst = Expr::const_(Name::from_string(inst_name), vec![]);
    Expr::app(
        Expr::app(Expr::app(Expr::app(proj, nat_ty), inst), lhs),
        rhs,
    )
}

#[test]
fn test_ord_compare_full_app_reduces_through_instance() {
    let mut env = Environment::new();
    env.init_ord().expect("init Ord");

    let tc = TypeChecker::new(&env);

    // Ord.compare Nat instOrdNat 3 5 should reduce through:
    //   delta(Ord.compare) → beta × 4 → Proj(Ord, 0, instOrdNat) 3 5
    //   → delta(instOrdNat) → proj on Ord.mk(Nat, Nat.compare) → Nat.compare 3 5
    let expr = ordering_proj_nat_app("Ord.compare", "instOrdNat", nat(3), nat(5));
    let result = tc.whnf(&expr);

    let nat_compare_app = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Nat.compare"), vec![]),
            nat(3),
        ),
        nat(5),
    );
    assert!(
        tc.is_def_eq(&result, &nat_compare_app),
        "Ord.compare Nat instOrdNat 3 5 should reduce to Nat.compare 3 5, got: {result:?}"
    );
}

#[test]
fn test_le_full_app_reduces_through_instance() {
    let mut env = Environment::new();
    env.init_le().expect("init LE");

    let tc = TypeChecker::new(&env);

    let expr = ordering_proj_nat_app("LE.le", "instLENat", nat(2), nat(5));
    let result = tc.whnf(&expr);

    let nat_le_app = Expr::app(
        Expr::app(Expr::const_(Name::from_string("Nat.le"), vec![]), nat(2)),
        nat(5),
    );
    assert!(
        tc.is_def_eq(&result, &nat_le_app),
        "LE.le Nat instLENat 2 5 should reduce to Nat.le 2 5, got: {result:?}"
    );
}

#[test]
fn test_lt_full_app_reduces_through_instance() {
    let mut env = Environment::new();
    env.init_lt().expect("init LT");

    let tc = TypeChecker::new(&env);

    let expr = ordering_proj_nat_app("LT.lt", "instLTNat", nat(2), nat(5));
    let result = tc.whnf(&expr);

    let nat_lt_app = Expr::app(
        Expr::app(Expr::const_(Name::from_string("Nat.lt"), vec![]), nat(2)),
        nat(5),
    );
    assert!(
        tc.is_def_eq(&result, &nat_lt_app),
        "LT.lt Nat instLTNat 2 5 should reduce to Nat.lt 2 5, got: {result:?}"
    );
}

/// Regression test for #2150: is_def_eq must recognize @LE.le Nat instLENat a b
/// as definitionally equal to Nat.le a b WITHOUT pre-whnf normalization.
///
/// The lazy delta reduction loop must handle the case where LE.le unfolds to
/// Proj("LE", 0, instLENat) (a non-delta, non-const head), and the other side
/// is Nat.le (an inductive, also non-delta). The (None, None) case must try
/// projection reduction before returning DefUnknown.
#[test]
fn test_is_def_eq_le_through_instance_without_whnf() {
    let mut env = Environment::new();
    env.init_le().expect("init LE");

    let tc = TypeChecker::new(&env);

    let le_app = ordering_proj_nat_app("LE.le", "instLENat", nat(2), nat(5));
    let nat_le_app = Expr::app(
        Expr::app(Expr::const_(Name::from_string("Nat.le"), vec![]), nat(2)),
        nat(5),
    );
    assert!(
        tc.is_def_eq(&le_app, &nat_le_app),
        "@LE.le Nat instLENat 2 5 should be def-eq to Nat.le 2 5 \
         without pre-whnf (lazy delta must reduce through projection chain)"
    );
}

/// Test lazy_delta_reduction (None,None): both sides are stuck projections
/// with opaque struct arguments that WHNF cannot reduce.
///
/// When try_unfold_proj_app is called on a Proj whose struct argument is an
/// opaque axiom, whnf_core returns the expression unchanged, and
/// try_unfold_proj_app returns None. Both sides returning None causes
/// DefUnknown, which is the correct result (genuinely non-equal).
#[test]
fn test_lazy_delta_none_none_both_stuck_projections_rejects() {
    use crate::env::Declaration;
    use crate::inductive::{Constructor, InductiveDecl, InductiveType};

    let mut env = Environment::new();

    // Nat must exist for constructor type checking (#2156 validation).
    env.add_decl_unchecked(Declaration::Axiom {
        name: Name::from_string("Nat"),
        level_params: vec![],
        type_: Expr::sort(Level::succ(Level::zero())),
    });

    // Define a simple struct: `structure Wrapper where val : Nat`
    let wrapper_name = Name::from_string("Wrapper");
    let wrapper_mk = Name::from_string("Wrapper.mk");
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: wrapper_name.clone(),
            type_: Expr::type_(),
            constructors: vec![Constructor {
                name: wrapper_mk.clone(),
                type_: Expr::pi(
                    BinderInfo::Default,
                    nat_const(),
                    Expr::const_(wrapper_name.clone(), vec![]),
                ),
            }],
        }],
    })
    .expect("Wrapper inductive should add");

    // Two opaque axioms of type Wrapper — their values are unknown
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("opaque_a"),
        level_params: vec![],
        type_: Expr::const_(wrapper_name.clone(), vec![]),
    })
    .expect("opaque_a axiom");
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("opaque_b"),
        level_params: vec![],
        type_: Expr::const_(wrapper_name.clone(), vec![]),
    })
    .expect("opaque_b axiom");

    let tc = TypeChecker::new(&env);

    // Proj(Wrapper, 0, opaque_a) and Proj(Wrapper, 0, opaque_b)
    // Both are stuck: whnf can't reduce Proj on an axiom (not a constructor).
    let proj_a = Expr::proj(
        wrapper_name.clone(),
        0,
        Expr::const_(Name::from_string("opaque_a"), vec![]),
    );
    let proj_b = Expr::proj(
        wrapper_name,
        0,
        Expr::const_(Name::from_string("opaque_b"), vec![]),
    );

    // These are genuinely different — is_def_eq must return false.
    assert!(
        !tc.is_def_eq(&proj_a, &proj_b),
        "stuck projections on different opaque axioms must not be def-eq"
    );
}

/// Test lazy_delta_reduction (None,None): both sides are reducible projections.
///
/// Both @LE.le and @LT.lt unfold to Proj-headed expressions, and both can be
/// reduced through their respective instances. They should NOT be def-eq since
/// Nat.le != Nat.lt.
#[test]
fn test_lazy_delta_none_none_both_reducible_projections_different() {
    let mut env = Environment::new();
    env.init_le().expect("init LE");
    env.init_lt().expect("init LT");

    let tc = TypeChecker::new(&env);

    let le_app = ordering_proj_nat_app("LE.le", "instLENat", nat(2), nat(5));
    let lt_app = ordering_proj_nat_app("LT.lt", "instLTNat", nat(2), nat(5));

    // LE.le → Nat.le and LT.lt → Nat.lt: different underlying operations.
    assert!(
        !tc.is_def_eq(&le_app, &lt_app),
        "@LE.le ... 2 5 must not be def-eq to @LT.lt ... 2 5 \
         (Nat.le != Nat.lt)"
    );
}

/// Test lazy_delta_reduction (None,None): both sides reduce to the SAME value.
///
/// Two expressions that reach the (None,None) case should be recognized as
/// equal when both reduce to the same underlying operation.
#[test]
fn test_lazy_delta_none_none_both_reducible_same_value() {
    let mut env = Environment::new();
    env.init_le().expect("init LE");

    let tc = TypeChecker::new(&env);

    let le_app_a = ordering_proj_nat_app("LE.le", "instLENat", nat(3), nat(7));
    let le_app_b = ordering_proj_nat_app("LE.le", "instLENat", nat(3), nat(7));

    // Same expression on both sides — trivially equal, but exercises the
    // (None,None) → try_unfold_proj_app → DefEqual path.
    assert!(
        tc.is_def_eq(&le_app_a, &le_app_b),
        "identical LE.le applications should be def-eq"
    );
}
