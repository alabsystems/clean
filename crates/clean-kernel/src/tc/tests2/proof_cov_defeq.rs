// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Proof coverage tests — definitional equality structural paths.
//!
//! Covers:
//! - `is_def_eq_offset` — structural Nat successor peeling
//! - `is_def_eq_unit_like` — unit-like type equality
//! - `is_structure_like` — structure-like type classification
//! - `is_def_eq_binding_impl` — Pi/Lam binder comparison via FVar opening

use super::*;

// ===== is_def_eq_offset tests =====
// is_def_eq_offset (tc/mod.rs:4028) implements structural Nat successor peeling.
// It handles: Nat.zero =?= Nat.zero → true, Nat.succ(a) =?= Nat.succ(b) → a =?= b.
// Previously had zero direct tests.

/// Test is_def_eq_offset: two Nat.zero constants are equal.
#[test]
fn test_is_def_eq_offset_zero_zero() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    let zero1 = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let zero2 = Expr::const_(Name::from_string("Nat.zero"), vec![]);

    // is_def_eq_offset should return Some(true) for zero =?= zero
    let result = tc.is_def_eq_offset(&zero1, &zero2);
    assert_eq!(
        result,
        Some(true),
        "Nat.zero =?= Nat.zero should be Some(true)"
    );
}

/// Test is_def_eq_offset: Nat.zero vs Nat.succ should return None (cannot determine).
#[test]
fn test_is_def_eq_offset_zero_vs_succ() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let succ_zero = Expr::app(
        Expr::const_(Name::from_string("Nat.succ"), vec![]),
        Expr::const_(Name::from_string("Nat.zero"), vec![]),
    );

    // Zero vs Succ: cannot be handled by offset alone, returns None
    let result = tc.is_def_eq_offset(&zero, &succ_zero);
    assert_eq!(
        result, None,
        "Nat.zero =?= Nat.succ(Nat.zero) should be None"
    );
}

/// Test is_def_eq_offset: Nat.succ(Nat.zero) =?= Nat.succ(Nat.zero) peels to zero =?= zero.
#[test]
fn test_is_def_eq_offset_succ_succ_equal() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    let succ = |e: Expr| Expr::app(Expr::const_(Name::from_string("Nat.succ"), vec![]), e);
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);

    let s1 = succ(zero.clone());
    let s2 = succ(zero.clone());

    let result = tc.is_def_eq_offset(&s1, &s2);
    assert_eq!(
        result,
        Some(true),
        "Nat.succ(zero) =?= Nat.succ(zero) should peel to Some(true)"
    );
}

/// Test is_def_eq_offset: Nat literal 0 is recognized as zero.
#[test]
fn test_is_def_eq_offset_literal_zero() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    let lit_zero = Expr::nat_lit(0);
    let const_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);

    // Both are "zero" per is_nat_zero_expr
    let result = tc.is_def_eq_offset(&lit_zero, &const_zero);
    assert_eq!(
        result,
        Some(true),
        "Nat.lit(0) =?= Nat.zero should be Some(true)"
    );
}

/// Test is_def_eq_offset: Nat literals use successor peeling via is_nat_succ_expr.
#[test]
fn test_is_def_eq_offset_literal_succ_peeling() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    let lit_3 = Expr::nat_lit(3);
    let succ_lit_2 = Expr::app(
        Expr::const_(Name::from_string("Nat.succ"), vec![]),
        Expr::nat_lit(2),
    );

    // Nat.lit(3) peels to Nat.lit(2), Nat.succ(Nat.lit(2)) peels to Nat.lit(2)
    // So they should match via recursive is_def_eq_core
    let result = tc.is_def_eq_offset(&lit_3, &succ_lit_2);
    assert_eq!(
        result,
        Some(true),
        "Nat.lit(3) =?= Nat.succ(2) should peel to equal"
    );
}

/// Test is_def_eq_offset: non-Nat expressions return None.
#[test]
fn test_is_def_eq_offset_non_nat_returns_none() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    let prop = Expr::prop();
    let type_ = Expr::type_();

    let result = tc.is_def_eq_offset(&prop, &type_);
    assert_eq!(result, None, "Non-Nat expressions should return None");
}

// ===== is_def_eq_unit_like tests =====
// is_def_eq_unit_like (tc/mod.rs:3718) makes two values of a unit-like type
// (single constructor, zero fields) definitionally equal.
// Previously had zero direct tests.

/// Test is_def_eq_unit_like: two distinct constants of a unit-like type are equal.
#[test]
fn test_is_def_eq_unit_like_basic() {
    use crate::env::Declaration;
    use crate::inductive::{Constructor, InductiveDecl, InductiveType};

    let mut env = Environment::new();

    // Define a unit-like type: inductive Unit : Type where | star : Unit
    let unit_name = Name::from_string("Unit");
    let unit_ref = Expr::const_(unit_name.clone(), vec![]);

    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: unit_name.clone(),
            type_: Expr::type_(),
            constructors: vec![Constructor {
                name: Name::from_string("Unit.star"),
                type_: unit_ref.clone(),
            }],
        }],
    })
    .expect("env setup: add Unit inductive type");

    // Add two distinct axioms of type Unit
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("u1"),
        level_params: vec![],
        type_: unit_ref.clone(),
    })
    .expect("env setup: add axiom u1");
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("u2"),
        level_params: vec![],
        type_: unit_ref.clone(),
    })
    .expect("env setup: add axiom u2");

    let tc = TypeChecker::new(&env);

    let u1 = Expr::const_(Name::from_string("u1"), vec![]);
    let u2 = Expr::const_(Name::from_string("u2"), vec![]);

    // Two values of a unit-like type should be definitionally equal
    assert!(
        tc.is_def_eq(&u1, &u2),
        "Two values of a unit type should be definitionally equal"
    );
}

/// Test is_def_eq_unit_like: a type with fields is NOT unit-like.
#[test]
fn test_is_def_eq_unit_like_not_unit_with_fields() {
    use crate::env::Declaration;
    use crate::inductive::{Constructor, InductiveDecl, InductiveType};

    let mut env = Environment::new();

    // Define a type with one constructor that has a field:
    // inductive Wrap : Type where | mk : Prop → Wrap
    let wrap_name = Name::from_string("Wrap");
    let wrap_ref = Expr::const_(wrap_name.clone(), vec![]);

    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: wrap_name.clone(),
            type_: Expr::type_(),
            constructors: vec![Constructor {
                name: Name::from_string("Wrap.mk"),
                type_: Expr::arrow(Expr::prop(), wrap_ref.clone()),
            }],
        }],
    })
    .expect("env setup: add Wrap inductive type");

    // Add two axioms of type Wrap
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("w1"),
        level_params: vec![],
        type_: wrap_ref.clone(),
    })
    .expect("env setup: add axiom w1");
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("w2"),
        level_params: vec![],
        type_: wrap_ref.clone(),
    })
    .expect("env setup: add axiom w2");

    let tc = TypeChecker::new(&env);
    let w1 = Expr::const_(Name::from_string("w1"), vec![]);
    let w2 = Expr::const_(Name::from_string("w2"), vec![]);

    // Two values of a non-unit type should NOT be definitionally equal
    assert!(
        !tc.is_def_eq(&w1, &w2),
        "Two values of a type with fields should NOT be def_eq via unit_like"
    );
}

/// Test is_structure_like: correct identification of structure-like types.
#[test]
fn test_is_structure_like_classification() {
    use crate::inductive::{Constructor, InductiveDecl, InductiveType};

    let mut env = Environment::new();
    env.init_nat().expect("init_nat should succeed");

    let nat = Expr::const_(Name::from_string("Nat"), vec![]);

    // Structure-like: single constructor, no indices, not recursive
    let pair_name = Name::from_string("Pair");
    let pair_ref = Expr::const_(pair_name.clone(), vec![]);
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: pair_name.clone(),
            type_: Expr::type_(),
            constructors: vec![Constructor {
                name: Name::from_string("Pair.mk"),
                type_: Expr::pi(
                    BinderInfo::Default,
                    nat.clone(),
                    Expr::pi(BinderInfo::Default, nat.clone(), pair_ref.clone()),
                ),
            }],
        }],
    })
    .expect("env setup: add Pair inductive type");

    let tc = TypeChecker::new(&env);

    // Pair is structure-like (single ctor, 0 indices, not recursive)
    assert!(
        tc.is_structure_like(&pair_name),
        "Pair should be structure-like"
    );

    // Nat is NOT structure-like (it's recursive: Nat.succ takes Nat)
    let nat_name = Name::from_string("Nat");
    assert!(
        !tc.is_structure_like(&nat_name),
        "Nat should NOT be structure-like (it's recursive)"
    );

    // Non-existent name is NOT structure-like
    let fake = Name::from_string("Fake");
    assert!(
        !tc.is_structure_like(&fake),
        "Non-existent type should not be structure-like"
    );
}

// ===== is_def_eq_binding_impl tests =====
// is_def_eq_binding_impl (tc/mod.rs:4790) compares Pi/Lam binders by opening
// bodies with a fresh FVar. Previously had zero direct tests.

/// Test is_def_eq_binding_impl: structurally identical Pi types.
/// In de Bruijn representation, alpha-equivalence IS structural identity,
/// so Π (x : Type), x and Π (y : Type), y are the same expression: Pi(Default, Type, BVar(0)).
#[test]
fn test_is_def_eq_binding_identical_pi() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    let pi1 = Expr::pi(BinderInfo::Default, Expr::type_(), Expr::bvar(0));
    let pi2 = Expr::pi(BinderInfo::Default, Expr::type_(), Expr::bvar(0));

    assert!(
        tc.is_def_eq(&pi1, &pi2),
        "Structurally identical Pi types should be def_eq"
    );
}

/// Test is_def_eq_binding_impl: nested binders exercise the FVar substitution path.
/// Π (A : Type), Π (x : A), A  vs  Π (B : Type), Π (y : B), B
/// These are structurally identical in de Bruijn (both: Pi(Type, Pi(BVar(0), BVar(1)))),
/// but the comparison still exercises is_def_eq_binding_impl's FVar instantiation
/// for the inner binder's body because BVar(0) in the domain is not closed.
#[test]
fn test_is_def_eq_binding_nested_binders() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    // Π (A : Type), Π (x : A), A = Pi(Default, Type, Pi(Default, BVar(0), BVar(1)))
    let pi1 = Expr::pi(
        BinderInfo::Default,
        Expr::type_(),
        Expr::pi(BinderInfo::Default, Expr::bvar(0), Expr::bvar(1)),
    );
    let pi2 = Expr::pi(
        BinderInfo::Default,
        Expr::type_(),
        Expr::pi(BinderInfo::Default, Expr::bvar(0), Expr::bvar(1)),
    );

    assert!(
        tc.is_def_eq(&pi1, &pi2),
        "Nested binders with open bodies should be def_eq (exercises FVar instantiation)"
    );

    // Negative: Π (A : Type), Π (x : A), A  vs  Π (A : Type), Π (x : A), x
    // BVar(1) vs BVar(0) in body — these refer to different binders
    let pi3 = Expr::pi(
        BinderInfo::Default,
        Expr::type_(),
        Expr::pi(BinderInfo::Default, Expr::bvar(0), Expr::bvar(0)),
    );

    assert!(
        !tc.is_def_eq(&pi1, &pi3),
        "Pi types with different body references should NOT be def_eq"
    );
}

/// Test is_def_eq_binding_impl: closed bodies fast path.
/// When neither body has loose BVars, no fresh FVar is needed.
#[test]
fn test_is_def_eq_binding_closed_bodies() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    // Π (_ : Type), Prop — body is Prop (closed, no BVar references)
    let pi1 = Expr::pi(BinderInfo::Default, Expr::type_(), Expr::prop());
    let pi2 = Expr::pi(BinderInfo::Default, Expr::type_(), Expr::prop());

    // This exercises the closed-body fast path (line 4804)
    assert!(
        tc.is_def_eq(&pi1, &pi2),
        "Closed-body Pi types should be def_eq via fast path"
    );
}

/// Test is_def_eq_binding_impl: different bodies are not equal.
#[test]
fn test_is_def_eq_binding_different_bodies() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    // Π (x : Type), x vs Π (x : Type), Prop
    let pi1 = Expr::pi(BinderInfo::Default, Expr::type_(), Expr::bvar(0));
    let pi2 = Expr::pi(BinderInfo::Default, Expr::type_(), Expr::prop());

    assert!(
        !tc.is_def_eq(&pi1, &pi2),
        "Pi types with different bodies should NOT be def_eq"
    );
}

/// Test is_def_eq_binding_impl: different domains are not equal.
#[test]
fn test_is_def_eq_binding_different_domains() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    // Π (x : Type), x vs Π (x : Prop), x
    let pi1 = Expr::pi(BinderInfo::Default, Expr::type_(), Expr::bvar(0));
    let pi2 = Expr::pi(BinderInfo::Default, Expr::prop(), Expr::bvar(0));

    assert!(
        !tc.is_def_eq(&pi1, &pi2),
        "Pi types with different domains should NOT be def_eq"
    );
}
