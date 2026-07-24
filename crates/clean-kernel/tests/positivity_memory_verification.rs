// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Memory verification tests for the positivity checker.
//!
//! These tests verify the #2135 mutual positivity fix against Lean 4's C++
//! kernel and document the #2147 whnf gap.
//!
//! Part of #2135, Part of #2147

use clean_kernel::expr::Expr;
use clean_kernel::inductive::{
    check_positivity, validate_inductive, Constructor, InductiveDecl, InductiveError, InductiveType,
};
use clean_kernel::Name;

/// Mutual inductive with sibling in positive (codomain) position of a
/// higher-order constructor argument is valid.
///
/// A.mk : (Nat → B) → A should be accepted because B appears to the RIGHT
/// of the inner arrow (positive position). This exercises the Pi codomain
/// branch in check_strictly_positive_impl.
#[test]
fn test_positivity_mutual_codomain_positive() {
    let (a, b) = (Name::from_string("A"), Name::from_string("B"));
    let (a_ref, b_ref) = (
        Expr::const_(a.clone(), vec![]),
        Expr::const_(b.clone(), vec![]),
    );
    let nat_ref = Expr::const_(Name::from_string("Nat"), vec![]);
    // A.mk : (Nat → B) → A — B in codomain of inner arrow = positive
    let a_mk = Expr::arrow(Expr::arrow(nat_ref, b_ref.clone()), a_ref.clone());
    // B.mk : B (nullary)
    let b_mk = b_ref.clone();
    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![
            InductiveType {
                name: a.clone(),
                type_: Expr::type_(),
                constructors: vec![Constructor {
                    name: Name::from_string("A.mk"),
                    type_: a_mk,
                }],
            },
            InductiveType {
                name: b.clone(),
                type_: Expr::type_(),
                constructors: vec![Constructor {
                    name: Name::from_string("B.mk"),
                    type_: b_mk,
                }],
            },
        ],
    };
    validate_inductive(&decl)
        .expect("B in positive (codomain) position of inner arrow should pass");
}

/// Lean 4 calls whnf before positivity checking (inductive.cpp:394).
/// clean does NOT — positivity is checked on raw expression structure.
///
/// A Let binding that hides a negative occurrence will not be caught:
///   let T := (Foo → Nat) in (T → Foo) unfolds to ((Foo → Nat) → Foo)
///   which has Foo in negative position. Without whnf, the Let expression
///   hits the `_ =>` catch-all in `check_positivity_in_ctor_type_impl`
///   (inductive.rs:320-323) which treats all non-Pi expressions as the
///   return type and returns Ok — the body is never examined.
///
/// This test documents the gap for tracking purposes. When whnf is added
/// to check_positivity_in_ctor_type_impl, this test should be inverted
/// (change expect to expect_err).
#[test]
fn test_positivity_let_hides_negative_occurrence_gap() {
    let foo = Name::from_string("Foo");
    let foo_ref = Expr::const_(foo.clone(), vec![]);
    let nat_ref = Expr::const_(Name::from_string("Nat"), vec![]);

    // T := (Foo → Nat)
    let t_def = Expr::arrow(foo_ref.clone(), nat_ref.clone());
    let t_ref = Expr::bvar(0); // de Bruijn index 0 refers to the Let binding

    // Ctor type: let T := (Foo → Nat) in (T → Foo)
    // After substitution this is ((Foo → Nat) → Foo) which has Foo in
    // the domain of an inner arrow (negative). Without whnf, the Let
    // hits the catch-all in check_positivity_in_ctor_type_impl:320
    // which returns Ok(()) — the body is never even examined.
    let ctor_type = Expr::let_named(
        Name::anon(),
        Expr::type_(), // type annotation: (Foo → Nat) is a Type
        t_def,
        Expr::arrow(t_ref, foo_ref.clone()),
        false,
    );

    // Without whnf, this PASSES despite the hidden negative occurrence.
    // This documents the gap vs Lean 4 (inductive.cpp:394 calls whnf first).
    check_positivity(&foo, &ctor_type, 0, &[&foo])
        .expect("Without whnf, Let-hidden negative occurrence is not detected (known gap, #2147)");
}

/// Verify that the #2135 fix correctly rejects mutual inductives where
/// a sibling type appears in negative position (domain of inner arrow).
///
/// This is a regression test for the fix validated against Lean 4's
/// check_positivity (inductive.cpp:393-409) which uses has_ind_occ to
/// check ALL mutual type names simultaneously.
#[test]
fn test_positivity_mutual_nested_negative_in_domain() {
    let (a, b) = (Name::from_string("A"), Name::from_string("B"));
    let (a_ref, b_ref) = (
        Expr::const_(a.clone(), vec![]),
        Expr::const_(b.clone(), vec![]),
    );
    let nat_ref = Expr::const_(Name::from_string("Nat"), vec![]);

    // A.mk : ((B → Nat) → Nat) → A
    // B appears in a doubly-nested negative position: the inner (B → Nat) puts
    // B on the left side of an arrow within a domain that itself is on the left
    // of the outer arrow. This must be rejected.
    let inner = Expr::arrow(b_ref.clone(), nat_ref.clone());
    let outer = Expr::arrow(inner, nat_ref);
    let a_mk = Expr::arrow(outer, a_ref.clone());
    let b_mk = b_ref.clone(); // B.mk : B

    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![
            InductiveType {
                name: a.clone(),
                type_: Expr::type_(),
                constructors: vec![Constructor {
                    name: Name::from_string("A.mk"),
                    type_: a_mk,
                }],
            },
            InductiveType {
                name: b.clone(),
                type_: Expr::type_(),
                constructors: vec![Constructor {
                    name: Name::from_string("B.mk"),
                    type_: b_mk,
                }],
            },
        ],
    };
    let result = validate_inductive(&decl);
    assert!(
        matches!(result, Err(InductiveError::NonPositive(..))),
        "B in doubly-nested negative position must be rejected as NonPositive, got: {:?}",
        result
    );
}
