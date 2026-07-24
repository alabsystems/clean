// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Proof coverage tests — inductive positivity checking.
//!
//! `check_positivity` (inductive.rs:270) is soundness-critical:
//! if it fails to reject non-positive occurrences, you can construct `False`.
//! Previously had zero direct test coverage.

use clean_kernel::expr::Expr;
use clean_kernel::inductive::{
    check_positivity, validate_inductive, Constructor, InductiveDecl, InductiveType,
};
use clean_kernel::name::Name;
use clean_kernel::InductiveError;

/// Helper: single-name positivity check for non-mutual tests.
fn check_pos(name: &Name, expr: &Expr, param_count: u32) -> Result<(), InductiveError> {
    check_positivity(name, expr, param_count, &[name])
}

/// Positive test: constructor type `Nat → T` has T only in positive position.
#[test]
fn test_positivity_simple_positive() {
    let t_name = Name::from_string("T");
    let t_ref = Expr::const_(t_name.clone(), vec![]);
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);

    // T appears only in the return position (codomain).
    let ctor_type = Expr::arrow(nat, t_ref);

    assert!(
        check_pos(&t_name, &ctor_type, 0).is_ok(),
        "T in return position should be strictly positive"
    );
}

/// Negative: `(T → Prop) → T` has T in negative position.
#[test]
fn test_positivity_negative_occurrence() {
    let t_name = Name::from_string("T");
    let t_ref = Expr::const_(t_name.clone(), vec![]);

    let domain = Expr::arrow(t_ref.clone(), Expr::prop());
    let ctor_type = Expr::arrow(domain, t_ref);

    let result = check_pos(&t_name, &ctor_type, 0);
    assert!(
        result.is_err(),
        "(T → Prop) → T should be rejected as non-positive"
    );
    assert!(
        matches!(result, Err(InductiveError::NonPositive(_, _))),
        "Error should be NonPositive variant"
    );
}

/// Direct arrow `T → T` is positive: T as Const in domain is fine,
/// only Pi-within-domain triggers negative check.
#[test]
fn test_positivity_direct_arrow_to_self() {
    let t_name = Name::from_string("T");
    let t_ref = Expr::const_(t_name.clone(), vec![]);

    let ctor_type = Expr::arrow(t_ref.clone(), t_ref);

    assert!(
        check_pos(&t_name, &ctor_type, 0).is_ok(),
        "T → T should be positive (T as direct arg, not left of arrow in domain)"
    );
}

/// No occurrence: constructor type `Nat → Prop` doesn't mention T at all.
#[test]
fn test_positivity_no_occurrence() {
    let t_name = Name::from_string("T");
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);

    let ctor_type = Expr::arrow(nat, Expr::prop());

    assert!(
        check_pos(&t_name, &ctor_type, 0).is_ok(),
        "Constructor not mentioning T should pass positivity"
    );
}

/// Nested negative: `(T → T) → T` — T in domain of inner arrow within outer domain.
#[test]
fn test_positivity_nested_negative() {
    let t_name = Name::from_string("T");
    let t_ref = Expr::const_(t_name.clone(), vec![]);

    let inner_arrow = Expr::arrow(t_ref.clone(), t_ref.clone());
    let ctor_type = Expr::arrow(inner_arrow, t_ref);

    assert!(
        check_pos(&t_name, &ctor_type, 0).is_err(),
        "(T → T) → T should be rejected: T in nested negative position"
    );
}

/// Classic unsound: `(Bad → False) → Bad` — the standard non-positive example.
#[test]
fn test_positivity_classic_unsound_bad() {
    let bad_name = Name::from_string("Bad");
    let bad_ref = Expr::const_(bad_name.clone(), vec![]);
    let false_type = Expr::const_(Name::from_string("False"), vec![]);

    let domain = Expr::arrow(bad_ref.clone(), false_type);
    let ctor_type = Expr::arrow(domain, bad_ref);

    assert!(
        check_pos(&bad_name, &ctor_type, 0).is_err(),
        "Classic unsound type (Bad → False) → Bad must be rejected"
    );
}

/// Application in positive position: `List T → T` where List is not T.
#[test]
fn test_positivity_app_positive() {
    let t_name = Name::from_string("T");
    let t_ref = Expr::const_(t_name.clone(), vec![]);
    let list_t = Expr::app(
        Expr::const_(Name::from_string("List"), vec![]),
        t_ref.clone(),
    );

    let ctor_type = Expr::arrow(list_t, t_ref);

    assert!(
        check_pos(&t_name, &ctor_type, 0).is_ok(),
        "List T → T should pass: T in app arg of non-T head"
    );
}

/// Self-application: `T(T) → T` — T in args of T-headed app is negative.
#[test]
fn test_positivity_self_app_negative() {
    let t_name = Name::from_string("T");
    let t_ref = Expr::const_(t_name.clone(), vec![]);

    let domain = Expr::app(t_ref.clone(), t_ref.clone());
    let ctor_type = Expr::arrow(domain, t_ref);

    assert!(
        check_pos(&t_name, &ctor_type, 0).is_err(),
        "T(T) → T should be rejected: T in args of T-headed application"
    );
}

/// Three-way mutual inductive where sibling C appears in an index
/// argument of a B-headed application inside B's own constructor:
///
/// A.mk : A              (nullary — innocuous)
/// B.mk : B (C Unit) → B Unit  (C in index arg of B-headed domain)
/// C.mk : C Unit         (innocuous)
///
/// When validating B.mk for positivity of B (outer loop inductive_name=B),
/// the domain `B (C Unit)` has head=B, so we enter "I applied to args".
/// Args=[C Unit]. The inner loop over all_ind_names checks
/// `check_no_negative_occurrence("C", C_Unit)`, which detects C.
/// Without the #2145 fix, only "B" would be checked.
#[test]
fn test_positivity_three_way_mutual_transitive_rejected() {
    let a = Name::from_string("A");
    let b = Name::from_string("B");
    let c = Name::from_string("C");
    let unit = Name::from_string("Unit");

    let a_ref = Expr::const_(a.clone(), vec![]);
    let b_ref = Expr::const_(b.clone(), vec![]);
    let c_ref = Expr::const_(c.clone(), vec![]);
    let unit_ref = Expr::const_(unit.clone(), vec![]);

    // C Unit — C applied to Unit
    let c_unit = Expr::app(c_ref.clone(), unit_ref.clone());
    // B (C Unit) — B applied to index arg containing mutual type C
    let b_c_unit = Expr::app(b_ref.clone(), c_unit);
    // B Unit — B applied to clean index
    let b_unit = Expr::app(b_ref.clone(), unit_ref.clone());

    // A.mk : A (nullary)
    let a_mk = a_ref.clone();
    // B.mk : B (C Unit) → B Unit — domain has B-headed App with C in index
    let b_mk = Expr::arrow(b_c_unit, b_unit);
    // C.mk : Unit → C Unit
    let c_mk = Expr::arrow(
        unit_ref,
        Expr::app(
            c_ref.clone(),
            Expr::const_(Name::from_string("Unit"), vec![]),
        ),
    );

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
            InductiveType {
                name: c.clone(),
                type_: Expr::type_(),
                constructors: vec![Constructor {
                    name: Name::from_string("C.mk"),
                    type_: c_mk,
                }],
            },
        ],
    };

    let result = validate_inductive(&decl);
    assert!(
        result.is_err(),
        "Three-way mutual: C in index arg of B should be rejected, got {result:?}"
    );
}

/// Three-way mutual inductive where all types are direct arguments (no
/// index position), which is valid.
///
/// A.mk : B → A
/// B.mk : C → B
/// C.mk : C
#[test]
fn test_positivity_three_way_mutual_direct_accepted() {
    let a = Name::from_string("A");
    let b = Name::from_string("B");
    let c = Name::from_string("C");

    let a_ref = Expr::const_(a.clone(), vec![]);
    let b_ref = Expr::const_(b.clone(), vec![]);
    let c_ref = Expr::const_(c.clone(), vec![]);

    // A.mk : B → A
    let a_mk = Expr::arrow(b_ref.clone(), a_ref.clone());
    // B.mk : C → B
    let b_mk = Expr::arrow(c_ref.clone(), b_ref.clone());
    // C.mk : C (nullary)
    let c_mk = c_ref.clone();

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
            InductiveType {
                name: c.clone(),
                type_: Expr::type_(),
                constructors: vec![Constructor {
                    name: Name::from_string("C.mk"),
                    type_: c_mk,
                }],
            },
        ],
    };

    validate_inductive(&decl)
        .expect("Three-way mutual with direct args only should pass positivity");
}
