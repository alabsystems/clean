// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the public `SmtLogicalForm` classifier contract.
//!
//! Verifies that `classify_for_proof_translation` correctly maps Lean
//! expressions to the narrow cross-crate `SmtLogicalForm` enum, that
//! internal-only fields (e.g., `original` on arithmetic variants) do not
//! leak, and that special cases (Int.negSucc → Atom, Exists predicate
//! recovery) behave correctly.
//!
//! Part of #2902 Wave A.

use super::super::proof_translation_contract::{classify_for_proof_translation, SmtLogicalForm};
use super::*;
use clean_kernel::Level;

fn mk_const(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

fn mk_const_u(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![Level::zero()])
}

fn mk_and(a: Expr, b: Expr) -> Expr {
    Expr::app(Expr::app(mk_const("And"), a), b)
}

fn mk_or(a: Expr, b: Expr) -> Expr {
    Expr::app(Expr::app(mk_const("Or"), a), b)
}

fn mk_not(a: Expr) -> Expr {
    Expr::app(mk_const("Not"), a)
}

fn mk_implies(a: Expr, b: Expr) -> Expr {
    Expr::pi(BinderInfo::Default, a, b)
}

fn mk_exists(binder_type: Expr, body: Expr) -> Expr {
    Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Exists"), vec![Level::zero()]),
            binder_type.clone(),
        ),
        Expr::lam(BinderInfo::Default, binder_type, body),
    )
}

#[test]
fn test_classify_and() {
    let p = mk_const("P");
    let q = mk_const("Q");
    let expr = mk_and(p, q);
    let form = classify_for_proof_translation(&expr);
    assert!(
        matches!(form, SmtLogicalForm::And(_, _)),
        "And should classify as And, got {form:?}"
    );
}

#[test]
fn test_classify_or() {
    let p = mk_const("P");
    let q = mk_const("Q");
    let expr = mk_or(p, q);
    let form = classify_for_proof_translation(&expr);
    assert!(
        matches!(form, SmtLogicalForm::Or(_, _)),
        "Or should classify as Or, got {form:?}"
    );
}

#[test]
fn test_classify_not() {
    let p = mk_const("P");
    let expr = mk_not(p);
    let form = classify_for_proof_translation(&expr);
    assert!(
        matches!(form, SmtLogicalForm::Not(_)),
        "Not should classify as Not, got {form:?}"
    );
}

#[test]
fn test_classify_implies_as_non_dependent_pi() {
    let p = mk_const("P");
    let q = mk_const("Q");
    let expr = mk_implies(p, q);
    let form = classify_for_proof_translation(&expr);
    assert!(
        matches!(form, SmtLogicalForm::Implies(_, _)),
        "Non-dependent Pi should classify as Implies, got {form:?}"
    );
}

#[test]
fn test_classify_true() {
    let expr = mk_const("True");
    let form = classify_for_proof_translation(&expr);
    assert!(
        matches!(form, SmtLogicalForm::True),
        "True should classify as True, got {form:?}"
    );
}

#[test]
fn test_classify_false() {
    let expr = mk_const("False");
    let form = classify_for_proof_translation(&expr);
    assert!(
        matches!(form, SmtLogicalForm::False),
        "False should classify as False, got {form:?}"
    );
}

#[test]
fn test_classify_atom_unknown_const() {
    let expr = mk_const("SomeRandomType");
    let form = classify_for_proof_translation(&expr);
    assert!(
        matches!(form, SmtLogicalForm::Atom(_)),
        "Unknown constant should classify as Atom, got {form:?}"
    );
}

#[test]
fn test_classify_eq() {
    let a_ty = mk_const("A");
    let a = mk_const("a");
    let b = mk_const("b");
    let eq_expr = Expr::app(Expr::app(Expr::app(mk_const_u("Eq"), a_ty), a), b);
    let form = classify_for_proof_translation(&eq_expr);
    assert!(
        matches!(form, SmtLogicalForm::Eq { .. }),
        "Eq should classify as Eq, got {form:?}"
    );
}

#[test]
fn test_classify_exists_recovers_predicate() {
    let nat_ty = mk_const("Nat");
    let body = Expr::bvar(0);
    let expr = mk_exists(nat_ty, body);
    let form = classify_for_proof_translation(&expr);
    match form {
        SmtLogicalForm::Exists {
            binder_type,
            body: _,
            predicate,
        } => {
            assert!(
                matches!(binder_type.kind(), ExprKind::Const(n, _) if n.to_string() == "Nat"),
                "binder_type should be Nat"
            );
            assert!(
                matches!(predicate.kind(), ExprKind::Lam(..)),
                "predicate should be the raw lambda from the Exists application, got {:?}",
                predicate.kind()
            );
        }
        other => panic!("Exists should classify as Exists, got {other:?}"),
    }
}

#[test]
fn test_classify_int_negsucc_as_atom() {
    let n = mk_const("zero");
    let negsucc = Expr::app(mk_const("Int.negSucc"), n);
    let form = classify_for_proof_translation(&negsucc);
    assert!(
        matches!(form, SmtLogicalForm::Atom(_)),
        "Int.negSucc should be classified as Atom (fail-closed), got {form:?}"
    );
}

#[test]
fn test_classify_forall_dependent_pi() {
    let nat_ty = mk_const("Nat");
    let body = Expr::bvar(0);
    let expr = Expr::pi(BinderInfo::Default, nat_ty, body);
    let form = classify_for_proof_translation(&expr);
    assert!(
        matches!(form, SmtLogicalForm::Forall { .. }),
        "Dependent Pi should classify as Forall, got {form:?}"
    );
}
