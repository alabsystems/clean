// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Unit tests for the metaprogram computed-control-flow recognizer
//! (`meta_control_flow`).
//!
//! These pin the *syntactic* recognition of the `if`-then-else body shape and the
//! `Bool`-constructor classification of a whnf-reduced condition. End-to-end
//! elaboration + kernel-check behavior (branch selection, decline-on-stuck,
//! wrong-typed branch failure) is covered by the integration-style tests in
//! `infer::tests::user_tactic_exec`.

use super::*;
use clean_kernel::Expr;
use clean_parser::{Span, SurfaceExpr};

fn ident(name: &str) -> SurfaceExpr {
    SurfaceExpr::Ident(Span::dummy(), name.to_owned())
}

fn if_expr(cond: SurfaceExpr, then_br: SurfaceExpr, else_br: SurfaceExpr) -> SurfaceExpr {
    SurfaceExpr::If(
        Span::dummy(),
        Box::new(cond),
        Box::new(then_br),
        Box::new(else_br),
    )
}

#[test]
fn test_is_meta_if_body_accepts_if_then_else() {
    let body = if_expr(ident("true"), ident("Nat.zero"), ident("Nat.succ"));
    assert!(
        is_meta_if_body(&body),
        "an `if c then a else b` body is a computed-control-flow body"
    );
}

#[test]
fn test_is_meta_if_body_rejects_ordinary_ident() {
    assert!(
        !is_meta_if_body(&ident("Nat.zero")),
        "an ordinary identifier body is not a computed-control-flow body"
    );
}

#[test]
fn test_is_meta_if_body_rejects_application() {
    let body = SurfaceExpr::App(
        Span::dummy(),
        Box::new(ident("f")),
        vec![clean_parser::SurfaceArg::positional(ident("x"))],
    );
    assert!(
        !is_meta_if_body(&body),
        "an application body is not a computed-control-flow body"
    );
}

#[test]
fn test_classify_bool_true_constructor_takes_then() {
    let reduced = Expr::const_(Name::from_string("Bool.true"), vec![]);
    assert!(
        matches!(classify_bool(&reduced), Some(CondDecision::Then)),
        "`Bool.true` must decide the then branch"
    );
}

#[test]
fn test_classify_bool_false_constructor_takes_else() {
    let reduced = Expr::const_(Name::from_string("Bool.false"), vec![]);
    assert!(
        matches!(classify_bool(&reduced), Some(CondDecision::Else)),
        "`Bool.false` must decide the else branch"
    );
}

#[test]
fn test_classify_bool_non_bool_constant_declines() {
    // A non-Bool constructor is not a decided metaprogram-time value.
    let reduced = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    assert!(
        classify_bool(&reduced).is_none(),
        "a non-Bool constant must decline (not pick a branch)"
    );
}

#[test]
fn test_classify_bool_stuck_application_declines() {
    // A stuck application (e.g. an unreduced `Nat.decEq x y`) is symbolic.
    let stuck = Expr::app(
        Expr::const_(Name::from_string("f"), vec![]),
        Expr::const_(Name::from_string("x"), vec![]),
    );
    assert!(
        classify_bool(&stuck).is_none(),
        "a stuck application condition must decline (not pick a branch)"
    );
}
