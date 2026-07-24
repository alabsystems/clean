// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Unit tests for the metaprogram query recognizer (`meta_query`).
//!
//! These pin the *syntactic* recognition of the value-channel / query body
//! shapes. End-to-end elaboration + kernel-check behavior is covered by the
//! integration-style tests in `infer::tests::user_tactic_exec`.

use super::*;
use clean_parser::{
    DoElem, Projection, Span, SurfaceArg, SurfaceBinder, SurfaceBinderInfo, SurfaceExpr,
};

fn ident(name: &str) -> SurfaceExpr {
    SurfaceExpr::Ident(Span::dummy(), name.to_owned())
}

fn binder(name: &str) -> SurfaceBinder {
    SurfaceBinder::new(name, None, SurfaceBinderInfo::Explicit)
}

#[test]
fn test_as_infer_type_call_recognizes_bare_head() {
    let call = infer_type_call(ident("x"));
    let arg = as_infer_type_call(&call).expect("`inferType x` should be recognized");
    assert!(
        matches!(arg, SurfaceExpr::Ident(_, n) if n == "x"),
        "argument should be `x`, got {arg:?}"
    );
}

#[test]
fn test_as_infer_type_call_recognizes_qualified_head() {
    // `Expr.inferType x`
    let head = SurfaceExpr::Proj(
        Span::dummy(),
        Box::new(ident("Expr")),
        Projection::Named("inferType".to_owned()),
    );
    let call = SurfaceExpr::App(
        Span::dummy(),
        Box::new(head),
        vec![SurfaceArg::positional(ident("x"))],
    );
    assert!(
        as_infer_type_call(&call).is_some(),
        "`Expr.inferType x` should be recognized"
    );
}

#[test]
fn test_as_infer_type_call_rejects_wrong_arity() {
    // `inferType a b` is not the single-argument query shape.
    let call = SurfaceExpr::App(
        Span::dummy(),
        Box::new(ident("inferType")),
        vec![
            SurfaceArg::positional(ident("a")),
            SurfaceArg::positional(ident("b")),
        ],
    );
    assert!(
        as_infer_type_call(&call).is_none(),
        "a two-argument `inferType` call must not be recognized"
    );
}

#[test]
fn test_as_infer_type_call_rejects_other_head() {
    let call = SurfaceExpr::App(
        Span::dummy(),
        Box::new(ident("mkConst")),
        vec![SurfaceArg::positional(ident("x"))],
    );
    assert!(
        as_infer_type_call(&call).is_none(),
        "`mkConst x` is not a query and must defer to the constructor evaluator"
    );
}

#[test]
fn test_is_meta_query_body_accepts_terminal_query() {
    assert!(
        is_meta_query_body(&infer_type_call(ident("x"))),
        "a terminal `inferType x` body is a meta-query body"
    );
}

#[test]
fn test_is_meta_query_body_accepts_value_channel_do_block() {
    // do let t := inferType x; t
    let body = SurfaceExpr::Do(
        Span::dummy(),
        vec![
            DoElem::Let(
                Span::dummy(),
                binder("t"),
                Box::new(infer_type_call(ident("x"))),
            ),
            DoElem::Expr(Span::dummy(), Box::new(ident("t"))),
        ],
    );
    assert!(
        is_meta_query_body(&body),
        "a `do let t := inferType x; t` body is a value-channel query body"
    );
}

#[test]
fn test_is_meta_query_body_rejects_plain_do_block() {
    // do let t := x; t  — no query, leave to the normal pipeline.
    let body = SurfaceExpr::Do(
        Span::dummy(),
        vec![
            DoElem::Let(Span::dummy(), binder("t"), Box::new(ident("x"))),
            DoElem::Expr(Span::dummy(), Box::new(ident("t"))),
        ],
    );
    assert!(
        !is_meta_query_body(&body),
        "a do-block with no query let must not be treated as a meta-query body"
    );
}

#[test]
fn test_is_meta_query_body_rejects_ordinary_expr() {
    assert!(
        !is_meta_query_body(&ident("Nat.zero")),
        "an ordinary identifier body is not a meta-query body"
    );
}

#[test]
fn test_as_whnf_call_recognizes_bare_head() {
    let call = whnf_call(ident("x"));
    let arg = as_whnf_call(&call).expect("`whnf x` should be recognized");
    assert!(
        matches!(arg, SurfaceExpr::Ident(_, n) if n == "x"),
        "argument should be `x`, got {arg:?}"
    );
}

#[test]
fn test_as_whnf_call_recognizes_qualified_head() {
    // `Expr.whnf x`
    let head = SurfaceExpr::Proj(
        Span::dummy(),
        Box::new(ident("Expr")),
        Projection::Named("whnf".to_owned()),
    );
    let call = SurfaceExpr::App(
        Span::dummy(),
        Box::new(head),
        vec![SurfaceArg::positional(ident("x"))],
    );
    assert!(
        as_whnf_call(&call).is_some(),
        "`Expr.whnf x` should be recognized"
    );
}

#[test]
fn test_as_whnf_call_rejects_wrong_arity() {
    let call = SurfaceExpr::App(
        Span::dummy(),
        Box::new(ident("whnf")),
        vec![
            SurfaceArg::positional(ident("a")),
            SurfaceArg::positional(ident("b")),
        ],
    );
    assert!(
        as_whnf_call(&call).is_none(),
        "a two-argument `whnf` call must not be recognized as the unary query"
    );
}

#[test]
fn test_as_check_type_call_recognizes_bare_head() {
    let call = check_type_call(ident("e"), ident("Nat"));
    let (e, ty) = as_check_type_call(&call).expect("`checkType e Nat` should be recognized");
    assert!(
        matches!(e, SurfaceExpr::Ident(_, n) if n == "e"),
        "first argument should be `e`, got {e:?}"
    );
    assert!(
        matches!(ty, SurfaceExpr::Ident(_, n) if n == "Nat"),
        "second argument should be `Nat`, got {ty:?}"
    );
}

#[test]
fn test_as_check_type_call_recognizes_qualified_head() {
    // `Expr.checkType e Nat`
    let head = SurfaceExpr::Proj(
        Span::dummy(),
        Box::new(ident("Expr")),
        Projection::Named("checkType".to_owned()),
    );
    let call = SurfaceExpr::App(
        Span::dummy(),
        Box::new(head),
        vec![
            SurfaceArg::positional(ident("e")),
            SurfaceArg::positional(ident("Nat")),
        ],
    );
    assert!(
        as_check_type_call(&call).is_some(),
        "`Expr.checkType e Nat` should be recognized"
    );
}

#[test]
fn test_as_check_type_call_rejects_wrong_arity() {
    // `checkType e` (one argument) is not the two-argument query shape.
    let call = SurfaceExpr::App(
        Span::dummy(),
        Box::new(ident("checkType")),
        vec![SurfaceArg::positional(ident("e"))],
    );
    assert!(
        as_check_type_call(&call).is_none(),
        "a one-argument `checkType` call must not be recognized"
    );
}

#[test]
fn test_is_meta_query_body_accepts_terminal_whnf_query() {
    assert!(
        is_meta_query_body(&whnf_call(ident("x"))),
        "a terminal `whnf x` body is a meta-query body"
    );
}

#[test]
fn test_is_meta_query_body_accepts_terminal_check_type_query() {
    assert!(
        is_meta_query_body(&check_type_call(ident("e"), ident("Nat"))),
        "a terminal `checkType e Nat` body is a meta-query body"
    );
}

#[test]
fn test_is_meta_query_body_accepts_value_channel_compose() {
    // do let t := inferType e; checkType e t
    let body = SurfaceExpr::Do(
        Span::dummy(),
        vec![
            DoElem::Let(
                Span::dummy(),
                binder("t"),
                Box::new(infer_type_call(ident("e"))),
            ),
            DoElem::Expr(
                Span::dummy(),
                Box::new(check_type_call(ident("e"), ident("t"))),
            ),
        ],
    );
    assert!(
        is_meta_query_body(&body),
        "a `do let t := inferType e; checkType e t` body is a value-channel query body"
    );
}
