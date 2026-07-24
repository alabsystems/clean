// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for where-clause desugaring into let-rec expressions.
//!
//! Split from where_desugar.rs for file size.

use super::*;
use clean_parser::{Span, SurfaceBinder, SurfaceExpr, WhereLocalDef};

fn dummy_span() -> Span {
    Span::dummy()
}

fn mk_ident(name: &str) -> SurfaceExpr {
    SurfaceExpr::ident(name)
}

fn mk_nat_ty() -> SurfaceExpr {
    SurfaceExpr::ident("Nat")
}

fn mk_explicit_binder(name: &str, ty: SurfaceExpr) -> SurfaceBinder {
    SurfaceBinder::explicit(name, ty)
}

// -- Single where clause --------------------------------------------------

#[test]
fn test_desugar_where_single_clause_produces_let_rec() {
    // def foo := bar n where bar (x : Nat) : Nat := x + 1
    let body = mk_ident("bar_call");
    let clause = WhereClause {
        name: "bar".to_string(),
        params: vec![mk_explicit_binder("x", mk_nat_ty())],
        return_type: Some(mk_nat_ty()),
        body: mk_ident("x_plus_1"),
        span: dummy_span(),
    };

    let result = desugar_where(body, &[clause]);

    // Should produce: let rec bar : (x : Nat) → Nat := fun (x : Nat) => x_plus_1 in bar_call
    match &result {
        SurfaceExpr::LetRec(_, binder, val, inner) => {
            assert_eq!(binder.name, "bar");
            // binder.ty should be a Pi type
            assert!(binder.ty.is_some());
            // val should be a Lambda
            assert!(matches!(val.as_ref(), SurfaceExpr::Lambda(..)));
            // inner body is the original body
            assert!(matches!(inner.as_ref(), SurfaceExpr::Ident(_, name) if name == "bar_call"));
        }
        other => panic!("expected LetRec, got {other:?}"),
    }
}

// -- Multiple where clauses -----------------------------------------------

#[test]
fn test_desugar_where_multiple_clauses_nested_let_rec() {
    // def foo := baz (bar n)
    // where
    //   bar (x : Nat) : Nat := x + 1
    //   baz (y : Nat) : Nat := y + 2
    let body = mk_ident("combined_call");
    let clauses = vec![
        WhereClause {
            name: "bar".to_string(),
            params: vec![mk_explicit_binder("x", mk_nat_ty())],
            return_type: Some(mk_nat_ty()),
            body: mk_ident("x_plus_1"),
            span: dummy_span(),
        },
        WhereClause {
            name: "baz".to_string(),
            params: vec![mk_explicit_binder("y", mk_nat_ty())],
            return_type: Some(mk_nat_ty()),
            body: mk_ident("bar_y_plus_1"),
            span: dummy_span(),
        },
    ];

    let result = desugar_where(body, &clauses);

    // Should produce: let rec bar := ... in (let rec baz := ... in combined_call)
    match &result {
        SurfaceExpr::LetRec(_, binder1, _, inner1) => {
            assert_eq!(binder1.name, "bar", "outer let rec should be 'bar'");
            match inner1.as_ref() {
                SurfaceExpr::LetRec(_, binder2, _, inner2) => {
                    assert_eq!(binder2.name, "baz", "inner let rec should be 'baz'");
                    assert!(
                        matches!(inner2.as_ref(), SurfaceExpr::Ident(_, name) if name == "combined_call"),
                        "innermost body should be original body"
                    );
                }
                other => panic!("expected inner LetRec, got {other:?}"),
            }
        }
        other => panic!("expected outer LetRec, got {other:?}"),
    }
}

// -- Empty clauses --------------------------------------------------------

#[test]
fn test_desugar_where_empty_clauses_returns_body_unchanged() {
    let body = mk_ident("original");
    let result = desugar_where(body, &[]);

    assert!(
        matches!(&result, SurfaceExpr::Ident(_, name) if name == "original"),
        "empty clauses should return body unchanged"
    );
}

// -- No parameters --------------------------------------------------------

#[test]
fn test_desugar_where_clause_no_params_no_lambda() {
    // where val : Nat := 42
    let body = mk_ident("use_val");
    let clause = WhereClause {
        name: "val".to_string(),
        params: vec![],
        return_type: Some(mk_nat_ty()),
        body: SurfaceExpr::nat(42),
        span: dummy_span(),
    };

    let result = desugar_where(body, &[clause]);

    match &result {
        SurfaceExpr::LetRec(_, binder, val, _) => {
            assert_eq!(binder.name, "val");
            // No params means val is NOT wrapped in a Lambda; the return-type
            // annotation rides as an ascription on the body (the recursive
            // lift reads the helper's return type from it).
            match val.as_ref() {
                SurfaceExpr::Ascription(_, inner, ty) => {
                    assert!(
                        matches!(inner.as_ref(), SurfaceExpr::Lit(..)),
                        "ascribed body should be the literal clause body"
                    );
                    assert!(
                        matches!(ty.as_ref(), SurfaceExpr::Ident(_, n) if n == "Nat"),
                        "ascription should carry the clause return type"
                    );
                }
                other => panic!("expected ascribed body without Lambda, got {other:?}"),
            }
        }
        other => panic!("expected LetRec, got {other:?}"),
    }
}

// -- No return type -------------------------------------------------------

#[test]
fn test_desugar_where_clause_no_return_type_leaves_binder_unannotated() {
    // where bar (x : Nat) := x
    let body = mk_ident("use_bar");
    let clause = WhereClause {
        name: "bar".to_string(),
        params: vec![mk_explicit_binder("x", mk_nat_ty())],
        return_type: None,
        body: mk_ident("x"),
        span: dummy_span(),
    };

    let result = desugar_where(body, &[clause]);

    match &result {
        SurfaceExpr::LetRec(_, binder, val, _) => {
            assert_eq!(binder.name, "bar");
            // No annotation: the binder type stays `None` so both the plain
            // `let` lowering and the recursive lift INFER the type from the
            // lambda value (a `Pi(.., Hole)` here would be mistaken for the
            // helper's RETURN type by the recursive lift).
            assert!(
                binder.ty.is_none(),
                "missing return type should leave the binder unannotated, got {:?}",
                binder.ty
            );
            assert!(
                matches!(val.as_ref(), SurfaceExpr::Lambda(..)),
                "value should still be the params lambda"
            );
        }
        other => panic!("expected LetRec, got {other:?}"),
    }
}

// -- Where clause referencing parameters ----------------------------------

#[test]
fn test_desugar_where_clause_referencing_outer_params() {
    let body = SurfaceExpr::app(mk_ident("helper"), vec![mk_ident("n")]);
    let helper_body = SurfaceExpr::app(mk_ident("HAdd.hAdd"), vec![mk_ident("x"), mk_ident("n")]);
    let clause = WhereClause {
        name: "helper".to_string(),
        params: vec![mk_explicit_binder("x", mk_nat_ty())],
        return_type: Some(mk_nat_ty()),
        body: helper_body,
        span: dummy_span(),
    };

    let result = desugar_where(body, &[clause]);

    match &result {
        SurfaceExpr::LetRec(_, binder, val, inner) => {
            assert_eq!(binder.name, "helper");
            assert!(matches!(val.as_ref(), SurfaceExpr::Lambda(..)));
            assert!(matches!(inner.as_ref(), SurfaceExpr::App(..)));
        }
        other => panic!("expected LetRec, got {other:?}"),
    }
}

// -- Multiple binders in one clause --------------------------------------

#[test]
fn test_desugar_where_clause_multiple_binders() {
    // where add (x : Nat) (y : Nat) : Nat := x + y
    let body = mk_ident("use_add");
    let clause = WhereClause {
        name: "add".to_string(),
        params: vec![
            mk_explicit_binder("x", mk_nat_ty()),
            mk_explicit_binder("y", mk_nat_ty()),
        ],
        return_type: Some(mk_nat_ty()),
        body: mk_ident("x_plus_y"),
        span: dummy_span(),
    };

    let result = desugar_where(body, &[clause]);

    match &result {
        SurfaceExpr::LetRec(_, binder, val, _) => {
            assert_eq!(binder.name, "add");
            match binder.ty.as_deref() {
                Some(SurfaceExpr::Pi(_, params, _)) => {
                    assert_eq!(params.len(), 2, "should have 2 params in Pi type");
                }
                other => panic!("expected Pi type with 2 params, got {other:?}"),
            }
            match val.as_ref() {
                SurfaceExpr::Lambda(_, params, _) => {
                    assert_eq!(params.len(), 2, "lambda should have 2 params");
                }
                other => panic!("expected Lambda with 2 params, got {other:?}"),
            }
        }
        other => panic!("expected LetRec, got {other:?}"),
    }
}

// -- desugar_where_from_parsed integration --------------------------------

#[test]
fn test_desugar_where_from_parsed_single_def() {
    let body = mk_ident("call_helper");
    let where_defs = vec![WhereLocalDef {
        span: dummy_span(),
        name: "helper".to_string(),
        binders: vec![SurfaceBinder::explicit("x", mk_nat_ty())],
        ret_ty: Some(Box::new(mk_nat_ty())),
        body: mk_ident("x_plus_1"),
    }];

    let result = desugar_where_from_parsed(&body, &where_defs);

    match &result {
        SurfaceExpr::LetRec(_, binder, _, inner) => {
            assert_eq!(binder.name, "helper");
            assert!(
                matches!(inner.as_ref(), SurfaceExpr::Ident(_, n) if n == "call_helper"),
                "inner should be original body"
            );
        }
        other => panic!("expected LetRec from desugar_where_from_parsed, got {other:?}"),
    }
}

#[test]
fn test_desugar_where_from_parsed_empty_defs_returns_body() {
    let body = mk_ident("unchanged");
    let result = desugar_where_from_parsed(&body, &[]);
    assert!(
        matches!(&result, SurfaceExpr::Ident(_, name) if name == "unchanged"),
        "empty where_defs should return body unchanged"
    );
}

#[test]
fn test_desugar_where_from_parsed_multiple_defs() {
    let body = mk_ident("call_both");
    let where_defs = vec![
        WhereLocalDef {
            span: dummy_span(),
            name: "f".to_string(),
            binders: vec![],
            ret_ty: Some(Box::new(mk_nat_ty())),
            body: SurfaceExpr::nat(1),
        },
        WhereLocalDef {
            span: dummy_span(),
            name: "g".to_string(),
            binders: vec![],
            ret_ty: Some(Box::new(mk_nat_ty())),
            body: SurfaceExpr::nat(2),
        },
    ];

    let result = desugar_where_from_parsed(&body, &where_defs);

    // Should produce: let rec f := 1 in (let rec g := 2 in call_both)
    match &result {
        SurfaceExpr::LetRec(_, binder1, _, inner1) => {
            assert_eq!(binder1.name, "f");
            match inner1.as_ref() {
                SurfaceExpr::LetRec(_, binder2, _, inner2) => {
                    assert_eq!(binder2.name, "g");
                    assert!(
                        matches!(inner2.as_ref(), SurfaceExpr::Ident(_, n) if n == "call_both"),
                    );
                }
                other => panic!("expected inner LetRec, got {other:?}"),
            }
        }
        other => panic!("expected outer LetRec, got {other:?}"),
    }
}
