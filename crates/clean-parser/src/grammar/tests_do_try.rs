// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Focused `do try/catch/finally` parser regressions.

#![allow(clippy::unwrap_used)]

use super::*;
use crate::{ParseError, SurfaceName};

#[test]
fn refutable_do_let_accepts_the_original_kernel_source() {
    let source = include_str!("../../../../theories/kcheck_labelled/KCheck/Kernel.lean");
    let report = crate::parse_file_with_diagnostics(source).unwrap();
    assert!(report.diagnostics.is_empty(), "{:?}", report.diagnostics);
    assert!(!report
        .decls
        .iter()
        .any(|decl| matches!(decl, SurfaceDecl::RawDecl { .. })));
    fn mutual_members(decl: &SurfaceDecl) -> Option<&[SurfaceDecl]> {
        match decl {
            SurfaceDecl::Namespace { decls, .. } => decls.iter().find_map(mutual_members),
            SurfaceDecl::SetOption {
                body: Some(body), ..
            } => mutual_members(body),
            SurfaceDecl::Mutual { decls, .. } => Some(decls),
            _ => None,
        }
    }
    let mutual = report.decls.iter().find_map(mutual_members);
    let names: Vec<_> = mutual
        .expect("original checker mutual block")
        .iter()
        .map(|decl| match decl {
            SurfaceDecl::Def { name, .. } => name.name().to_string(),
            other => panic!("unexpected checker block member: {other:?}"),
        })
        .collect();
    assert_eq!(names, ["whnf", "conv", "inferAnn", "check", "walk"]);
}

#[test]
fn refutable_do_let_keeps_a_local_function_before_an_outer_match_pipe() {
    let source = "do\n  match item with\n  | some n => do\n    let f x := x\n  | none => pure ()";
    Parser::parse_expr(source).unwrap();
}

#[test]
fn refutable_do_let_parses_a_bare_constructor_with_its_fallback() {
    let expr = Parser::parse_expr("do\n  let some n := xs[i]? | throw 7\n  pure n").unwrap();
    let SurfaceExpr::Do(_, elements) = expr else {
        panic!("expected a do expression")
    };
    assert!(matches!(
        elements.as_slice(),
        [DoElem::LetExpr(
            _,
            SurfacePattern::Ctor(name, fields),
            _,
            DoLetExprKind::PurePattern,
            fallback,
        ), DoElem::Expr(_, _)]
            if name.name() == SurfaceName::generated_path("some").name()
                && matches!(fields.as_slice(), [SurfacePattern::Var(field)]
                    if field.name() == SurfaceName::generated_path("n").name())
                && fallback.len() == 1
    ));
}

#[test]
fn test_parse_do_try_catch_finally_braced() {
    let expr =
        Parser::parse_expr("do try { return 1 } catch e => { return 0 } finally { return 2 }")
            .unwrap();
    match expr {
        SurfaceExpr::Do(_, elems) => {
            assert_eq!(elems.len(), 1);
            match &elems[0] {
                DoElem::TryCatch(_, try_body, catches, finally_body) => {
                    assert_eq!(try_body.len(), 1, "try body should have one element");
                    assert!(matches!(&try_body[0], DoElem::Return(_, _)));
                    assert_eq!(catches.len(), 1, "should have one catch clause");
                    assert_eq!(
                        (catches[0].binder).name(),
                        crate::SurfaceName::generated_path("e").name()
                    );
                    assert_eq!(
                        catches[0].body.len(),
                        1,
                        "catch body should have one element"
                    );
                    assert!(matches!(&catches[0].body[0], DoElem::Return(_, _)));
                    let finally_body = finally_body.as_ref().expect("should have finally clause");
                    assert_eq!(
                        finally_body.len(),
                        1,
                        "finally body should have one element"
                    );
                    assert!(matches!(&finally_body[0], DoElem::Return(_, _)));
                }
                other => panic!("Expected TryCatch, got {other:?}"),
            }
        }
        other => panic!("Expected Do, got {other:?}"),
    }
}

#[test]
fn test_parse_do_try_requires_clause_reports_current_line() {
    let err = Parser::parse_expr("\ndo try return 1").unwrap_err();
    match err {
        ParseError::UnexpectedToken { line, message, .. } => {
            assert_eq!(line, 2, "try-without-catch/finally should report line 2");
            assert!(
                message.contains("requires at least one `catch` or `finally` clause"),
                "unexpected message: {message}"
            );
        }
        other => panic!("Expected UnexpectedToken, got {other:?}"),
    }
}
