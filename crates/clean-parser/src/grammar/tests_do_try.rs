// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Focused `do try/catch/finally` parser regressions.

#![allow(clippy::unwrap_used)]

use super::*;
use crate::ParseError;

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
                    assert_eq!(catches[0].binder, "e");
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
