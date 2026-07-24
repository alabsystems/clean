// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for `parse_expr_with_tactics_exact` — validates all input consumed.

use super::*;
use crate::tactic_patterns::TacticPatterns;
use crate::ParseError;

fn empty_patterns() -> TacticPatterns {
    TacticPatterns::default()
}

#[test]
fn test_exact_valid_expression_consumed() {
    let patterns = empty_patterns();
    let result = Parser::parse_expr_with_tactics_exact("Prop", &patterns);
    assert!(
        result.is_ok(),
        "Simple ident should parse exactly: {result:?}"
    );
}

#[test]
fn test_exact_rejects_trailing_tokens() {
    let patterns = empty_patterns();
    let result = Parser::parse_expr_with_tactics_exact("Prop Type", &patterns);
    // "Prop Type" is function application (Prop applied to Type), should succeed
    assert!(
        result.is_ok(),
        "Application should parse exactly: {result:?}"
    );

    // But garbage after a valid expression should fail
    let result = Parser::parse_expr_with_tactics_exact("Prop, Type", &patterns);
    assert!(result.is_err(), "Trailing comma should be rejected");
    match result.unwrap_err() {
        ParseError::UnexpectedToken { message, .. } => {
            assert!(
                message.contains("trailing"),
                "Error should mention trailing: {message}"
            );
        }
        other => panic!("Expected UnexpectedToken, got {other:?}"),
    }
}

#[test]
fn test_exact_empty_input_errors() {
    let patterns = empty_patterns();
    let result = Parser::parse_expr_with_tactics_exact("", &patterns);
    assert!(result.is_err(), "Empty input should error");
}

#[test]
fn test_exact_projection_index_overflow_reports_current_line() {
    let patterns = empty_patterns();
    let result = Parser::parse_expr_with_tactics_exact("\nfoo.4294967296", &patterns);
    match result.unwrap_err() {
        ParseError::UnexpectedToken { line, message, .. } => {
            assert_eq!(line, 2, "projection index overflow should report line 2");
            assert!(
                message.contains("projection index too large"),
                "unexpected message: {message}"
            );
        }
        other => panic!("Expected UnexpectedToken, got {other:?}"),
    }
}

#[test]
fn test_exact_lexer_error_reports_current_line() {
    let patterns = empty_patterns();
    let result = Parser::parse_expr_with_tactics_exact("\n\"unterminated", &patterns);
    match result.unwrap_err() {
        ParseError::UnexpectedToken { line, message, .. } => {
            assert_eq!(line, 2, "lexer error should report line 2");
            assert!(
                message.contains("lexer error: unterminated string"),
                "unexpected message: {message}"
            );
        }
        other => panic!("Expected UnexpectedToken, got {other:?}"),
    }
}

#[test]
fn test_exact_garbage_input_errors() {
    let patterns = empty_patterns();
    // This is the exact input from the #2049 issue
    let result = Parser::parse_expr_with_tactics_exact("@@#$ invalid syntax !!", &patterns);
    assert!(
        result.is_err(),
        "Garbage input should error with exact parsing"
    );
}

#[test]
fn test_exact_arrow_expression_consumed() {
    let patterns = empty_patterns();
    let result = Parser::parse_expr_with_tactics_exact("A -> B -> C", &patterns);
    assert!(
        result.is_ok(),
        "Arrow chain should parse exactly: {result:?}"
    );
}

#[test]
fn test_exact_rejects_chained_set_difference() {
    let patterns = empty_patterns();
    let result = Parser::parse_expr_with_tactics_exact("A \\ B \\ C", &patterns);
    assert!(
        result.is_err(),
        "plain infix:70 set difference should reject chained `\\`: {result:?}"
    );
}

#[test]
fn test_exact_rejects_intersection_then_set_difference_without_parentheses() {
    let patterns = empty_patterns();
    let result = Parser::parse_expr_with_tactics_exact("A ∩ B \\ C", &patterns);
    assert!(
        result.is_err(),
        "plain infix:70 set difference should reject `A ∩ B \\\\ C` without parentheses: {result:?}"
    );
}

#[test]
fn test_exact_trailing_comment_ok() {
    let patterns = empty_patterns();
    // Comments are stripped by the lexer, so trailing comments should be fine
    let result = Parser::parse_expr_with_tactics_exact("Prop -- a comment", &patterns);
    assert!(
        result.is_ok(),
        "Trailing comment should be stripped: {result:?}"
    );
}

#[test]
fn test_exact_postfix_bang_keeps_termination_by_as_prefix_not_argument() {
    let patterns = empty_patterns();
    let expr = Parser::parse_expr_with_tactics_exact("f !termination_by", &patterns)
        .expect("prefix `!termination_by` argument should parse exactly");

    match expr {
        SurfaceExpr::App(_, func, args) => {
            assert!(matches!(&*func, SurfaceExpr::Ident(_, s) if s == "f"));
            assert_eq!(args.len(), 1, "expected one argument after f");
            match &args[0].expr {
                SurfaceExpr::App(_, not_func, not_args) => {
                    assert!(
                        matches!(&**not_func, SurfaceExpr::Ident(_, s) if s == "Not"),
                        "expected prefix Not argument"
                    );
                    assert_eq!(not_args.len(), 1, "Not should wrap exactly one expression");
                    assert!(
                        matches!(
                            &not_args[0].expr,
                            SurfaceExpr::Ident(_, s) if s == "termination_by"
                        ),
                        "expected `termination_by` identifier inside Not"
                    );
                }
                other => panic!("expected Not application argument, got {other:?}"),
            }
        }
        other => panic!("expected application, got {other:?}"),
    }
}

// =========================================================================
// Declaration exact-parsing tests (Part of #2553)
// =========================================================================

#[test]
fn test_exact_decl_valid_theorem_consumed() {
    let patterns = empty_patterns();
    let result = Parser::parse_decl_with_tactics_exact("theorem t : Prop := Prop", &patterns);
    assert!(
        result.is_ok(),
        "Valid theorem declaration should parse exactly: {result:?}"
    );
}

#[test]
fn test_exact_decl_rejects_trailing_garbage() {
    let patterns = empty_patterns();
    // Comma is not consumed by the expression parser as part of function application,
    // so it remains as a trailing token after the declaration body.
    let result = Parser::parse_decl_with_tactics_exact("theorem t : Prop := Prop, Type", &patterns);
    assert!(
        result.is_err(),
        "Declaration with trailing comma must be rejected"
    );
    match result.unwrap_err() {
        ParseError::UnexpectedToken { message, .. } => {
            assert!(
                message.contains("trailing"),
                "Error should mention trailing: {message}"
            );
        }
        other => panic!("Expected UnexpectedToken, got {other:?}"),
    }
}

#[test]
fn test_exact_decl_valid_def_consumed() {
    let patterns = empty_patterns();
    let result = Parser::parse_decl_with_tactics_exact("def f : Prop := Prop", &patterns);
    assert!(
        result.is_ok(),
        "Valid def declaration should parse exactly: {result:?}"
    );
}
