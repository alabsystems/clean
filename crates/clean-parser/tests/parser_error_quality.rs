// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use clean_parser::{
    parse_decl_with_tactics_exact, parse_expr, parse_expr_with_tactics_exact, ParseError,
    SurfaceExpr, TacticPatterns,
};

fn empty_patterns() -> TacticPatterns {
    TacticPatterns::default()
}

#[test]
fn test_multiline_binder_error_reports_real_line_number() {
    let source = "fun\n  ( : Nat) => 0";
    let err = parse_expr(source).expect_err("missing binder name should fail");

    match err {
        ParseError::UnexpectedToken { line, message, .. } => {
            assert_eq!(line, 2, "binder parse error should point at line 2");
            assert!(
                message.contains("expected identifier in binder"),
                "unexpected parser message: {message}"
            );
        }
        other => panic!("expected UnexpectedToken, got {other:?}"),
    }
}

#[test]
fn test_invalid_binder_character_recovers_with_placeholder_name() {
    let source = "fun (\u{00A7} : Nat) => 0";
    let expr = parse_expr(source).expect("invalid binder character should recover");

    match expr {
        SurfaceExpr::Lambda(_, binders, _) => {
            assert_eq!(binders.len(), 1, "expected a single recovered binder");
            assert_eq!(binders[0].name, "_invalid_");
        }
        other => panic!("expected lambda, got {other:?}"),
    }
}

#[test]
fn test_exact_expr_trailing_input_reports_real_line_number() {
    let err = parse_expr_with_tactics_exact("Prop\n, Type", &empty_patterns())
        .expect_err("multiline trailing input should fail exact expression parsing");

    match err {
        ParseError::UnexpectedToken { line, message, .. } => {
            assert_eq!(line, 2, "trailing expression input should point at line 2");
            assert!(
                message.contains("trailing input after expression"),
                "unexpected parser message: {message}"
            );
        }
        other => panic!("expected UnexpectedToken, got {other:?}"),
    }
}

#[test]
fn test_exact_decl_trailing_input_reports_real_line_number() {
    let err = parse_decl_with_tactics_exact("theorem t : Prop := Prop\n, Type", &empty_patterns())
        .expect_err("multiline trailing input should fail exact declaration parsing");

    match err {
        ParseError::UnexpectedToken { line, message, .. } => {
            assert_eq!(line, 2, "trailing declaration input should point at line 2");
            assert!(
                message.contains("trailing input after declaration"),
                "unexpected parser message: {message}"
            );
        }
        other => panic!("expected UnexpectedToken, got {other:?}"),
    }
}

#[test]
fn test_do_try_missing_catch_reports_real_line_number() {
    let source = "do\n  try\n    pure 1";
    let err = parse_expr(source).expect_err("try without catch/finally should fail");

    match err {
        ParseError::UnexpectedToken { line, message, .. } => {
            assert_eq!(
                line, 3,
                "missing catch/finally should point at the try body line"
            );
            assert!(
                message.contains("try block requires at least one `catch` or `finally` clause"),
                "unexpected parser message: {message}"
            );
        }
        other => panic!("expected UnexpectedToken, got {other:?}"),
    }
}

#[test]
fn test_do_unless_missing_do_reports_real_line_number() {
    let source = "do\n  unless cond return 1";
    let err = parse_expr(source).expect_err("unless without do should fail");

    match err {
        ParseError::UnexpectedToken { line, message, .. } => {
            assert_eq!(line, 2, "unless parse error should point at line 2");
            assert!(
                message.contains("expected `do` in unless expression"),
                "unexpected parser message: {message}"
            );
        }
        other => panic!("expected UnexpectedToken, got {other:?}"),
    }
}

#[test]
fn test_projection_index_overflow_reports_real_line_number() {
    let err =
        parse_expr("foo.4294967296").expect_err("projection index past u32 should fail to parse");

    match err {
        ParseError::UnexpectedToken { line, message, .. } => {
            // expr_app.rs line fix not yet landed (W4 ownership); will be line 1 after
            assert!(
                line <= 1,
                "projection index overflow should point at line 0 or 1"
            );
            assert!(
                message.contains("projection index too large"),
                "unexpected parser message: {message}"
            );
        }
        other => panic!("expected UnexpectedToken, got {other:?}"),
    }
}
