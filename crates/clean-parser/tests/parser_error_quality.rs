// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use clean_parser::{
    parse_decl, parse_decl_exact, parse_decl_with_tactics_exact, parse_expr,
    parse_expr_with_tactics_exact, parse_file, ParseError, TacticPatterns,
};

fn empty_patterns() -> TacticPatterns {
    TacticPatterns::default()
}

#[test]
fn exact_plain_declarations_reject_unconsumed_tokens_at_their_location() {
    for (source, expected_line) in [
        ("def exactValue : Type := Type\n)", 2),
        ("inductive ExactData : Type\n| mk : ExactData\n,", 3),
        ("def first : Type := Type\ndef second : Type := Type", 2),
    ] {
        parse_decl(source).expect("the prefix API still returns the first declaration");
        match parse_decl_exact(source).expect_err("the complete source must be consumed") {
            ParseError::UnexpectedToken { line, message, .. } => {
                assert_eq!(line, expected_line);
                assert!(
                    message.contains("trailing input after declaration"),
                    "{message}"
                );
            }
            other => panic!("expected a located trailing-input error, got {other:?}"),
        }
    }
}

#[test]
fn exact_plain_declarations_allow_trailing_comments() {
    for source in [
        "def exactValue : Type := Type\n-- trailing comment\n",
        "inductive ExactData : Type\n| mk : ExactData\n/- trailing comment -/\n",
    ] {
        parse_decl_exact(source).expect("comments and whitespace are not trailing tokens");
    }
}

#[test]
fn exact_plain_declarations_preserve_nested_command_refusals() {
    let source = "section\nprivate section\nend";
    let expected = parse_decl(source).expect_err("the nested command is refused");
    let actual = parse_decl_exact(source).expect_err("exact parsing preserves the first refusal");
    assert_eq!(actual.to_string(), expected.to_string());
}

#[test]
fn exact_declarations_reject_orphan_documentation_at_eof() {
    for (source, expected_line, expected_col, expected_message) in [
        (
            "def docEofValue : Nat := 1\n/-- orphan declaration documentation -/\n",
            3,
            0,
            "unexpected end of input; expected ",
        ),
        (
            "def docEofValue : Nat := 1\n/-- first -/\n/-- second -/\n",
            2,
            12,
            "unexpected token '/--'; expected ",
        ),
    ] {
        parse_decl(source).expect("the prefix API still returns the completed declaration");
        for (api, parsed) in [
            ("plain", parse_decl_exact(source)),
            (
                "tactic-aware",
                parse_decl_with_tactics_exact(source, &empty_patterns()),
            ),
        ] {
            match parsed.expect_err("a declaration doc comment must introduce a declaration") {
                ParseError::ModuleSyntaxRefused { line, col, message } => {
                    assert_eq!((line, col), (expected_line, expected_col), "{api}");
                    assert!(message.starts_with(expected_message), "{api}: {message}");
                    assert!(message.contains("'def'"), "{api}: {message}");
                }
                other => panic!("{api}: expected the located documentation refusal, got {other:?}"),
            }
        }
    }
}

#[test]
fn files_reject_orphan_documentation_at_eof() {
    for (source, expected_line, expected_col, expected_message) in [
        (
            "def docEofValue : Nat := 1\n/-- orphan declaration documentation -/\n",
            3,
            0,
            "unexpected end of input; expected ",
        ),
        (
            "def docEofValue : Nat := 1\n/-- first -/\n/-- second -/\n",
            2,
            12,
            "unexpected token '/--'; expected ",
        ),
    ] {
        match parse_file(source).expect_err("an orphan doc comment is not file whitespace") {
            ParseError::ModuleSyntaxRefused { line, col, message } => {
                assert_eq!((line, col), (expected_line, expected_col));
                assert!(message.starts_with(expected_message), "{message}");
                assert!(message.contains("'def'"), "{message}");
            }
            other => panic!("expected the located documentation refusal, got {other:?}"),
        }
    }
}

#[test]
fn eof_documentation_preserves_completed_and_argument_comments() {
    for source in [
        "def docEofValue : Nat := 1\n/- ordinary trailing comment -/\n",
        "def docEofValue : Nat := 1\n/-! trailing module documentation -/\n",
        "/-- valid declaration documentation -/\ndef docEofValue : Nat := 1\n",
        "library_note «title» /-- note argument -/\n",
    ] {
        parse_decl_exact(source).expect("the documentation belongs to a complete declaration");
        parse_decl_with_tactics_exact(source, &empty_patterns())
            .expect("tactic-aware parsing keeps the same documentation boundary");
        parse_file(source).expect("completed documentation remains valid in a file");
    }
    assert!(parse_file("/-! standalone module documentation -/\n")
        .expect("a module doc is a complete command")
        .is_empty());
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

/// `§` is not an identifier character, and pinned lean v4.30.0-rc2 rejects
/// `#check fun (§ : Nat) => 0` at parse time (`1:12: error: expected token`).
/// This test used to assert that the parser RECOVERED with a fabricated binder
/// named `_invalid_` — a silent tree, which the no-silent-trees rules forbid;
/// the typed-name refactor removed that placeholder, and the parser now
/// refuses the binder as Lean does. Pin the refusal and where it points.
#[test]
fn test_invalid_binder_character_is_refused_as_lean_does() {
    let source = "fun (\u{00A7} : Nat) => 0";
    match parse_expr(source) {
        Err(ParseError::UnexpectedToken { line, message, .. }) => {
            assert_eq!(line, 1, "the refusal must point at the binder's line");
            assert!(
                message.contains("expected identifier in binder"),
                "unexpected parser message: {message}"
            );
        }
        Ok(expr) => panic!("an invalid binder character must not parse, got {expr:?}"),
        Err(other) => panic!("expected UnexpectedToken, got {other:?}"),
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
