// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! String interpolation end-to-end parser tests.

use super::*;

/// s!"hello {name}" parses to InterpolatedStr with 2 parts: literal "hello " + expr name
#[test]
fn test_parse_s_interpolation_lit_and_expr() {
    use crate::interpolation::InterpolationPart;
    use crate::lexer::InterpolatedStringKind;

    let expr = Parser::parse_expr(r#"s!"hello {name}""#).unwrap();
    match &expr {
        SurfaceExpr::InterpolatedStr { kind, parts, .. } => {
            assert_eq!(*kind, InterpolatedStringKind::String);
            assert_eq!(parts.len(), 2);
            assert!(
                matches!(&parts[0], InterpolationPart::Literal(s) if s == "hello "),
                "expected literal \"hello \", got {:?}",
                parts[0]
            );
            assert!(
                matches!(&parts[1], InterpolationPart::Expr(SurfaceExpr::Ident(_, n)) if n == "name"),
                "expected expr name, got {:?}",
                parts[1]
            );
        }
        other => panic!("expected InterpolatedStr, got {other:?}"),
    }
}

/// s!"no interp" parses to InterpolatedStr with 1 literal part
#[test]
fn test_parse_s_interpolation_plain_text() {
    use crate::interpolation::InterpolationPart;
    use crate::lexer::InterpolatedStringKind;

    let expr = Parser::parse_expr(r#"s!"no interp""#).unwrap();
    match &expr {
        SurfaceExpr::InterpolatedStr { kind, parts, .. } => {
            assert_eq!(*kind, InterpolatedStringKind::String);
            assert_eq!(parts.len(), 1);
            assert!(matches!(&parts[0], InterpolationPart::Literal(s) if s == "no interp"),);
        }
        other => panic!("expected InterpolatedStr, got {other:?}"),
    }
}

/// s!"{x} and {y}" parses to InterpolatedStr with 3 parts
#[test]
fn test_parse_s_interpolation_multiple_exprs() {
    use crate::interpolation::InterpolationPart;
    use crate::lexer::InterpolatedStringKind;

    let expr = Parser::parse_expr(r#"s!"{x} and {y}""#).unwrap();
    match &expr {
        SurfaceExpr::InterpolatedStr { kind, parts, .. } => {
            assert_eq!(*kind, InterpolatedStringKind::String);
            assert_eq!(parts.len(), 3);
            assert!(
                matches!(&parts[0], InterpolationPart::Expr(SurfaceExpr::Ident(_, n)) if n == "x")
            );
            assert!(matches!(&parts[1], InterpolationPart::Literal(s) if s == " and "));
            assert!(
                matches!(&parts[2], InterpolationPart::Expr(SurfaceExpr::Ident(_, n)) if n == "y")
            );
        }
        other => panic!("expected InterpolatedStr, got {other:?}"),
    }
}

/// s!"" (empty string) parses to InterpolatedStr with 0 parts
#[test]
fn test_parse_s_interpolation_empty() {
    use crate::lexer::InterpolatedStringKind;

    let expr = Parser::parse_expr(r#"s!"""#).unwrap();
    match &expr {
        SurfaceExpr::InterpolatedStr { kind, parts, .. } => {
            assert_eq!(*kind, InterpolatedStringKind::String);
            assert!(parts.is_empty(), "expected 0 parts, got {}", parts.len());
        }
        other => panic!("expected InterpolatedStr, got {other:?}"),
    }
}

/// s!"{42}" parses to InterpolatedStr with 1 expr part (nat literal 42)
#[test]
fn test_parse_s_interpolation_nat_expr() {
    use crate::interpolation::InterpolationPart;
    use crate::lexer::InterpolatedStringKind;

    let expr = Parser::parse_expr(r#"s!"{42}""#).unwrap();
    match &expr {
        SurfaceExpr::InterpolatedStr { kind, parts, .. } => {
            assert_eq!(*kind, InterpolatedStringKind::String);
            assert_eq!(parts.len(), 1);
            assert!(
                matches!(
                    &parts[0],
                    InterpolationPart::Expr(SurfaceExpr::Lit(_, SurfaceLit::Nat(42)))
                ),
                "expected Nat(42), got {:?}",
                parts[0]
            );
        }
        other => panic!("expected InterpolatedStr, got {other:?}"),
    }
}

/// s!"hello" (no interpolation braces) parses to InterpolatedStr with 1 literal
#[test]
fn test_parse_s_interpolation_hello_no_braces() {
    use crate::interpolation::InterpolationPart;
    use crate::lexer::InterpolatedStringKind;

    let expr = Parser::parse_expr(r#"s!"hello""#).unwrap();
    match &expr {
        SurfaceExpr::InterpolatedStr { kind, parts, .. } => {
            assert_eq!(*kind, InterpolatedStringKind::String);
            assert_eq!(parts.len(), 1);
            assert!(matches!(&parts[0], InterpolationPart::Literal(s) if s == "hello"));
        }
        other => panic!("expected InterpolatedStr, got {other:?}"),
    }
}

/// s!"literal \{braces\}" parses with escaped braces as literal text
#[test]
fn test_parse_s_interpolation_escaped_braces() {
    use crate::interpolation::InterpolationPart;
    use crate::lexer::InterpolatedStringKind;

    let expr = Parser::parse_expr(r#"s!"literal \{braces\}""#).unwrap();
    match &expr {
        SurfaceExpr::InterpolatedStr { kind, parts, .. } => {
            assert_eq!(*kind, InterpolatedStringKind::String);
            assert_eq!(parts.len(), 1);
            assert!(
                matches!(&parts[0], InterpolationPart::Literal(s) if s == "literal {braces}"),
                "expected literal with braces, got {:?}",
                parts[0]
            );
        }
        other => panic!("expected InterpolatedStr, got {other:?}"),
    }
}

/// m!"..." parses to InterpolatedStr with MessageData kind
#[test]
fn test_parse_m_interpolation() {
    use crate::interpolation::InterpolationPart;
    use crate::lexer::InterpolatedStringKind;

    let expr = Parser::parse_expr(r#"m!"error: {msg}""#).unwrap();
    match &expr {
        SurfaceExpr::InterpolatedStr { kind, parts, .. } => {
            assert_eq!(*kind, InterpolatedStringKind::MessageData);
            assert_eq!(parts.len(), 2);
            assert!(matches!(&parts[0], InterpolationPart::Literal(s) if s == "error: "));
            assert!(
                matches!(&parts[1], InterpolationPart::Expr(SurfaceExpr::Ident(_, n)) if n == "msg")
            );
        }
        other => panic!("expected InterpolatedStr, got {other:?}"),
    }
}

/// f!"..." parses to InterpolatedStr with Format kind
#[test]
fn test_parse_f_interpolation() {
    use crate::interpolation::InterpolationPart;
    use crate::lexer::InterpolatedStringKind;

    let expr = Parser::parse_expr(r#"f!"x = {x}""#).unwrap();
    match &expr {
        SurfaceExpr::InterpolatedStr { kind, parts, .. } => {
            assert_eq!(*kind, InterpolatedStringKind::Format);
            assert_eq!(parts.len(), 2);
            assert!(matches!(&parts[0], InterpolationPart::Literal(s) if s == "x = "));
            assert!(
                matches!(&parts[1], InterpolationPart::Expr(SurfaceExpr::Ident(_, n)) if n == "x")
            );
        }
        other => panic!("expected InterpolatedStr, got {other:?}"),
    }
}

/// s!"x = {x}" — simple interpolation with text before and after expression
#[test]
fn test_parse_s_interpolation_x_eq_x() {
    use crate::interpolation::InterpolationPart;
    use crate::lexer::InterpolatedStringKind;

    let expr = Parser::parse_expr(r#"s!"x = {x}""#).unwrap();
    match &expr {
        SurfaceExpr::InterpolatedStr { kind, parts, .. } => {
            assert_eq!(*kind, InterpolatedStringKind::String);
            assert_eq!(parts.len(), 2);
            assert!(matches!(&parts[0], InterpolationPart::Literal(s) if s == "x = "));
            assert!(
                matches!(&parts[1], InterpolationPart::Expr(SurfaceExpr::Ident(_, n)) if n == "x")
            );
        }
        other => panic!("expected InterpolatedStr, got {other:?}"),
    }
}

/// s!"{a} + {b} = {a + b}" — complex expressions inside interpolation braces
#[test]
fn test_parse_s_interpolation_arithmetic_exprs() {
    use crate::interpolation::InterpolationPart;
    use crate::lexer::InterpolatedStringKind;

    let expr = Parser::parse_expr(r#"s!"{a} + {b} = {a + b}""#).unwrap();
    match &expr {
        SurfaceExpr::InterpolatedStr { kind, parts, .. } => {
            assert_eq!(*kind, InterpolatedStringKind::String);
            assert_eq!(parts.len(), 5);
            // {a}
            assert!(
                matches!(&parts[0], InterpolationPart::Expr(SurfaceExpr::Ident(_, n)) if n == "a"),
                "expected ident a, got {:?}",
                parts[0]
            );
            // " + "
            assert!(matches!(&parts[1], InterpolationPart::Literal(s) if s == " + "));
            // {b}
            assert!(
                matches!(&parts[2], InterpolationPart::Expr(SurfaceExpr::Ident(_, n)) if n == "b"),
                "expected ident b, got {:?}",
                parts[2]
            );
            // " = "
            assert!(matches!(&parts[3], InterpolationPart::Literal(s) if s == " = "));
            // {a + b} — should parse as App(App(Ident("+"), a), b) or similar
            assert!(
                matches!(&parts[4], InterpolationPart::Expr(SurfaceExpr::App(..))),
                "expected application expr, got {:?}",
                parts[4]
            );
        }
        other => panic!("expected InterpolatedStr, got {other:?}"),
    }
}

/// Nested interpolation: s!"outer {s!\"inner {x}\"}" is not directly supported
/// at the lexer level (inner quotes terminate the outer string), but we test that
/// s!"..." can contain braced expressions that happen to produce InterpolatedStr AST
/// nodes when the inner expression is parsed.
#[test]
fn test_parse_s_interpolation_nested_braces() {
    use crate::interpolation::InterpolationPart;
    use crate::lexer::InterpolatedStringKind;

    // s!"{f {a := x}}" — nested braces (not nested interpolation, but function
    // application). A struct literal `{a := x}` is used rather than `{x}`
    // because Brick 1 rejects finite-set braces `{x}` loudly; the point of this
    // test — that the interpolation lexer tracks a nested `{`/`}` inside the
    // interpolated expression without terminating the string early — is
    // preserved by any balanced brace form.
    let expr = Parser::parse_expr(r#"s!"{f {a := x}}""#).unwrap();
    match &expr {
        SurfaceExpr::InterpolatedStr { kind, parts, .. } => {
            assert_eq!(*kind, InterpolatedStringKind::String);
            assert_eq!(parts.len(), 1);
            // The inner expr should be a function application: f applied to the
            // struct literal `{a := x}`.
            assert!(
                matches!(&parts[0], InterpolationPart::Expr(_)),
                "expected expression, got {:?}",
                parts[0]
            );
        }
        other => panic!("expected InterpolatedStr, got {other:?}"),
    }
}
