// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for string interpolation elaboration (s!, m!, f! notation).
//!
//! Parser-level tests (parsing interpolation templates, desugaring to AST)
//! live in `clean_parser::interpolation_tests`. These tests verify the
//! elaboration-side behavior: the bridge from parsed `InterpolatedStr` nodes
//! to kernel expressions, plus utility functions.

use clean_parser::interpolation::InterpolationPart;
use clean_parser::InterpolatedStringKind;
use clean_parser::{SurfaceExpr, SurfaceLit};

use crate::string_interpolation::{
    count_interpolated_exprs, desugar_by_kind, desugar_s_interpolation, is_plain_literal,
    try_extract_plain_text,
};

// ---------------------------------------------------------------------------
// is_plain_literal
// ---------------------------------------------------------------------------

#[test]
fn test_is_plain_literal_all_literals_returns_true() {
    let parts = vec![
        InterpolationPart::Literal("Hello ".to_owned()),
        InterpolationPart::Literal("world".to_owned()),
    ];
    assert!(is_plain_literal(&parts));
}

#[test]
fn test_is_plain_literal_with_expr_returns_false() {
    let parts = vec![
        InterpolationPart::Literal("Hello ".to_owned()),
        InterpolationPart::Expr(SurfaceExpr::ident("name")),
    ];
    assert!(!is_plain_literal(&parts));
}

#[test]
fn test_is_plain_literal_empty_returns_true() {
    let parts: Vec<InterpolationPart> = vec![];
    assert!(is_plain_literal(&parts));
}

#[test]
fn test_is_plain_literal_single_expr_returns_false() {
    let parts = vec![InterpolationPart::Expr(SurfaceExpr::nat(42))];
    assert!(!is_plain_literal(&parts));
}

// ---------------------------------------------------------------------------
// try_extract_plain_text
// ---------------------------------------------------------------------------

#[test]
fn test_try_extract_plain_text_all_literals() {
    let parts = vec![
        InterpolationPart::Literal("Hello ".to_owned()),
        InterpolationPart::Literal("world!".to_owned()),
    ];
    assert_eq!(
        try_extract_plain_text(&parts),
        Some("Hello world!".to_owned())
    );
}

#[test]
fn test_try_extract_plain_text_with_expr_returns_none() {
    let parts = vec![
        InterpolationPart::Literal("x = ".to_owned()),
        InterpolationPart::Expr(SurfaceExpr::ident("x")),
    ];
    assert_eq!(try_extract_plain_text(&parts), None);
}

#[test]
fn test_try_extract_plain_text_empty_returns_empty_string() {
    let parts: Vec<InterpolationPart> = vec![];
    assert_eq!(try_extract_plain_text(&parts), Some(String::new()));
}

#[test]
fn test_try_extract_plain_text_single_literal() {
    let parts = vec![InterpolationPart::Literal("no interpolation".to_owned())];
    assert_eq!(
        try_extract_plain_text(&parts),
        Some("no interpolation".to_owned())
    );
}

// ---------------------------------------------------------------------------
// count_interpolated_exprs
// ---------------------------------------------------------------------------

#[test]
fn test_count_interpolated_exprs_none() {
    let parts = vec![InterpolationPart::Literal("plain".to_owned())];
    assert_eq!(count_interpolated_exprs(&parts), 0);
}

#[test]
fn test_count_interpolated_exprs_mixed() {
    let parts = vec![
        InterpolationPart::Literal("a = ".to_owned()),
        InterpolationPart::Expr(SurfaceExpr::ident("a")),
        InterpolationPart::Literal(", b = ".to_owned()),
        InterpolationPart::Expr(SurfaceExpr::ident("b")),
    ];
    assert_eq!(count_interpolated_exprs(&parts), 2);
}

#[test]
fn test_count_interpolated_exprs_all_exprs() {
    let parts = vec![
        InterpolationPart::Expr(SurfaceExpr::ident("x")),
        InterpolationPart::Expr(SurfaceExpr::ident("y")),
        InterpolationPart::Expr(SurfaceExpr::ident("z")),
    ];
    assert_eq!(count_interpolated_exprs(&parts), 3);
}

#[test]
fn test_count_interpolated_exprs_empty() {
    let parts: Vec<InterpolationPart> = vec![];
    assert_eq!(count_interpolated_exprs(&parts), 0);
}

// ---------------------------------------------------------------------------
// desugar_s_interpolation
// ---------------------------------------------------------------------------

#[test]
fn test_desugar_s_single_literal_passes_through() {
    let parts = vec![InterpolationPart::Literal("hello".to_owned())];
    let expr = desugar_s_interpolation(&parts);
    assert!(
        matches!(&expr, SurfaceExpr::Lit(_, SurfaceLit::String(s)) if s == "hello"),
        "expected string literal, got {expr:?}"
    );
}

#[test]
fn test_desugar_s_single_expr_wraps_to_string() {
    let parts = vec![InterpolationPart::Expr(SurfaceExpr::ident("name"))];
    let expr = desugar_s_interpolation(&parts);
    match &expr {
        SurfaceExpr::App(_, func, args) => {
            assert!(
                matches!(func.as_ref(), SurfaceExpr::Ident(_, n) if n == "toString"),
                "expected toString wrapper, got {func:?}"
            );
            assert_eq!(args.len(), 1);
        }
        other => panic!("expected toString application, got {other:?}"),
    }
}

#[test]
fn test_desugar_s_mixed_produces_string_append_chain() {
    // s!"Hello {name}!" → String.append "Hello " (String.append (toString name) "!")
    let parts = vec![
        InterpolationPart::Literal("Hello ".to_owned()),
        InterpolationPart::Expr(SurfaceExpr::ident("name")),
        InterpolationPart::Literal("!".to_owned()),
    ];
    let expr = desugar_s_interpolation(&parts);
    match &expr {
        SurfaceExpr::App(_, func, _) => {
            assert!(
                matches!(func.as_ref(), SurfaceExpr::Ident(_, n) if n == "String.append"),
                "expected String.append at root, got {func:?}"
            );
        }
        other => panic!("expected String.append chain, got {other:?}"),
    }
}

#[test]
fn test_desugar_s_empty_produces_empty_string() {
    let parts: Vec<InterpolationPart> = vec![];
    let expr = desugar_s_interpolation(&parts);
    assert!(
        matches!(&expr, SurfaceExpr::Lit(_, SurfaceLit::String(s)) if s.is_empty()),
        "expected empty string literal, got {expr:?}"
    );
}

// ---------------------------------------------------------------------------
// desugar_by_kind
// ---------------------------------------------------------------------------

#[test]
fn test_desugar_by_kind_string_matches_s_desugar() {
    let parts = vec![
        InterpolationPart::Literal("x = ".to_owned()),
        InterpolationPart::Expr(SurfaceExpr::ident("x")),
    ];
    let s_result = desugar_s_interpolation(&parts);
    let kind_result = desugar_by_kind(InterpolatedStringKind::String, &parts);
    // Both should produce String.append at root
    assert!(matches!(
        &s_result,
        SurfaceExpr::App(_, func, _)
            if matches!(func.as_ref(), SurfaceExpr::Ident(_, n) if n == "String.append")
    ));
    assert!(matches!(
        &kind_result,
        SurfaceExpr::App(_, func, _)
            if matches!(func.as_ref(), SurfaceExpr::Ident(_, n) if n == "String.append")
    ));
}

#[test]
fn test_desugar_by_kind_format_uses_format_append() {
    let parts = vec![
        InterpolationPart::Literal("x = ".to_owned()),
        InterpolationPart::Expr(SurfaceExpr::ident("x")),
    ];
    let expr = desugar_by_kind(InterpolatedStringKind::Format, &parts);
    match &expr {
        SurfaceExpr::App(_, func, _) => {
            assert!(
                matches!(func.as_ref(), SurfaceExpr::Ident(_, n) if n == "Format.append"),
                "expected Format.append at root, got {func:?}"
            );
        }
        other => panic!("expected Format.append, got {other:?}"),
    }
}

#[test]
fn test_desugar_by_kind_message_data_wraps_in_of_format() {
    let parts = vec![InterpolationPart::Expr(SurfaceExpr::ident("msg"))];
    let expr = desugar_by_kind(InterpolatedStringKind::MessageData, &parts);
    match &expr {
        SurfaceExpr::App(_, func, _) => {
            assert!(
                matches!(func.as_ref(), SurfaceExpr::Ident(_, n) if n == "MessageData.ofFormat"),
                "expected MessageData.ofFormat wrapper, got {func:?}"
            );
        }
        other => panic!("expected MessageData.ofFormat application, got {other:?}"),
    }
}

#[test]
fn test_desugar_by_kind_format_literal_uses_format_text() {
    let parts = vec![InterpolationPart::Literal("plain text".to_owned())];
    let expr = desugar_by_kind(InterpolatedStringKind::Format, &parts);
    // f!"plain text" → Format.text "plain text"
    match &expr {
        SurfaceExpr::App(_, func, args) => {
            assert!(
                matches!(func.as_ref(), SurfaceExpr::Ident(_, n) if n == "Format.text"),
                "expected Format.text, got {func:?}"
            );
            assert_eq!(args.len(), 1);
            assert!(
                matches!(&args[0].expr, SurfaceExpr::Lit(_, SurfaceLit::String(s)) if s == "plain text"),
            );
        }
        other => panic!("expected Format.text application, got {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// InterpolationPart construction and variant coverage
// ---------------------------------------------------------------------------

#[test]
fn test_interpolation_part_literal_variant() {
    let part = InterpolationPart::Literal("test".to_owned());
    assert!(matches!(&part, InterpolationPart::Literal(s) if s == "test"));
}

#[test]
fn test_interpolation_part_expr_variant() {
    let part = InterpolationPart::Expr(SurfaceExpr::nat(42));
    assert!(matches!(&part, InterpolationPart::Expr(_)));
}

// ---------------------------------------------------------------------------
// Adjacent expressions (no literal between them)
// ---------------------------------------------------------------------------

#[test]
fn test_desugar_s_adjacent_exprs() {
    // s!"{a}{b}" → String.append (toString a) (toString b)
    let parts = vec![
        InterpolationPart::Expr(SurfaceExpr::ident("a")),
        InterpolationPart::Expr(SurfaceExpr::ident("b")),
    ];
    let expr = desugar_s_interpolation(&parts);
    match &expr {
        SurfaceExpr::App(_, func, args) => {
            assert!(
                matches!(func.as_ref(), SurfaceExpr::Ident(_, n) if n == "String.append"),
                "expected String.append, got {func:?}"
            );
            assert_eq!(args.len(), 2);
            // Both args should be toString applications
            for (i, arg) in args.iter().enumerate() {
                assert!(
                    matches!(&arg.expr, SurfaceExpr::App(_, inner_func, _)
                        if matches!(inner_func.as_ref(), SurfaceExpr::Ident(_, n) if n == "toString")),
                    "arg {i} should be toString application, got {:?}",
                    arg.expr
                );
            }
        }
        other => panic!("expected String.append of two toString, got {other:?}"),
    }
}
