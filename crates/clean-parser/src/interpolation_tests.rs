// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use crate::interpolation::{
    desugar_interpolation, desugar_prefixed_interpolation, parse_interpolation, InterpolationError,
    InterpolationPart,
};
use crate::lexer::InterpolatedStringKind;
use crate::{SurfaceExpr, SurfaceLit};

#[test]
fn parse_interpolation_handles_literals_exprs_and_escapes() {
    let parts = parse_interpolation(r#"hello \{x\} {name}\n"#).unwrap();
    assert_eq!(parts.len(), 3);
    assert!(matches!(
        &parts[0],
        InterpolationPart::Literal(text) if text == "hello {x} "
    ));
    assert!(matches!(&parts[1], InterpolationPart::Expr(_)));
    assert!(matches!(
        &parts[2],
        InterpolationPart::Literal(text) if text == "\n"
    ));
}

#[test]
fn parse_interpolation_handles_braces_inside_string_and_comments() {
    let string_parts = parse_interpolation(r#"{f "{x}"}"#).unwrap();
    assert_eq!(string_parts.len(), 1);
    assert!(matches!(&string_parts[0], InterpolationPart::Expr(_)));

    let comment_parts = parse_interpolation("{x /- } -/ + y}").unwrap();
    assert_eq!(comment_parts.len(), 1);
    assert!(matches!(&comment_parts[0], InterpolationPart::Expr(_)));
}

#[test]
fn parse_interpolation_reports_errors() {
    assert!(matches!(
        parse_interpolation("hello {name").unwrap_err(),
        InterpolationError::UnclosedBrace { offset: 6 }
    ));
    assert!(matches!(
        parse_interpolation("hello {}").unwrap_err(),
        InterpolationError::EmptyInterpolation { offset: 6 }
    ));
    assert!(matches!(
        parse_interpolation("hello }").unwrap_err(),
        InterpolationError::UnmatchedCloseBrace { offset: 6 }
    ));
}

#[test]
fn desugar_interpolation_uses_string_append_and_to_string() {
    let expr = desugar_interpolation(vec![
        InterpolationPart::Literal("Hello ".to_owned()),
        InterpolationPart::Expr(SurfaceExpr::ident("x")),
        InterpolationPart::Literal("!".to_owned()),
    ]);

    match expr {
        SurfaceExpr::App(_, func, args) => {
            assert!(
                matches!(func.as_ref(), SurfaceExpr::Ident(_, name) if name == "String.append")
            );
            assert_eq!(args.len(), 2);
            assert!(
                matches!(&args[0].expr, SurfaceExpr::Lit(_, SurfaceLit::String(s)) if s == "Hello ")
            );
            match &args[1].expr {
                SurfaceExpr::App(_, inner_func, inner_args) => {
                    assert!(
                        matches!(inner_func.as_ref(), SurfaceExpr::Ident(_, name) if name == "String.append")
                    );
                    assert!(
                        matches!(&inner_args[0].expr, SurfaceExpr::App(_, to_string, _)
                        if matches!(to_string.as_ref(), SurfaceExpr::Ident(_, name) if name == "toString"))
                    );
                    assert!(
                        matches!(&inner_args[1].expr, SurfaceExpr::Lit(_, SurfaceLit::String(s)) if s == "!")
                    );
                }
                other => panic!("expected nested String.append, got {other:?}"),
            }
        }
        other => panic!("expected String.append chain, got {other:?}"),
    }
}

#[test]
fn desugar_prefixed_interpolation_wraps_format_and_message_data() {
    let format_expr =
        desugar_prefixed_interpolation(InterpolatedStringKind::Format, "x = {x}").unwrap();
    assert!(matches!(format_expr, SurfaceExpr::App(_, ref func, _)
        if matches!(func.as_ref(), SurfaceExpr::Ident(_, name) if name == "Format.append")));

    let message_expr =
        desugar_prefixed_interpolation(InterpolatedStringKind::MessageData, "{x}").unwrap();
    assert!(matches!(message_expr, SurfaceExpr::App(_, ref func, _)
        if matches!(func.as_ref(), SurfaceExpr::Ident(_, name) if name == "MessageData.ofFormat")));
}

#[test]
fn parse_interpolation_empty_input() {
    let parts = parse_interpolation("").unwrap();
    assert!(parts.is_empty());
}

#[test]
fn desugar_interpolation_empty_parts_produces_empty_string() {
    let expr = desugar_interpolation(vec![]);
    assert!(
        matches!(&expr, SurfaceExpr::Lit(_, SurfaceLit::String(s)) if s.is_empty()),
        "expected empty string literal, got {expr:?}"
    );
}

#[test]
fn desugar_interpolation_single_literal() {
    let expr = desugar_interpolation(vec![InterpolationPart::Literal("hello".to_owned())]);
    assert!(
        matches!(&expr, SurfaceExpr::Lit(_, SurfaceLit::String(s)) if s == "hello"),
        "expected \"hello\" literal, got {expr:?}"
    );
}

#[test]
fn desugar_interpolation_single_expr_wraps_in_to_string() {
    let expr = desugar_interpolation(vec![InterpolationPart::Expr(SurfaceExpr::nat(42))]);
    match &expr {
        SurfaceExpr::App(_, func, args) => {
            assert!(
                matches!(func.as_ref(), SurfaceExpr::Ident(_, n) if n == "toString"),
                "expected toString, got {func:?}"
            );
            assert_eq!(args.len(), 1);
            assert!(matches!(
                &args[0].expr,
                SurfaceExpr::Lit(_, SurfaceLit::Nat(42))
            ));
        }
        other => panic!("expected toString 42, got {other:?}"),
    }
}

#[test]
fn desugar_prefixed_interpolation_s_empty() {
    let expr = desugar_prefixed_interpolation(InterpolatedStringKind::String, "").unwrap();
    assert!(
        matches!(&expr, SurfaceExpr::Lit(_, SurfaceLit::String(s)) if s.is_empty()),
        "expected empty string, got {expr:?}"
    );
}

#[test]
fn parse_interpolation_adjacent_exprs() {
    // Two expressions side by side: {x}{y}
    let parts = parse_interpolation("{x}{y}").unwrap();
    assert_eq!(parts.len(), 2);
    assert!(matches!(&parts[0], InterpolationPart::Expr(_)));
    assert!(matches!(&parts[1], InterpolationPart::Expr(_)));
}

#[test]
fn desugar_prefixed_interpolation_f_plain_text() {
    let expr =
        desugar_prefixed_interpolation(InterpolatedStringKind::Format, "plain text").unwrap();
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
