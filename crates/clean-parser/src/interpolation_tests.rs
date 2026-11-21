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
    let parts = parse_interpolation(r#"hello \{x} {name}\n"#).unwrap();
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
        parse_interpolation(r"hello \}").unwrap_err(),
        InterpolationError::InvalidEscape { offset: 7 }
    ));
}

#[test]
fn closing_braces_in_interpolated_literals_follow_lean() {
    for prefix in ["s!", "m!", "f!"] {
        let valid = [prefix, r#""\{.v = {"word"}}}""#].concat();
        let expr = crate::parse_expr(&valid).unwrap();
        let SurfaceExpr::InterpolatedStr { parts, .. } = expr else {
            panic!("expected interpolation: {expr:?}");
        };
        assert!(matches!(
            &parts[..],
            [
                InterpolationPart::Literal(start),
                InterpolationPart::Expr(SurfaceExpr::Lit(_, SurfaceLit::String(word))),
                InterpolationPart::Literal(end)
            ] if start == "{.v = " && word == "word" && end == "}}"
        ));

        let invalid = [prefix, r#""\}""#].concat();
        let error = crate::parse_expr(&invalid).unwrap_err();
        assert!(
            error.to_string().contains("invalid escape sequence"),
            "{error}"
        );
    }
}

fn string_body(expr: &SurfaceExpr) -> &SurfaceExpr {
    let SurfaceExpr::Ascription(_, body, ty) = expr else {
        panic!("s! must have its String ascription: {expr:?}");
    };
    assert!(matches!(ty.as_ref(), SurfaceExpr::Ident(_, name)
        if name.name() == crate::SurfaceName::generated_path("String").name()
            && name.is_global_reference()));
    body
}

fn call_args<'a>(expr: &'a SurfaceExpr, canonical: &str) -> &'a [crate::SurfaceArg] {
    let SurfaceExpr::App(_, head, args) = expr else {
        panic!("expected {canonical} application: {expr:?}");
    };
    assert!(
        matches!(head.as_ref(), SurfaceExpr::Ident(_, name)
        if name.name() == crate::SurfaceName::generated_path(canonical).name()
            && name.is_global_reference()),
        "expected hygienic {canonical}: {head:?}"
    );
    args
}

#[test]
fn desugar_interpolation_converts_every_chunk_and_appends_left_to_right() {
    let expr = desugar_interpolation(vec![
        InterpolationPart::Literal("Hello ".to_owned()),
        InterpolationPart::Expr(crate::parse_expr("x").expect("lexical hole parses")),
        InterpolationPart::Literal("!".to_owned()),
    ]);
    let outer = call_args(string_body(&expr), "HAppend.hAppend");
    assert_eq!(outer.len(), 2);
    let left = call_args(&outer[0].expr, "HAppend.hAppend");
    assert_eq!(left.len(), 2);
    let first = call_args(&left[0].expr, "ToString.toString");
    let middle = call_args(&left[1].expr, "ToString.toString");
    let last = call_args(&outer[1].expr, "ToString.toString");
    assert_eq!(first.len(), 1);
    assert_eq!(middle.len(), 1);
    assert_eq!(last.len(), 1);
    assert!(matches!(&first[0].expr, SurfaceExpr::Lit(_, SurfaceLit::String(s)) if s == "Hello "));
    assert!(matches!(&middle[0].expr, SurfaceExpr::Ident(_, name)
        if name.name() == crate::SurfaceName::generated_path("x").name()
            && !name.is_global_reference()));
    assert!(matches!(&last[0].expr, SurfaceExpr::Lit(_, SurfaceLit::String(s)) if s == "!"));
}

#[test]
fn desugar_interpolation_skips_empty_literals_without_converting_an_empty_prefix() {
    let expr = desugar_interpolation(vec![
        InterpolationPart::Literal(String::new()),
        InterpolationPart::Expr(SurfaceExpr::ident("x")),
        InterpolationPart::Literal(String::new()),
    ]);
    let args = call_args(string_body(&expr), "ToString.toString");
    assert_eq!(args.len(), 1);
    assert!(matches!(&args[0].expr, SurfaceExpr::Ident(_, name)
        if name.name() == crate::SurfaceName::generated_path("x").name()));
}

#[test]
fn desugar_prefixed_interpolation_wraps_format_and_message_data() {
    let format_expr =
        desugar_prefixed_interpolation(InterpolatedStringKind::Format, "x = {x}").unwrap();
    assert!(matches!(format_expr, SurfaceExpr::App(_, ref func, _)
        if matches!(func.as_ref(), SurfaceExpr::Ident(_, name) if (name).name() == crate::SurfaceName::generated_path("Format.append").name())));

    // `m!` is Lean's own expansion: `((toMessageData "a " ++ toMessageData x
    // ++ …) : MessageData)`, left-associative, empty literals skipped, names
    // hygienic in namespace `Lean` (`Lean/Message.lean`, the `m!` macro).
    let message_expr =
        desugar_prefixed_interpolation(InterpolatedStringKind::MessageData, "a {x}{y}").unwrap();
    let SurfaceExpr::Ascription(_, body, ty) = &message_expr else {
        panic!("m! must be ascribed `Lean.MessageData`: {message_expr:?}");
    };
    assert!(matches!(ty.as_ref(), SurfaceExpr::Ident(_, name)
        if name.name() == crate::SurfaceName::generated_path("Lean.MessageData").name()));
    let head_is = |e: &SurfaceExpr, want: &str| {
        matches!(e, SurfaceExpr::App(_, func, _)
        if matches!(func.as_ref(), SurfaceExpr::Ident(_, name)
            if name.name() == crate::SurfaceName::generated_path(want).name()))
    };
    // ((toMessageData "a " ++ toMessageData x) ++ toMessageData y)
    let SurfaceExpr::App(_, _, outer) = body.as_ref() else {
        panic!("m! body must be an application: {body:?}");
    };
    assert!(head_is(body, "HAppend.hAppend"), "joined with ++: {body:?}");
    assert!(
        head_is(&outer[0].expr, "HAppend.hAppend"),
        "LEFT-associative: {body:?}"
    );
    assert!(
        head_is(&outer[1].expr, "Lean.ToMessageData.toMessageData"),
        "{body:?}"
    );
    // An empty m! is `toMessageData ""`.
    let empty = desugar_prefixed_interpolation(InterpolatedStringKind::MessageData, "").unwrap();
    assert!(
        matches!(&empty, SurfaceExpr::Ascription(_, b, _) if head_is(b, "Lean.ToMessageData.toMessageData"))
    );
}

#[test]
fn parse_interpolation_empty_input() {
    let parts = parse_interpolation("").unwrap();
    assert!(parts.is_empty());
}

#[test]
fn desugar_interpolation_empty_parts_converts_the_empty_string() {
    for parts in [vec![], vec![InterpolationPart::Literal(String::new())]] {
        let expr = desugar_interpolation(parts);
        let args = call_args(string_body(&expr), "ToString.toString");
        assert_eq!(args.len(), 1);
        assert!(
            matches!(&args[0].expr, SurfaceExpr::Lit(_, SurfaceLit::String(s)) if s.is_empty())
        );
    }
}

#[test]
fn desugar_interpolation_single_literal_is_converted() {
    let expr = desugar_interpolation(vec![InterpolationPart::Literal("hello".to_owned())]);
    let args = call_args(string_body(&expr), "ToString.toString");
    assert_eq!(args.len(), 1);
    assert!(matches!(&args[0].expr, SurfaceExpr::Lit(_, SurfaceLit::String(s)) if s == "hello"));
}

#[test]
fn desugar_interpolation_single_expr_wraps_in_canonical_to_string() {
    let expr = desugar_interpolation(vec![InterpolationPart::Expr(SurfaceExpr::nat(42))]);
    let args = call_args(string_body(&expr), "ToString.toString");
    assert_eq!(args.len(), 1);
    assert!(matches!(
        &args[0].expr,
        SurfaceExpr::Lit(_, SurfaceLit::Nat(42))
    ));
}

#[test]
fn desugar_prefixed_interpolation_s_empty() {
    let expr = desugar_prefixed_interpolation(InterpolatedStringKind::String, "").unwrap();
    let args = call_args(string_body(&expr), "ToString.toString");
    assert_eq!(args.len(), 1);
    assert!(matches!(&args[0].expr, SurfaceExpr::Lit(_, SurfaceLit::String(s)) if s.is_empty()));
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
                matches!(func.as_ref(), SurfaceExpr::Ident(_, n) if (n).name() == crate::SurfaceName::generated_path("Format.text").name()),
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
