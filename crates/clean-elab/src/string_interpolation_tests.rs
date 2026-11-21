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

fn string_body(expr: &SurfaceExpr) -> &SurfaceExpr {
    let SurfaceExpr::Ascription(_, body, ty) = expr else {
        panic!("s! must retain the String ascription: {expr:?}");
    };
    assert!(matches!(ty.as_ref(), SurfaceExpr::Ident(_, name)
        if name.name() == &clean_kernel::Name::from_string("String") && name.is_global_reference()));
    body
}

fn converted_argument(expr: &SurfaceExpr) -> &SurfaceExpr {
    let SurfaceExpr::App(_, head, args) = expr else {
        panic!("expected canonical ToString application: {expr:?}");
    };
    assert!(matches!(head.as_ref(), SurfaceExpr::Ident(_, name)
        if name.name() == &clean_kernel::Name::from_string("ToString.toString")
            && name.is_global_reference()));
    assert_eq!(args.len(), 1);
    &args[0].expr
}

// ---------------------------------------------------------------------------
// desugar_s_interpolation
// ---------------------------------------------------------------------------

#[test]
fn test_desugar_s_single_literal_is_converted() {
    let parts = vec![InterpolationPart::Literal("hello".to_owned())];
    let expr = desugar_s_interpolation(&parts);
    assert!(matches!(converted_argument(string_body(&expr)),
        SurfaceExpr::Lit(_, SurfaceLit::String(s)) if s == "hello"));
}

#[test]
fn test_desugar_s_single_expr_wraps_canonical_to_string() {
    let parts = vec![InterpolationPart::Expr(
        clean_parser::parse_expr("name").expect("lexical hole parses"),
    )];
    let expr = desugar_s_interpolation(&parts);
    assert!(
        matches!(converted_argument(string_body(&expr)), SurfaceExpr::Ident(_, name)
        if name.name() == &clean_kernel::Name::from_string("name") && !name.is_global_reference())
    );
}

#[test]
fn test_desugar_s_mixed_produces_ascribed_happend() {
    let parts = vec![
        InterpolationPart::Literal("Hello ".to_owned()),
        InterpolationPart::Expr(SurfaceExpr::ident("name")),
        InterpolationPart::Literal("!".to_owned()),
    ];
    let expr = desugar_s_interpolation(&parts);
    assert!(matches!(string_body(&expr), SurfaceExpr::App(_, head, _)
        if matches!(head.as_ref(), SurfaceExpr::Ident(_, name)
            if name.name() == &clean_kernel::Name::from_string("HAppend.hAppend") && name.is_global_reference())));
}

#[test]
fn test_desugar_s_empty_converts_empty_string() {
    let expr = desugar_s_interpolation(&[]);
    assert!(matches!(converted_argument(string_body(&expr)),
        SurfaceExpr::Lit(_, SurfaceLit::String(s)) if s.is_empty()));
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
    for expr in [s_result, kind_result] {
        assert!(matches!(string_body(&expr), SurfaceExpr::App(_, head, _)
            if matches!(head.as_ref(), SurfaceExpr::Ident(_, name)
                if name.name() == &clean_kernel::Name::from_string("HAppend.hAppend") && name.is_global_reference())));
    }
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
                matches!(func.as_ref(), SurfaceExpr::Ident(_, n) if n.name() == &clean_kernel::Name::from_string("Format.append")),
                "expected Format.append at root, got {func:?}"
            );
        }
        other => panic!("expected Format.append, got {other:?}"),
    }
}

#[test]
fn test_desugar_by_kind_message_data_is_leans_expansion() {
    // `m!"{msg}"` is `(toMessageData msg : MessageData)` in Lean's macro, with
    // the names hygienic in namespace `Lean`.
    let parts = vec![InterpolationPart::Expr(SurfaceExpr::ident("msg"))];
    let expr = desugar_by_kind(InterpolatedStringKind::MessageData, &parts);
    match &expr {
        SurfaceExpr::Ascription(_, body, ty) => {
            assert!(
                matches!(ty.as_ref(), SurfaceExpr::Ident(_, n) if n.name() == &clean_kernel::Name::from_string("Lean.MessageData")),
                "expected the `Lean.MessageData` ascription, got {ty:?}"
            );
            assert!(
                matches!(body.as_ref(), SurfaceExpr::App(_, func, _)
                    if matches!(func.as_ref(), SurfaceExpr::Ident(_, n) if n.name() == &clean_kernel::Name::from_string("Lean.ToMessageData.toMessageData"))),
                "expected `Lean.ToMessageData.toMessageData msg`, got {body:?}"
            );
        }
        other => {
            panic!("expected an ascribed `Lean.ToMessageData.toMessageData` chain, got {other:?}")
        }
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
                matches!(func.as_ref(), SurfaceExpr::Ident(_, n) if n.name() == &clean_kernel::Name::from_string("Format.text")),
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
    let parts = vec![
        InterpolationPart::Expr(SurfaceExpr::ident("a")),
        InterpolationPart::Expr(SurfaceExpr::ident("b")),
    ];
    let expr = desugar_s_interpolation(&parts);
    let SurfaceExpr::App(_, head, args) = string_body(&expr) else {
        panic!("expected HAppend application: {expr:?}");
    };
    assert!(matches!(head.as_ref(), SurfaceExpr::Ident(_, name)
        if name.name() == &clean_kernel::Name::from_string("HAppend.hAppend") && name.is_global_reference()));
    assert_eq!(args.len(), 2);
    for (arg, expected) in args.iter().zip(["a", "b"]) {
        assert!(
            matches!(converted_argument(&arg.expr), SurfaceExpr::Ident(_, name)
            if name.name() == &clean_kernel::Name::from_string(expected))
        );
    }
}

fn register_interpolation_source(
    env: &mut clean_kernel::Environment,
    source: &str,
    expected_theorems: &[&str],
) {
    let mut file = crate::FileContext::new();
    let declarations = clean_parser::parse_file(source).expect("regression source parses");
    assert!(!declarations.is_empty());
    for declaration in declarations {
        let declaration = crate::preprocess_decl_with_context(&declaration, &mut file);
        let result = crate::elaborate_decl_and_register_with_context(env, &declaration, &mut file)
            .unwrap_or_else(|error| panic!("{source}\n{error:?}"));
        assert!(
            result.source_error_message().is_none(),
            "{source}\n{result:?}"
        );
        let mut pending = vec![&result];
        while let Some(leaf) = pending.pop() {
            match leaf {
                crate::ElabResult::Multiple(leaves) => pending.extend(leaves),
                crate::ElabResult::Diagnosed { result, .. } => pending.push(result),
                crate::ElabResult::Failed { .. } => panic!("{source}\n{leaf:?}"),
                _ => {}
            }
        }
    }
    assert!(!expected_theorems.is_empty());
    for name in expected_theorems {
        let info = env
            .get_const(&clean_kernel::Name::from_string(name))
            .unwrap_or_else(|| panic!("expected theorem {name} was not registered"));
        assert_eq!(info.kind, clean_kernel::ConstantKind::Theorem, "{name}");
    }
}

#[test]
fn test_s_interpolation_without_a_root_to_string_constant() {
    use clean_kernel::{Environment, Name};
    let mut env = Environment::with_prelude();
    // Official Init exports an alias, not a root definition. Keep this
    // distinction visible instead of letting the builtin stand-in hide it.
    assert!(env.forget_decl(&Name::from_string("toString")));
    assert!(env.get_const(&Name::from_string("toString")).is_none());
    env.register_export_alias(
        Name::from_string("toString"),
        Name::from_string("ToString.toString"),
    );
    register_interpolation_source(
        &mut env,
        r#"
def aliasControl : String := toString 7
theorem aliasControl_eq : aliasControl = "7" := rfl
def rendered (n : Nat) (b : Bool) : String := s!"n={n};bool={b}"
theorem rendered_eq : rendered 42 true = "n=42;bool=true" := rfl
def renderedBool : String := s!"and={true && false};or={false || true}"
theorem renderedBool_eq : renderedBool = "and=false;or=true" := rfl
"#,
        &["aliasControl_eq", "rendered_eq", "renderedBool_eq"],
    );
}

#[test]
fn test_s_interpolation_does_not_capture_local_or_namespace_to_string() {
    register_interpolation_source(
        &mut clean_kernel::Environment::with_prelude(),
        r#"
namespace InterpolationShadow
def toString (_ : Nat) : String := "NAMESPACE"
def rendered : String := s!"value={7}"
theorem rendered_eq : rendered = "value=7" := rfl
end InterpolationShadow
def localInterpolation (toString : Nat → String) : String := s!"value={7}"
theorem localInterpolation_eq : localInterpolation (fun _ => "LOCAL") = "value=7" := rfl
"#,
        &["InterpolationShadow.rendered_eq", "localInterpolation_eq"],
    );
}

#[test]
fn test_s_interpolation_converts_literal_and_empty_chunks_through_the_instance() {
    register_interpolation_source(
        &mut clean_kernel::Environment::with_prelude(),
        r#"
instance (priority := 2000) bracketStrings : ToString String where
  toString s := String.append "[" (String.append s "]")
def literalInterpolation : String := s!"text"
def emptyInterpolation : String := s!""
def mixedInterpolation : String := s!"a{"b"}"
theorem literalInterpolation_eq : literalInterpolation = "[text]" := rfl
theorem emptyInterpolation_eq : emptyInterpolation = "[]" := rfl
theorem mixedInterpolation_eq : mixedInterpolation = "[a][b]" := rfl
"#,
        &[
            "literalInterpolation_eq",
            "emptyInterpolation_eq",
            "mixedInterpolation_eq",
        ],
    );
}

#[test]
fn test_s_interpolation_uses_left_associated_happend_instance() {
    register_interpolation_source(
        &mut clean_kernel::Environment::with_prelude(),
        r#"
instance (priority := 2000) bracketAppend : HAppend String String String where
  hAppend a b := String.append "(" (String.append a (String.append "|" (String.append b ")")))
def groupedInterpolation : String := s!"{"a"}{"b"}{"c"}"
theorem groupedInterpolation_eq : groupedInterpolation = "((a|b)|c)" := rfl
"#,
        &["groupedInterpolation_eq"],
    );
}

#[test]
fn test_s_interpolation_keeps_missing_instance_refusal() {
    let mut env = clean_kernel::Environment::with_prelude();
    let mut file = crate::FileContext::new();
    let declarations = clean_parser::parse_file("structure NoInterpolationInstance where\n  n : Nat\ndef rejected (x : NoInterpolationInstance) : String := s!\"{x}\"\n")
        .expect("negative source parses");
    assert_eq!(declarations.len(), 2);
    let first = crate::preprocess_decl_with_context(&declarations[0], &mut file);
    crate::elaborate_decl_and_register_with_context(&mut env, &first, &mut file)
        .expect("structure is well-formed");
    let rejected = crate::preprocess_decl_with_context(&declarations[1], &mut file);
    let error = crate::elaborate_decl_and_register_with_context(&mut env, &rejected, &mut file)
        .expect_err("interpolation requires an actual ToString instance");
    let text = error.to_string();
    assert!(text.contains("ToString"), "{text}");
    assert!(!text.contains("Unknown identifier"), "{text}");
}
