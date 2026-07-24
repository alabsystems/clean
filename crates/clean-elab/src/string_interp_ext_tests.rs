// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for extended string interpolation elaboration (`string_interp_ext`).
//!
//! Covers all `InterpKind` variants, fragment handling, chain building,
//! toString insertion, format spec parsing, validation, and edge cases.

use clean_kernel::name::Name;
use clean_kernel::Expr;

use crate::string_interp_ext::{
    build_message_chain, build_string_append_chain, elaborate_interpolation, insert_to_string,
    parse_format_spec, validate_interpolation, Align, FormatSpec, InterpConfig, InterpFragment,
    InterpKind,
};

// =============================================================================
// InterpKind variant coverage
// =============================================================================

#[test]
fn test_interp_kind_sstring_debug() {
    let kind = InterpKind::SString;
    assert_eq!(format!("{kind:?}"), "SString");
}

#[test]
fn test_interp_kind_message_debug() {
    let kind = InterpKind::Message;
    assert_eq!(format!("{kind:?}"), "Message");
}

#[test]
fn test_interp_kind_format_debug() {
    let kind = InterpKind::Format;
    assert_eq!(format!("{kind:?}"), "Format");
}

#[test]
fn test_interp_kind_custom_debug() {
    let kind = InterpKind::Custom(Name::from_string("Html"));
    let dbg = format!("{kind:?}");
    assert!(dbg.contains("Custom"), "expected Custom variant: {dbg}");
}

#[test]
fn test_interp_kind_equality() {
    assert_eq!(InterpKind::SString, InterpKind::SString);
    assert_ne!(InterpKind::SString, InterpKind::Message);
    assert_ne!(InterpKind::Format, InterpKind::Message);
}

// =============================================================================
// InterpConfig defaults
// =============================================================================

#[test]
fn test_config_default_values() {
    let config = InterpConfig::default();
    assert_eq!(config.max_fragments, 100);
    assert!(config.allow_nested);
    assert!(config.auto_to_string);
}

// =============================================================================
// validate_interpolation
// =============================================================================

#[test]
fn test_validate_empty_fragments_ok() {
    let config = InterpConfig::default();
    validate_interpolation(&[], &config).expect("empty should pass validation");
}

#[test]
fn test_validate_within_limit_ok() {
    let frags: Vec<InterpFragment> = (0..50)
        .map(|i| InterpFragment::Literal(format!("frag{i}")))
        .collect();
    let config = InterpConfig::default();
    validate_interpolation(&frags, &config).expect("50 < 100 should pass");
}

#[test]
fn test_validate_exceeds_limit_error() {
    let frags: Vec<InterpFragment> = (0..5)
        .map(|i| InterpFragment::Literal(format!("f{i}")))
        .collect();
    let config = InterpConfig {
        max_fragments: 3,
        ..Default::default()
    };
    let err = validate_interpolation(&frags, &config).unwrap_err();
    let msg = format!("{err}");
    assert!(
        msg.contains("5 fragments"),
        "error should mention count: {msg}"
    );
}

#[test]
fn test_validate_nested_disallowed_error() {
    let frags = vec![InterpFragment::Nested(vec![InterpFragment::Literal(
        "x".into(),
    )])];
    let config = InterpConfig {
        allow_nested: false,
        ..Default::default()
    };
    let err = validate_interpolation(&frags, &config).unwrap_err();
    let msg = format!("{err}");
    assert!(
        msg.contains("nested"),
        "error should mention nesting: {msg}"
    );
}

#[test]
fn test_validate_nested_allowed_ok() {
    let frags = vec![InterpFragment::Nested(vec![InterpFragment::Literal(
        "x".into(),
    )])];
    let config = InterpConfig {
        allow_nested: true,
        ..Default::default()
    };
    validate_interpolation(&frags, &config).expect("nesting allowed should pass");
}

// =============================================================================
// build_string_append_chain
// =============================================================================

#[test]
fn test_string_chain_empty_produces_empty_lit() {
    let expr = build_string_append_chain(&[]);
    assert!(expr.is_lit(), "empty chain should produce string literal");
}

#[test]
fn test_string_chain_single_literal() {
    let frags = vec![InterpFragment::Literal("hello".into())];
    let expr = build_string_append_chain(&frags);
    assert!(expr.is_lit(), "single literal should be a lit: {expr:?}");
}

#[test]
fn test_string_chain_single_expr() {
    let frags = vec![InterpFragment::Expr(Expr::nat_lit(42))];
    let expr = build_string_append_chain(&frags);
    // Single expr should be returned directly (no append wrapping for single elem)
    assert!(expr.is_lit(), "single expr nat_lit should be lit: {expr:?}");
}

#[test]
fn test_string_chain_two_parts_produces_append() {
    let frags = vec![
        InterpFragment::Literal("x = ".into()),
        InterpFragment::Expr(Expr::nat_lit(42)),
    ];
    let expr = build_string_append_chain(&frags);
    // Should be String.append "x = " 42
    assert!(expr.is_app(), "two-part chain should produce app: {expr:?}");
}

#[test]
fn test_string_chain_three_parts_right_assoc() {
    let frags = vec![
        InterpFragment::Literal("a".into()),
        InterpFragment::Literal("b".into()),
        InterpFragment::Literal("c".into()),
    ];
    let expr = build_string_append_chain(&frags);
    // Adjacent literals should be coalesced by flatten_into push_literal
    // "a" + "b" + "c" -> "abc" (single lit)
    assert!(
        expr.is_lit(),
        "three adjacent literals should coalesce: {expr:?}"
    );
}

#[test]
fn test_string_chain_mixed_not_coalesced() {
    let frags = vec![
        InterpFragment::Literal("a".into()),
        InterpFragment::Expr(Expr::nat_lit(1)),
        InterpFragment::Literal("c".into()),
    ];
    let expr = build_string_append_chain(&frags);
    // "a", nat(1), "c" cannot be coalesced — produces append chain
    assert!(
        expr.is_app(),
        "mixed parts should produce app chain: {expr:?}"
    );
}

#[test]
fn test_string_chain_nested_flattened() {
    let frags = vec![
        InterpFragment::Literal("outer".into()),
        InterpFragment::Nested(vec![InterpFragment::Literal("inner".into())]),
    ];
    let expr = build_string_append_chain(&frags);
    // "outer" + "inner" coalesced to "outerinner" by push_literal
    assert!(expr.is_lit(), "nested literals should coalesce: {expr:?}");
}

// =============================================================================
// build_message_chain
// =============================================================================

#[test]
fn test_message_chain_empty_produces_wrapped_nil() {
    let expr = build_message_chain(&[]);
    // empty_message() = MessageData.ofFormat (Format.nil) → is_app
    assert!(
        expr.is_app(),
        "empty message chain should be MessageData.ofFormat: {expr:?}"
    );
}

#[test]
fn test_message_chain_single_literal() {
    let frags = vec![InterpFragment::Literal("error".into())];
    let expr = build_message_chain(&frags);
    // Should be MessageData.ofFormat (Format.text "error")
    assert!(
        expr.is_app(),
        "single literal message should be app: {expr:?}"
    );
}

#[test]
fn test_message_chain_single_expr() {
    let frags = vec![InterpFragment::Expr(Expr::nat_lit(1))];
    let expr = build_message_chain(&frags);
    // Single expr is returned as-is (since build_message_chain maps Expr to itself)
    assert!(
        expr.is_lit(),
        "single expr message should be the expr itself: {expr:?}"
    );
}

#[test]
fn test_message_chain_multiple_parts() {
    let frags = vec![
        InterpFragment::Literal("error: ".into()),
        InterpFragment::Expr(Expr::nat_lit(42)),
    ];
    let expr = build_message_chain(&frags);
    // Should be MessageData.compose (...) (...)
    assert!(expr.is_app(), "multi-part message should be app: {expr:?}");
}

// =============================================================================
// insert_to_string
// =============================================================================

#[test]
fn test_insert_to_string_wraps_expr() {
    let inner = Expr::nat_lit(42);
    let target = Expr::const_str("String");
    let wrapped = insert_to_string(&inner, &target);
    assert!(wrapped.is_app(), "toString should produce app: {wrapped:?}");
    let head = wrapped.get_app_fn();
    assert!(head.is_const(), "head should be toString const: {head:?}");
}

#[test]
fn test_insert_to_string_preserves_inner() {
    let inner = Expr::str_lit("already a string");
    let target = Expr::const_str("String");
    let wrapped = insert_to_string(&inner, &target);
    // Should still wrap — toString is applied unconditionally at this level
    assert!(wrapped.is_app());
    assert_eq!(wrapped.get_app_num_args(), 1);
}

// =============================================================================
// elaborate_interpolation integration
// =============================================================================

#[test]
fn test_elaborate_sstring_empty() {
    let config = InterpConfig::default();
    let result = elaborate_interpolation(&InterpKind::SString, &[], &config)
        .expect("empty s! should succeed");
    assert_eq!(result.fragments_count, 0);
    assert_eq!(result.to_string_insertions, 0);
    assert!(result.elaborated.is_lit());
}

#[test]
fn test_elaborate_sstring_literal_only() {
    let config = InterpConfig::default();
    let frags = vec![InterpFragment::Literal("hello world".into())];
    let result = elaborate_interpolation(&InterpKind::SString, &frags, &config)
        .expect("literal s! should succeed");
    assert_eq!(result.fragments_count, 1);
    assert_eq!(result.to_string_insertions, 0);
}

#[test]
fn test_elaborate_sstring_with_expr() {
    let config = InterpConfig::default();
    let frags = vec![
        InterpFragment::Literal("value = ".into()),
        InterpFragment::Expr(Expr::nat_lit(42)),
    ];
    let result = elaborate_interpolation(&InterpKind::SString, &frags, &config)
        .expect("s! with expr should succeed");
    assert_eq!(result.fragments_count, 2);
    assert_eq!(result.to_string_insertions, 1);
}

#[test]
fn test_elaborate_sstring_auto_to_string_disabled() {
    let config = InterpConfig {
        auto_to_string: false,
        ..Default::default()
    };
    let frags = vec![InterpFragment::Expr(Expr::nat_lit(42))];
    let result = elaborate_interpolation(&InterpKind::SString, &frags, &config)
        .expect("s! without auto_to_string should succeed");
    assert_eq!(result.to_string_insertions, 0);
}

#[test]
fn test_elaborate_message() {
    let config = InterpConfig::default();
    let frags = vec![InterpFragment::Literal("error".into())];
    let result =
        elaborate_interpolation(&InterpKind::Message, &frags, &config).expect("m! should succeed");
    assert_eq!(result.fragments_count, 1);
    assert_eq!(result.to_string_insertions, 0);
}

#[test]
fn test_elaborate_format() {
    let config = InterpConfig::default();
    let frags = vec![
        InterpFragment::Literal("x = ".into()),
        InterpFragment::Expr(Expr::nat_lit(1)),
    ];
    let result =
        elaborate_interpolation(&InterpKind::Format, &frags, &config).expect("f! should succeed");
    assert_eq!(result.fragments_count, 2);
    assert_eq!(result.to_string_insertions, 0);
}

#[test]
fn test_elaborate_custom() {
    let config = InterpConfig::default();
    let kind = InterpKind::Custom(Name::from_string("Html"));
    let frags = vec![InterpFragment::Literal("<div>".into())];
    let result =
        elaborate_interpolation(&kind, &frags, &config).expect("custom interp should succeed");
    assert_eq!(result.fragments_count, 1);
}

#[test]
fn test_elaborate_exceeds_limit_fails() {
    let config = InterpConfig {
        max_fragments: 2,
        ..Default::default()
    };
    let frags = vec![
        InterpFragment::Literal("a".into()),
        InterpFragment::Literal("b".into()),
        InterpFragment::Literal("c".into()),
    ];
    let err = elaborate_interpolation(&InterpKind::SString, &frags, &config).unwrap_err();
    let msg = format!("{err}");
    assert!(msg.contains("3 fragments"), "should mention count: {msg}");
}

#[test]
fn test_elaborate_nested_rejected_when_disabled() {
    let config = InterpConfig {
        allow_nested: false,
        ..Default::default()
    };
    let frags = vec![InterpFragment::Nested(vec![InterpFragment::Literal(
        "x".into(),
    )])];
    let err = elaborate_interpolation(&InterpKind::SString, &frags, &config).unwrap_err();
    let msg = format!("{err}");
    assert!(msg.contains("nested"), "should reject nesting: {msg}");
}

// =============================================================================
// parse_format_spec
// =============================================================================

#[test]
fn test_parse_format_spec_empty() {
    let spec = parse_format_spec("").expect("empty spec should succeed");
    assert_eq!(spec, FormatSpec::default());
}

#[test]
fn test_parse_format_spec_width_only() {
    let spec = parse_format_spec("10").expect("width-only should succeed");
    assert_eq!(spec.width, Some(10));
    assert_eq!(spec.precision, None);
    assert_eq!(spec.fill, ' ');
    assert_eq!(spec.align, Align::Left);
}

#[test]
fn test_parse_format_spec_left_align() {
    let spec = parse_format_spec("<10").expect("left align should succeed");
    assert_eq!(spec.align, Align::Left);
    assert_eq!(spec.width, Some(10));
}

#[test]
fn test_parse_format_spec_right_align() {
    let spec = parse_format_spec(">5").expect("right align should succeed");
    assert_eq!(spec.align, Align::Right);
    assert_eq!(spec.width, Some(5));
}

#[test]
fn test_parse_format_spec_center_align() {
    let spec = parse_format_spec("^20").expect("center align should succeed");
    assert_eq!(spec.align, Align::Center);
    assert_eq!(spec.width, Some(20));
}

#[test]
fn test_parse_format_spec_fill_and_align() {
    let spec = parse_format_spec("*>10").expect("fill+align should succeed");
    assert_eq!(spec.fill, '*');
    assert_eq!(spec.align, Align::Right);
    assert_eq!(spec.width, Some(10));
}

#[test]
fn test_parse_format_spec_zero_fill() {
    let spec = parse_format_spec("04d").expect("zero-fill should succeed");
    assert_eq!(spec.fill, '0');
    assert_eq!(spec.width, Some(4));
}

#[test]
fn test_parse_format_spec_precision() {
    let spec = parse_format_spec(".2f").expect("precision should succeed");
    assert_eq!(spec.precision, Some(2));
}

#[test]
fn test_parse_format_spec_width_and_precision() {
    let spec = parse_format_spec(">5.2f").expect("width+precision should succeed");
    assert_eq!(spec.align, Align::Right);
    assert_eq!(spec.width, Some(5));
    assert_eq!(spec.precision, Some(2));
}

#[test]
fn test_parse_format_spec_type_only_d() {
    let spec = parse_format_spec("d").expect("type-only should succeed");
    // type char is stripped; result is default
    assert_eq!(spec, FormatSpec::default());
}

#[test]
fn test_parse_format_spec_type_only_x() {
    let spec = parse_format_spec("x").expect("hex type should succeed");
    assert_eq!(spec, FormatSpec::default());
}

#[test]
fn test_parse_format_spec_type_only_s() {
    let spec = parse_format_spec("s").expect("string type should succeed");
    assert_eq!(spec, FormatSpec::default());
}

#[test]
fn test_parse_format_spec_with_colon_prefix() {
    // parse_format_spec strips leading ':'
    let spec = parse_format_spec(":10d").expect("colon prefix should succeed");
    assert_eq!(spec.width, Some(10));
}

#[test]
fn test_parse_format_spec_with_brace_prefix() {
    // parse_format_spec strips "{:" prefix and "}" suffix
    let spec = parse_format_spec("{:>5.2f}").expect("brace-wrapped should succeed");
    assert_eq!(spec.align, Align::Right);
    assert_eq!(spec.width, Some(5));
    assert_eq!(spec.precision, Some(2));
}

#[test]
fn test_parse_format_spec_dot_without_digits_error() {
    let err = parse_format_spec(".").unwrap_err();
    let msg = format!("{err}");
    assert!(
        msg.contains("precision"),
        "should require digits after dot: {msg}"
    );
}

#[test]
fn test_parse_format_spec_full_complex() {
    // fill='=', align='^', width=20, precision=3
    let spec = parse_format_spec("=^20.3f").expect("complex spec should succeed");
    assert_eq!(spec.fill, '=');
    assert_eq!(spec.align, Align::Center);
    assert_eq!(spec.width, Some(20));
    assert_eq!(spec.precision, Some(3));
}

// =============================================================================
// FormatSpec default
// =============================================================================

#[test]
fn test_format_spec_default() {
    let spec = FormatSpec::default();
    assert_eq!(spec.fill, ' ');
    assert_eq!(spec.align, Align::Left);
    assert_eq!(spec.width, None);
    assert_eq!(spec.precision, None);
}

// =============================================================================
// Edge cases
// =============================================================================

#[test]
fn test_string_chain_all_exprs() {
    let frags = vec![
        InterpFragment::Expr(Expr::nat_lit(1)),
        InterpFragment::Expr(Expr::nat_lit(2)),
        InterpFragment::Expr(Expr::nat_lit(3)),
    ];
    let expr = build_string_append_chain(&frags);
    assert!(expr.is_app(), "all-expr chain should be app: {expr:?}");
}

#[test]
fn test_message_chain_nested_flattened() {
    let frags = vec![InterpFragment::Nested(vec![InterpFragment::Literal(
        "nested msg".into(),
    )])];
    let expr = build_message_chain(&frags);
    assert!(
        expr.is_app(),
        "nested message should flatten and produce app: {expr:?}"
    );
}

#[test]
fn test_elaborate_with_nested_fragments() {
    let config = InterpConfig::default();
    let frags = vec![
        InterpFragment::Literal("start ".into()),
        InterpFragment::Nested(vec![
            InterpFragment::Literal("mid ".into()),
            InterpFragment::Expr(Expr::nat_lit(99)),
        ]),
        InterpFragment::Literal(" end".into()),
    ];
    let result = elaborate_interpolation(&InterpKind::SString, &frags, &config)
        .expect("nested fragments should elaborate");
    // count_fragments: "start " = 1, Nested(2 inner) = 1+2 = 3, " end" = 1 => total 5
    assert_eq!(result.fragments_count, 5);
    assert_eq!(result.to_string_insertions, 1); // only the Expr gets toString
}

#[test]
fn test_interp_result_fields_consistent() {
    let config = InterpConfig::default();
    let frags = vec![
        InterpFragment::Expr(Expr::nat_lit(1)),
        InterpFragment::Expr(Expr::nat_lit(2)),
    ];
    let result =
        elaborate_interpolation(&InterpKind::SString, &frags, &config).expect("should succeed");
    assert_eq!(result.fragments_count, 2);
    assert_eq!(result.to_string_insertions, 2);
    assert!(
        result.elaborated.is_app(),
        "two exprs should produce app chain"
    );
}

#[test]
fn test_elaborate_sstring_multiple_exprs_to_string_count() {
    let config = InterpConfig::default();
    let frags = vec![
        InterpFragment::Expr(Expr::nat_lit(1)),
        InterpFragment::Expr(Expr::nat_lit(2)),
        InterpFragment::Expr(Expr::nat_lit(3)),
    ];
    let result = elaborate_interpolation(&InterpKind::SString, &frags, &config)
        .expect("multiple exprs should succeed");
    assert_eq!(result.to_string_insertions, 3);
}

#[test]
fn test_elaborate_format_no_to_string() {
    let config = InterpConfig::default();
    let frags = vec![
        InterpFragment::Expr(Expr::nat_lit(1)),
        InterpFragment::Expr(Expr::nat_lit(2)),
    ];
    let result = elaborate_interpolation(&InterpKind::Format, &frags, &config)
        .expect("format should succeed");
    // Format never inserts toString
    assert_eq!(result.to_string_insertions, 0);
}

#[test]
fn test_elaborate_custom_with_to_string() {
    let config = InterpConfig::default();
    let kind = InterpKind::Custom(Name::from_string("MyInterp"));
    let frags = vec![
        InterpFragment::Expr(Expr::nat_lit(1)),
        InterpFragment::Literal("text".into()),
    ];
    let result = elaborate_interpolation(&kind, &frags, &config).expect("custom should succeed");
    // Custom with auto_to_string inserts toString for expr fragments
    assert_eq!(result.to_string_insertions, 1);
}
