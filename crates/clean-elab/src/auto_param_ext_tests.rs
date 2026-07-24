// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for extended auto-bound parameter handling.

use std::collections::HashSet;

use clean_kernel::expr::BinderInfo;
use clean_kernel::level::Level;
use clean_kernel::name::Name;
use clean_kernel::Expr;

use super::auto_param_ext::*;

// =============================================================================
// Helpers
// =============================================================================

fn name(s: &str) -> Name {
    Name::from_string(s)
}

fn mk_param(n: &str, ty: Expr, kind: ParamKind) -> ParamDesc {
    ParamDesc {
        name: name(n),
        type_expr: ty,
        kind,
        default_value: None,
        is_auto_bound: false,
        is_out_param: false,
    }
}

fn mk_auto_param(n: &str, ty: Expr, kind: ParamKind) -> ParamDesc {
    ParamDesc {
        name: name(n),
        type_expr: ty,
        kind,
        default_value: None,
        is_auto_bound: true,
        is_out_param: false,
    }
}

fn mk_param_with_default(n: &str, ty: Expr, kind: ParamKind, dv: Expr) -> ParamDesc {
    ParamDesc {
        name: name(n),
        type_expr: ty,
        kind,
        default_value: Some(dv),
        is_auto_bound: false,
        is_out_param: false,
    }
}

// =============================================================================
// ParamKind / BinderInfo conversion
// =============================================================================

#[test]
fn test_param_kind_from_binder_info_default() {
    assert_eq!(ParamKind::from(BinderInfo::Default), ParamKind::Explicit);
}

#[test]
fn test_param_kind_from_binder_info_implicit() {
    assert_eq!(ParamKind::from(BinderInfo::Implicit), ParamKind::Implicit);
}

#[test]
fn test_param_kind_from_binder_info_strict() {
    assert_eq!(
        ParamKind::from(BinderInfo::StrictImplicit),
        ParamKind::StrictImplicit
    );
}

#[test]
fn test_param_kind_from_binder_info_inst() {
    assert_eq!(
        ParamKind::from(BinderInfo::InstImplicit),
        ParamKind::InstanceImplicit
    );
}

#[test]
fn test_binder_info_from_param_kind_roundtrip() {
    for pk in [
        ParamKind::Explicit,
        ParamKind::Implicit,
        ParamKind::StrictImplicit,
        ParamKind::InstanceImplicit,
    ] {
        let bi: BinderInfo = pk.into();
        assert_eq!(ParamKind::from(bi), pk);
    }
}

// =============================================================================
// Instance implicit detection
// =============================================================================

#[test]
fn test_is_known_typeclass_positive() {
    assert!(is_known_typeclass("Decidable"));
    assert!(is_known_typeclass("BEq"));
    assert!(is_known_typeclass("Monad"));
    assert!(is_known_typeclass("Inhabited"));
}

#[test]
fn test_is_known_typeclass_negative() {
    assert!(!is_known_typeclass("Nat"));
    assert!(!is_known_typeclass("MyCustomType"));
    assert!(!is_known_typeclass(""));
}

#[test]
fn test_detect_instance_implicits_simple_app() {
    // BEq α
    let alpha = Expr::const_str("α");
    let beq = Expr::app(Expr::const_str("BEq"), alpha);
    let results = detect_instance_implicits(&beq);
    assert_eq!(results.len(), 1);
    assert_eq!(results[0].0, "BEq");
    assert_eq!(results[0].1.len(), 1);
}

#[test]
fn test_detect_instance_implicits_nested_pi() {
    // {α : Type} → [BEq α] → α → Bool
    let alpha = Expr::const_str("α");
    let beq_alpha = Expr::app(Expr::const_str("BEq"), alpha.clone());
    let body = Expr::pi(
        BinderInfo::InstImplicit,
        beq_alpha.clone(),
        Expr::const_str("Bool"),
    );
    let outer = Expr::pi(BinderInfo::Implicit, Expr::type_(), body);
    let results = detect_instance_implicits(&outer);
    assert!(!results.is_empty());
    assert!(results.iter().any(|(n, _)| n == "BEq"));
}

#[test]
fn test_detect_instance_implicits_no_typeclass() {
    let e = Expr::app(Expr::const_str("List"), Expr::const_str("Nat"));
    let results = detect_instance_implicits(&e);
    assert!(results.is_empty());
}

#[test]
fn test_detect_instance_implicits_multiple_classes() {
    // (BEq α, Hashable α)
    let alpha = Expr::const_str("α");
    let beq = Expr::app(Expr::const_str("BEq"), alpha.clone());
    let hash = Expr::app(Expr::const_str("Hashable"), alpha);
    // Combine in a Pi: [BEq α] → [Hashable α] → result
    let inner = Expr::pi(BinderInfo::InstImplicit, hash, Expr::const_str("Unit"));
    let outer = Expr::pi(BinderInfo::InstImplicit, beq, inner);
    let results = detect_instance_implicits(&outer);
    assert!(results.len() >= 2);
}

// =============================================================================
// Strict implicit handling
// =============================================================================

#[test]
fn test_should_insert_strict_when_later_explicit_exists() {
    let params = vec![
        mk_param("x", Expr::type_(), ParamKind::StrictImplicit),
        mk_param("y", Expr::const_str("Nat"), ParamKind::Explicit),
    ];
    assert!(should_insert_strict_implicit(&params, 0));
}

#[test]
fn test_should_not_insert_strict_when_no_later_explicit() {
    let params = vec![
        mk_param("x", Expr::type_(), ParamKind::StrictImplicit),
        mk_param("y", Expr::type_(), ParamKind::Implicit),
    ];
    assert!(!should_insert_strict_implicit(&params, 0));
}

#[test]
fn test_strict_implicit_trailing_position() {
    let params = vec![
        mk_param("a", Expr::const_str("Nat"), ParamKind::Explicit),
        mk_param("x", Expr::type_(), ParamKind::StrictImplicit),
    ];
    assert!(!should_insert_strict_implicit(&params, 1));
}

// =============================================================================
// Default value parameters
// =============================================================================

#[test]
fn test_resolve_defaults_unsupplied() {
    let params = vec![
        mk_param("x", Expr::const_str("Nat"), ParamKind::Explicit),
        mk_param_with_default(
            "y",
            Expr::const_str("Nat"),
            ParamKind::Explicit,
            Expr::const_str("0"),
        ),
    ];
    let supplied = HashSet::from([0]);
    let defaults = resolve_defaults(&params, &supplied);
    assert_eq!(defaults.len(), 1);
    assert_eq!(defaults[0].0, 1);
}

#[test]
fn test_resolve_defaults_all_supplied() {
    let params = vec![mk_param_with_default(
        "x",
        Expr::const_str("Nat"),
        ParamKind::Explicit,
        Expr::const_str("0"),
    )];
    let supplied = HashSet::from([0]);
    let defaults = resolve_defaults(&params, &supplied);
    assert!(defaults.is_empty());
}

#[test]
fn test_resolve_defaults_none_have_default() {
    let params = vec![mk_param("x", Expr::const_str("Nat"), ParamKind::Explicit)];
    let supplied = HashSet::new();
    let defaults = resolve_defaults(&params, &supplied);
    assert!(defaults.is_empty());
}

#[test]
fn test_validate_defaults_valid_backward_ref() {
    // y defaults to x: valid since x comes first
    let params = vec![
        mk_param("x", Expr::const_str("Nat"), ParamKind::Explicit),
        mk_param_with_default(
            "y",
            Expr::const_str("Nat"),
            ParamKind::Explicit,
            Expr::const_str("x"),
        ),
    ];
    assert!(validate_defaults(&params).is_ok());
}

#[test]
fn test_validate_defaults_invalid_forward_ref() {
    // x defaults to y: invalid since y comes after
    let params = vec![
        mk_param_with_default(
            "x",
            Expr::const_str("Nat"),
            ParamKind::Explicit,
            Expr::const_str("y"),
        ),
        mk_param("y", Expr::const_str("Nat"), ParamKind::Explicit),
    ];
    let err = validate_defaults(&params);
    assert!(err.is_err());
    let msg = format!("{}", err.unwrap_err());
    assert!(msg.contains("unbound"));
}

// =============================================================================
// Named argument resolution
// =============================================================================

#[test]
fn test_resolve_named_args_basic() {
    let params = vec![
        mk_param("x", Expr::const_str("Nat"), ParamKind::Explicit),
        mk_param("y", Expr::const_str("Bool"), ParamKind::Explicit),
    ];
    let named = vec![(name("y"), Expr::const_str("true"))];
    let result = resolve_named_args(&params, &named).expect("should resolve");
    assert_eq!(result.len(), 1);
    assert_eq!(result[0].param_index, 1);
}

#[test]
fn test_resolve_named_args_unknown() {
    let params = vec![mk_param("x", Expr::const_str("Nat"), ParamKind::Explicit)];
    let named = vec![(name("z"), Expr::const_str("0"))];
    let err = resolve_named_args(&params, &named);
    assert!(err.is_err());
    let msg = format!("{}", err.unwrap_err());
    assert!(msg.contains("unknown"));
}

#[test]
fn test_resolve_named_args_duplicate() {
    let params = vec![mk_param("x", Expr::const_str("Nat"), ParamKind::Explicit)];
    let named = vec![
        (name("x"), Expr::const_str("1")),
        (name("x"), Expr::const_str("2")),
    ];
    let err = resolve_named_args(&params, &named);
    assert!(err.is_err());
    let msg = format!("{}", err.unwrap_err());
    assert!(msg.contains("duplicate"));
}

#[test]
fn test_resolve_named_args_empty() {
    let params = vec![mk_param("x", Expr::const_str("Nat"), ParamKind::Explicit)];
    let named: Vec<(Name, Expr)> = vec![];
    let result = resolve_named_args(&params, &named).expect("should resolve");
    assert!(result.is_empty());
}

// =============================================================================
// Out-parameter detection
// =============================================================================

#[test]
fn test_detect_out_params_basic() {
    // (α : Type) → List α → α
    let params = vec![
        mk_param("α", Expr::type_(), ParamKind::Implicit),
        mk_param(
            "l",
            Expr::app(Expr::const_str("List"), Expr::const_str("α")),
            ParamKind::Explicit,
        ),
    ];
    // Return type references α
    let ret = Expr::const_str("α");
    let out = detect_out_params(&params, &ret);
    assert_eq!(out, vec![0]);
}

#[test]
fn test_detect_out_params_none() {
    let params = vec![mk_param("x", Expr::const_str("Nat"), ParamKind::Explicit)];
    let ret = Expr::const_str("Bool");
    let out = detect_out_params(&params, &ret);
    assert!(out.is_empty());
}

#[test]
fn test_detect_out_params_multiple() {
    let params = vec![
        mk_param("α", Expr::type_(), ParamKind::Implicit),
        mk_param("β", Expr::type_(), ParamKind::Implicit),
        mk_param("f", Expr::const_str("Fn"), ParamKind::Explicit),
    ];
    // Return type: Prod α β
    let ret = Expr::app(
        Expr::app(Expr::const_str("Prod"), Expr::const_str("α")),
        Expr::const_str("β"),
    );
    let out = detect_out_params(&params, &ret);
    assert_eq!(out, vec![0, 1]);
}

// =============================================================================
// Universe auto-binding
// =============================================================================

#[test]
fn test_collect_universe_params_from_sort() {
    // Sort (u + 1)
    let u = Level::Param(name("u"));
    let succ_u = Level::succ(u);
    let expr = Expr::sort(succ_u);
    let params = collect_universe_params(&expr, &[]);
    assert_eq!(params.len(), 1);
    assert_eq!(params[0], name("u"));
}

#[test]
fn test_collect_universe_params_skips_declared() {
    let u = Level::Param(name("u"));
    let expr = Expr::sort(u);
    let declared = vec![name("u")];
    let params = collect_universe_params(&expr, &declared);
    assert!(params.is_empty());
}

#[test]
fn test_collect_universe_params_multiple() {
    // Sort (max u v)
    let u = Level::Param(name("u"));
    let v = Level::Param(name("v"));
    let max_uv = Level::max(u, v);
    let expr = Expr::sort(max_uv);
    let params = collect_universe_params(&expr, &[]);
    assert_eq!(params.len(), 2);
    assert!(params.contains(&name("u")));
    assert!(params.contains(&name("v")));
}

#[test]
fn test_collect_universe_params_zero_level() {
    let expr = Expr::prop(); // Sort 0
    let params = collect_universe_params(&expr, &[]);
    assert!(params.is_empty());
}

#[test]
fn test_collect_universe_params_from_const_levels() {
    // Const "List" [u]
    let u = Level::Param(name("u"));
    let expr = Expr::const_str_levels("List", vec![u]);
    let params = collect_universe_params(&expr, &[]);
    assert_eq!(params.len(), 1);
    assert_eq!(params[0], name("u"));
}

// =============================================================================
// Parameter ordering validation
// =============================================================================

#[test]
fn test_validate_ordering_correct_implicit_before_explicit() {
    let params = vec![
        mk_param("α", Expr::type_(), ParamKind::Implicit),
        mk_param("x", Expr::const_str("α"), ParamKind::Explicit),
    ];
    assert!(validate_param_ordering(&params).is_ok());
}

#[test]
fn test_validate_ordering_instance_before_explicit() {
    let params = vec![
        mk_param("α", Expr::type_(), ParamKind::Implicit),
        mk_param("inst", Expr::const_str("BEq"), ParamKind::InstanceImplicit),
        mk_param("x", Expr::const_str("α"), ParamKind::Explicit),
    ];
    assert!(validate_param_ordering(&params).is_ok());
}

#[test]
fn test_validate_ordering_violation_implicit_after_explicit() {
    let params = vec![
        mk_param("x", Expr::const_str("Nat"), ParamKind::Explicit),
        mk_param("α", Expr::type_(), ParamKind::Implicit),
    ];
    let err = validate_param_ordering(&params);
    assert!(err.is_err());
}

#[test]
fn test_validate_ordering_auto_bound_after_explicit_is_ok() {
    // Auto-bound implicits are allowed after explicit (they get reordered)
    let params = vec![
        mk_param("x", Expr::const_str("Nat"), ParamKind::Explicit),
        mk_auto_param("α", Expr::type_(), ParamKind::Implicit),
    ];
    assert!(validate_param_ordering(&params).is_ok());
}

#[test]
fn test_validate_ordering_empty() {
    let params: Vec<ParamDesc> = vec![];
    assert!(validate_param_ordering(&params).is_ok());
}

// =============================================================================
// Statistics tracking
// =============================================================================

#[test]
fn test_stats_default_zero() {
    let stats = AutoParamStats::new();
    assert_eq!(stats.total_insertions(), 0);
}

#[test]
fn test_stats_total_insertions() {
    let stats = AutoParamStats {
        implicit_type_params: 2,
        instance_implicits: 1,
        strict_implicits: 1,
        defaults_applied: 0,
        named_args_resolved: 3,
        out_params_detected: 1,
        universe_params: 2,
    };
    assert_eq!(stats.total_insertions(), 10);
}

#[test]
fn test_stats_merge() {
    let mut a = AutoParamStats {
        implicit_type_params: 1,
        instance_implicits: 2,
        ..Default::default()
    };
    let b = AutoParamStats {
        implicit_type_params: 3,
        instance_implicits: 1,
        universe_params: 4,
        ..Default::default()
    };
    a.merge(&b);
    assert_eq!(a.implicit_type_params, 4);
    assert_eq!(a.instance_implicits, 3);
    assert_eq!(a.universe_params, 4);
}

// =============================================================================
// Full pipeline: process_params
// =============================================================================

#[test]
fn test_process_params_basic() {
    let mut params = vec![
        mk_auto_param("α", Expr::type_(), ParamKind::Implicit),
        mk_param("x", Expr::const_str("α"), ParamKind::Explicit),
    ];
    let named: Vec<(Name, Expr)> = vec![];
    let stats = process_params(&mut params, &named, None).expect("should succeed");
    assert_eq!(stats.implicit_type_params, 1);
}

#[test]
fn test_process_params_with_named_args() {
    let mut params = vec![
        mk_param("x", Expr::const_str("Nat"), ParamKind::Explicit),
        mk_param("y", Expr::const_str("Nat"), ParamKind::Explicit),
    ];
    let named = vec![(name("y"), Expr::const_str("42"))];
    let stats = process_params(&mut params, &named, None).expect("should succeed");
    assert_eq!(stats.named_args_resolved, 1);
}

#[test]
fn test_process_params_with_return_type() {
    let mut params = vec![
        mk_auto_param("α", Expr::type_(), ParamKind::Implicit),
        mk_param("x", Expr::const_str("α"), ParamKind::Explicit),
    ];
    let ret = Expr::const_str("α");
    let named: Vec<(Name, Expr)> = vec![];
    let stats = process_params(&mut params, &named, Some(&ret)).expect("should succeed");
    assert_eq!(stats.out_params_detected, 1);
    assert!(params[0].is_out_param);
}

#[test]
fn test_process_params_ordering_violation() {
    let mut params = vec![
        mk_param("x", Expr::const_str("Nat"), ParamKind::Explicit),
        mk_param("α", Expr::type_(), ParamKind::Implicit),
    ];
    let named: Vec<(Name, Expr)> = vec![];
    let result = process_params(&mut params, &named, None);
    assert!(result.is_err());
}

#[test]
fn test_process_params_instance_implicit_stats() {
    let mut params = vec![
        mk_auto_param("α", Expr::type_(), ParamKind::Implicit),
        mk_param("inst", Expr::const_str("BEq"), ParamKind::InstanceImplicit),
        mk_param("x", Expr::const_str("α"), ParamKind::Explicit),
    ];
    let named: Vec<(Name, Expr)> = vec![];
    let stats = process_params(&mut params, &named, None).expect("should succeed");
    assert_eq!(stats.implicit_type_params, 1);
    assert_eq!(stats.instance_implicits, 1);
}

// =============================================================================
// Error display
// =============================================================================

#[test]
fn test_auto_param_error_display_unknown_named() {
    let err = AutoParamError::UnknownNamedArg {
        name: "z".to_owned(),
    };
    assert_eq!(format!("{err}"), "unknown named argument 'z'");
}

#[test]
fn test_auto_param_error_display_duplicate_named() {
    let err = AutoParamError::DuplicateNamedArg {
        name: "x".to_owned(),
    };
    assert_eq!(format!("{err}"), "duplicate named argument 'x'");
}

#[test]
fn test_auto_param_error_display_ordering() {
    let err = AutoParamError::OrderingViolation {
        reason: "implicit after explicit".to_owned(),
    };
    let msg = format!("{err}");
    assert!(msg.contains("ordering violation"));
}

#[test]
fn test_auto_param_error_display_default_unbound() {
    let err = AutoParamError::DefaultValueUnbound {
        param: "x".to_owned(),
        var: "y".to_owned(),
    };
    let msg = format!("{err}");
    assert!(msg.contains("unbound variable"));
}

#[test]
fn test_auto_param_error_display_cyclic_default() {
    let err = AutoParamError::CyclicDefault {
        param: "x".to_owned(),
    };
    let msg = format!("{err}");
    assert!(msg.contains("cyclic"));
}
