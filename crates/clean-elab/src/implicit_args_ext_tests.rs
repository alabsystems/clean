// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for extended implicit argument insertion.

use clean_kernel::{BinderData, BinderInfo, Environment, Expr, ExprKind, Name};

use crate::implicit_args::ImplicitConfig;
use crate::implicit_args_ext::{
    detect_auto_bound_implicits, eta_expand_implicits, insert_implicits_ext, is_type_variable_name,
    is_universe_variable_name, resolve_named_arg_ext, should_insert_strict_ext,
    type_has_unresolved_metas, AutoBoundKind, ExtImplicitConfig, ImplicitTrace, TraceAction,
};
use crate::meta::MetaCtx;

fn bd(info: BinderInfo) -> BinderData {
    BinderData::unrestricted(info)
}

/// `{A : Type} -> A -> A`
fn mk_id_type() -> Expr {
    Expr::pi(
        bd(BinderInfo::Implicit),
        Expr::type_(),
        Expr::pi(bd(BinderInfo::Default), Expr::bvar(0), Expr::bvar(1)),
    )
}

/// `{A : Type} -> {B : Type} -> A -> B -> A`
fn mk_two_implicit_type() -> Expr {
    Expr::pi(
        bd(BinderInfo::Implicit),
        Expr::type_(),
        Expr::pi(
            bd(BinderInfo::Implicit),
            Expr::type_(),
            Expr::pi(
                bd(BinderInfo::Default),
                Expr::bvar(1),
                Expr::pi(bd(BinderInfo::Default), Expr::bvar(1), Expr::bvar(3)),
            ),
        ),
    )
}

/// `[inst : T] -> T -> Nat`
fn mk_instance_type() -> Expr {
    let t = Expr::const_str("T");
    Expr::pi(
        bd(BinderInfo::InstImplicit),
        t.clone(),
        Expr::pi(bd(BinderInfo::Default), t, Expr::const_str("Nat")),
    )
}

/// `{{A : Type}} -> A -> A`
fn mk_strict_type() -> Expr {
    Expr::pi(
        bd(BinderInfo::StrictImplicit),
        Expr::type_(),
        Expr::pi(bd(BinderInfo::Default), Expr::bvar(0), Expr::bvar(1)),
    )
}

/// `Nat -> Nat`
fn mk_simple_arrow() -> Expr {
    Expr::arrow(Expr::const_str("Nat"), Expr::const_str("Nat"))
}

/// `{A : Type} -> [inst : A] -> A -> Nat`
fn mk_mixed_type() -> Expr {
    Expr::pi(
        bd(BinderInfo::Implicit),
        Expr::type_(),
        Expr::pi(
            bd(BinderInfo::InstImplicit),
            Expr::bvar(0),
            Expr::pi(
                bd(BinderInfo::Default),
                Expr::bvar(1),
                Expr::const_str("Nat"),
            ),
        ),
    )
}

fn make_env_and_meta() -> (Environment, ()) {
    (Environment::new(), ())
}

fn default_ext_config() -> ExtImplicitConfig {
    ExtImplicitConfig::default()
}

fn tracing_config() -> ExtImplicitConfig {
    ExtImplicitConfig {
        tracing: true,
        ..Default::default()
    }
}

// ── Universe variable name detection ────────────────────────────────

#[test]
fn test_is_universe_variable_u() {
    assert!(is_universe_variable_name(&Name::from_string("u")));
}

#[test]
fn test_is_universe_variable_v() {
    assert!(is_universe_variable_name(&Name::from_string("v")));
}

#[test]
fn test_is_universe_variable_w() {
    assert!(is_universe_variable_name(&Name::from_string("w")));
}

#[test]
fn test_is_universe_variable_u1() {
    assert!(is_universe_variable_name(&Name::from_string("u1")));
}

#[test]
fn test_is_universe_variable_x_not() {
    assert!(!is_universe_variable_name(&Name::from_string("x")));
}

#[test]
fn test_is_universe_variable_anon_not() {
    assert!(!is_universe_variable_name(&Name::anon()));
}

// ── Type variable name detection ────────────────────────────────────

#[test]
fn test_is_type_variable_alpha() {
    assert!(is_type_variable_name(&Name::from_string("α")));
}

#[test]
fn test_is_type_variable_beta() {
    assert!(is_type_variable_name(&Name::from_string("β")));
}

#[test]
fn test_is_type_variable_single_upper() {
    assert!(is_type_variable_name(&Name::from_string("A")));
}

#[test]
fn test_is_type_variable_lower_not() {
    assert!(!is_type_variable_name(&Name::from_string("x")));
}

#[test]
fn test_is_type_variable_multi_upper_not() {
    // Multi-char uppercase like "AB" is not a type variable.
    assert!(!is_type_variable_name(&Name::from_string("AB")));
}

// ── Auto-bound detection ────────────────────────────────────────────

#[test]
fn test_detect_auto_bound_universe_in_const() {
    let expr = Expr::const_str("u");
    let autos = detect_auto_bound_implicits(&expr);
    assert_eq!(autos.len(), 1);
    assert_eq!(autos[0].1, AutoBoundKind::Universe);
}

#[test]
fn test_detect_auto_bound_type_var_in_app() {
    let expr = Expr::app(Expr::const_str("α"), Expr::const_str("Nat"));
    let autos = detect_auto_bound_implicits(&expr);
    assert!(autos.iter().any(|(_, k)| *k == AutoBoundKind::TypeVar));
}

#[test]
fn test_detect_auto_bound_no_candidates() {
    let expr = Expr::const_str("Nat");
    let autos = detect_auto_bound_implicits(&expr);
    assert!(autos.is_empty());
}

#[test]
fn test_detect_auto_bound_dedup() {
    // `u` appears twice; should deduplicate.
    let expr = Expr::app(Expr::const_str("u"), Expr::const_str("u"));
    let autos = detect_auto_bound_implicits(&expr);
    assert_eq!(autos.len(), 1);
}

// ── Named argument resolution (extended) ────────────────────────────

#[test]
fn test_resolve_named_arg_ext_exact() {
    let named = vec![(Name::from_string("x"), Expr::const_str("val"))];
    let result = resolve_named_arg_ext(&Name::from_string("x"), &named);
    assert!(result.is_some());
}

#[test]
fn test_resolve_named_arg_ext_missing() {
    let named = vec![(Name::from_string("x"), Expr::const_str("val"))];
    let result = resolve_named_arg_ext(&Name::from_string("y"), &named);
    assert!(result.is_none());
}

// ── Strict implicit check (extended) ────────────────────────────────

#[test]
fn test_should_insert_strict_ext_with_explicit() {
    assert!(should_insert_strict_ext(1, 0));
}

#[test]
fn test_should_insert_strict_ext_with_named_only() {
    assert!(should_insert_strict_ext(0, 1));
}

#[test]
fn test_should_insert_strict_ext_none() {
    assert!(!should_insert_strict_ext(0, 0));
}

// ── Type completeness check ─────────────────────────────────────────

#[test]
fn test_type_has_unresolved_metas_fvar() {
    use clean_kernel::FVarId;
    let expr = Expr::fvar(FVarId::new(999));
    assert!(type_has_unresolved_metas(&expr));
}

#[test]
fn test_type_has_unresolved_metas_const() {
    assert!(!type_has_unresolved_metas(&Expr::const_str("Nat")));
}

#[test]
fn test_type_has_unresolved_metas_nested_app() {
    use clean_kernel::FVarId;
    let expr = Expr::app(Expr::const_str("List"), Expr::fvar(FVarId::new(1)));
    assert!(type_has_unresolved_metas(&expr));
}

// ── Trace ───────────────────────────────────────────────────────────

#[test]
fn test_trace_default_empty() {
    let t = ImplicitTrace::default();
    assert!(t.is_empty());
    assert_eq!(t.len(), 0);
}

#[test]
fn test_trace_record() {
    let mut t = ImplicitTrace::default();
    t.record(0, TraceAction::InsertedMeta, BinderInfo::Implicit);
    assert_eq!(t.len(), 1);
    assert_eq!(t.entries[0].action, TraceAction::InsertedMeta);
}

// ── Extended insertion: basic implicit ───────────────────────────────

#[test]
fn test_insert_ext_single_implicit() {
    let env = Environment::new();
    let mut meta_ctx = MetaCtx::new(&env);
    let fn_expr = Expr::const_str("id");
    let fn_type = mk_id_type();
    let config = default_ext_config();

    let result = insert_implicits_ext(
        fn_expr,
        &fn_type,
        &[Expr::const_str("x")],
        &[],
        &[],
        &[],
        &mut meta_ctx,
        &config,
    )
    .expect("should succeed");

    // 1 implicit meta + 1 explicit = 2 args.
    assert_eq!(result.all_args.len(), 2);
}

#[test]
fn test_insert_ext_two_implicits() {
    let env = Environment::new();
    let mut meta_ctx = MetaCtx::new(&env);
    let fn_expr = Expr::const_str("f");
    let fn_type = mk_two_implicit_type();
    let config = default_ext_config();

    let result = insert_implicits_ext(
        fn_expr,
        &fn_type,
        &[Expr::const_str("a"), Expr::const_str("b")],
        &[],
        &[],
        &[],
        &mut meta_ctx,
        &config,
    )
    .expect("should succeed");

    // 2 implicit metas + 2 explicit = 4.
    assert_eq!(result.all_args.len(), 4);
}

// ── Instance implicit ───────────────────────────────────────────────

#[test]
fn test_insert_ext_instance_implicit() {
    let env = Environment::new();
    let mut meta_ctx = MetaCtx::new(&env);
    let fn_expr = Expr::const_str("f");
    let fn_type = mk_instance_type();
    let config = default_ext_config();

    let result = insert_implicits_ext(
        fn_expr,
        &fn_type,
        &[Expr::const_str("x")],
        &[],
        &[],
        &[],
        &mut meta_ctx,
        &config,
    )
    .expect("should succeed");

    assert_eq!(result.instance_goals.len(), 1);
    assert_eq!(result.all_args.len(), 2);
}

// ── Strict implicit ─────────────────────────────────────────────────

#[test]
fn test_insert_ext_strict_with_explicit() {
    let env = Environment::new();
    let mut meta_ctx = MetaCtx::new(&env);
    let fn_expr = Expr::const_str("f");
    let fn_type = mk_strict_type();
    let config = default_ext_config();

    let result = insert_implicits_ext(
        fn_expr,
        &fn_type,
        &[Expr::const_str("x")],
        &[],
        &[],
        &[],
        &mut meta_ctx,
        &config,
    )
    .expect("should succeed");

    // Strict implicit inserted because explicit arg follows.
    assert_eq!(result.all_args.len(), 2);
}

#[test]
fn test_insert_ext_strict_no_explicit_skips() {
    let env = Environment::new();
    let mut meta_ctx = MetaCtx::new(&env);
    let fn_expr = Expr::const_str("f");
    let fn_type = mk_strict_type();
    let config = default_ext_config();

    let result = insert_implicits_ext(
        fn_expr,
        &fn_type,
        &[], // No explicit args.
        &[],
        &[],
        &[],
        &mut meta_ctx,
        &config,
    )
    .expect("should succeed");

    // Strict implicit NOT inserted (no later explicit arg).
    assert_eq!(result.all_args.len(), 0);
}

// ── No implicits ────────────────────────────────────────────────────

#[test]
fn test_insert_ext_no_implicits() {
    let env = Environment::new();
    let mut meta_ctx = MetaCtx::new(&env);
    let fn_expr = Expr::const_str("f");
    let fn_type = mk_simple_arrow();
    let config = default_ext_config();

    let result = insert_implicits_ext(
        fn_expr,
        &fn_type,
        &[Expr::const_str("x")],
        &[],
        &[],
        &[],
        &mut meta_ctx,
        &config,
    )
    .expect("should succeed");

    assert_eq!(result.all_args.len(), 1);
    assert!(result.instance_goals.is_empty());
}

// ── Mixed binder kinds ──────────────────────────────────────────────

#[test]
fn test_insert_ext_mixed_implicit_and_instance() {
    let env = Environment::new();
    let mut meta_ctx = MetaCtx::new(&env);
    let fn_expr = Expr::const_str("f");
    let fn_type = mk_mixed_type();
    let config = default_ext_config();

    let result = insert_implicits_ext(
        fn_expr,
        &fn_type,
        &[Expr::const_str("x")],
        &[],
        &[],
        &[],
        &mut meta_ctx,
        &config,
    )
    .expect("should succeed");

    // 1 implicit + 1 instance + 1 explicit = 3.
    assert_eq!(result.all_args.len(), 3);
    assert_eq!(result.instance_goals.len(), 1);
}

// ── Too many arguments ──────────────────────────────────────────────

#[test]
fn test_insert_ext_too_many_args() {
    let env = Environment::new();
    let mut meta_ctx = MetaCtx::new(&env);
    let fn_expr = Expr::const_str("f");
    let fn_type = mk_simple_arrow(); // Nat -> Nat
    let config = default_ext_config();

    let result = insert_implicits_ext(
        fn_expr,
        &fn_type,
        &[Expr::const_str("a"), Expr::const_str("b")],
        &[],
        &[],
        &[],
        &mut meta_ctx,
        &config,
    );

    assert!(result.is_err());
}

// ── Tracing ─────────────────────────────────────────────────────────

#[test]
fn test_insert_ext_tracing_records() {
    let env = Environment::new();
    let mut meta_ctx = MetaCtx::new(&env);
    let fn_expr = Expr::const_str("id");
    let fn_type = mk_id_type();
    let config = tracing_config();

    let result = insert_implicits_ext(
        fn_expr,
        &fn_type,
        &[Expr::const_str("x")],
        &[],
        &[],
        &[],
        &mut meta_ctx,
        &config,
    )
    .expect("should succeed");

    assert!(!result.trace.is_empty());
    // First entry should be implicit meta insertion.
    assert_eq!(result.trace.entries[0].action, TraceAction::InsertedMeta);
    // Second should be explicit consumed.
    assert_eq!(
        result.trace.entries[1].action,
        TraceAction::ExplicitConsumed
    );
}

#[test]
fn test_insert_ext_tracing_disabled_empty() {
    let env = Environment::new();
    let mut meta_ctx = MetaCtx::new(&env);
    let fn_expr = Expr::const_str("id");
    let fn_type = mk_id_type();
    let config = default_ext_config();

    let result = insert_implicits_ext(
        fn_expr,
        &fn_type,
        &[Expr::const_str("x")],
        &[],
        &[],
        &[],
        &mut meta_ctx,
        &config,
    )
    .expect("should succeed");

    assert!(result.trace.is_empty());
}

// ── Eta expansion ───────────────────────────────────────────────────

#[test]
fn test_eta_expand_no_implicits() {
    let env = Environment::new();
    let mut meta_ctx = MetaCtx::new(&env);
    let fn_expr = Expr::const_str("f");
    let fn_type = mk_simple_arrow();

    let expanded = eta_expand_implicits(&fn_expr, &fn_type, &mut meta_ctx);
    // No implicit binders — should return unchanged.
    assert_eq!(format!("{expanded:?}"), format!("{fn_expr:?}"));
}

#[test]
fn test_eta_expand_single_implicit() {
    let env = Environment::new();
    let mut meta_ctx = MetaCtx::new(&env);
    let fn_expr = Expr::const_str("id");
    let fn_type = mk_id_type();

    let expanded = eta_expand_implicits(&fn_expr, &fn_type, &mut meta_ctx);
    // Should produce `fun {A : Type} => id A`.
    match expanded.kind() {
        ExprKind::Lam(bd, _, _) => {
            assert_eq!(bd.info, BinderInfo::Implicit);
        }
        other => panic!("expected Lam, got {other:?}"),
    }
}

#[test]
fn test_eta_expand_two_implicits() {
    let env = Environment::new();
    let mut meta_ctx = MetaCtx::new(&env);
    let fn_expr = Expr::const_str("f");
    let fn_type = mk_two_implicit_type();

    let expanded = eta_expand_implicits(&fn_expr, &fn_type, &mut meta_ctx);
    // Should produce `fun {A} {B} => f A B` (two nested lambdas).
    match expanded.kind() {
        ExprKind::Lam(bd1, _, inner) => {
            assert_eq!(bd1.info, BinderInfo::Implicit);
            match inner.kind() {
                ExprKind::Lam(bd2, _, _) => {
                    assert_eq!(bd2.info, BinderInfo::Implicit);
                }
                other => panic!("expected inner Lam, got {other:?}"),
            }
        }
        other => panic!("expected Lam, got {other:?}"),
    }
}

// ── All implicits (no explicit) ─────────────────────────────────────

#[test]
fn test_insert_ext_all_implicit_no_explicit() {
    let env = Environment::new();
    let mut meta_ctx = MetaCtx::new(&env);
    let fn_expr = Expr::const_str("f");
    // {A : Type} -> {B : Type} -> Nat (all implicit, result is Nat)
    let fn_type = Expr::pi(
        bd(BinderInfo::Implicit),
        Expr::type_(),
        Expr::pi(
            bd(BinderInfo::Implicit),
            Expr::type_(),
            Expr::const_str("Nat"),
        ),
    );
    let config = default_ext_config();

    let result = insert_implicits_ext(
        fn_expr,
        &fn_type,
        &[], // No explicit args.
        &[],
        &[],
        &[],
        &mut meta_ctx,
        &config,
    )
    .expect("should succeed");

    assert_eq!(result.all_args.len(), 2);
}

// ── Config disabling ────────────────────────────────────────────────

#[test]
fn test_insert_ext_implicit_disabled() {
    let env = Environment::new();
    let mut meta_ctx = MetaCtx::new(&env);
    let fn_expr = Expr::const_str("id");
    let fn_type = mk_id_type();
    let config = ExtImplicitConfig {
        base: ImplicitConfig {
            insert_implicit: false,
            ..ImplicitConfig::default()
        },
        ..Default::default()
    };

    let result = insert_implicits_ext(
        fn_expr,
        &fn_type,
        &[Expr::const_str("x")],
        &[],
        &[],
        &[],
        &mut meta_ctx,
        &config,
    )
    .expect("should succeed");

    // Implicit disabled — stops at implicit binder.
    assert_eq!(result.all_args.len(), 0);
}

#[test]
fn test_insert_ext_instance_disabled() {
    let env = Environment::new();
    let mut meta_ctx = MetaCtx::new(&env);
    let fn_expr = Expr::const_str("f");
    let fn_type = mk_instance_type();
    let config = ExtImplicitConfig {
        base: ImplicitConfig {
            insert_instance: false,
            ..ImplicitConfig::default()
        },
        ..Default::default()
    };

    let result = insert_implicits_ext(
        fn_expr,
        &fn_type,
        &[Expr::const_str("x")],
        &[],
        &[],
        &[],
        &mut meta_ctx,
        &config,
    )
    .expect("should succeed");

    // Instance disabled — stops at instance binder.
    assert_eq!(result.all_args.len(), 0);
    assert!(result.instance_goals.is_empty());
}

// ── Strict implicit with tracing ────────────────────────────────────

#[test]
fn test_strict_skip_traced() {
    let env = Environment::new();
    let mut meta_ctx = MetaCtx::new(&env);
    let fn_expr = Expr::const_str("f");
    let fn_type = mk_strict_type();
    let config = tracing_config();

    let result = insert_implicits_ext(
        fn_expr,
        &fn_type,
        &[],
        &[],
        &[],
        &[],
        &mut meta_ctx,
        &config,
    )
    .expect("should succeed");

    assert_eq!(result.all_args.len(), 0);
    assert!(!result.trace.is_empty());
    assert_eq!(result.trace.entries[0].action, TraceAction::StrictSkipped);
}

// ── Instance tracing ────────────────────────────────────────────────

#[test]
fn test_instance_traced() {
    let env = Environment::new();
    let mut meta_ctx = MetaCtx::new(&env);
    let fn_expr = Expr::const_str("f");
    let fn_type = mk_instance_type();
    let config = tracing_config();

    let result = insert_implicits_ext(
        fn_expr,
        &fn_type,
        &[Expr::const_str("x")],
        &[],
        &[],
        &[],
        &mut meta_ctx,
        &config,
    )
    .expect("should succeed");

    assert!(result
        .trace
        .entries
        .iter()
        .any(|e| e.action == TraceAction::InsertedInstance));
}
