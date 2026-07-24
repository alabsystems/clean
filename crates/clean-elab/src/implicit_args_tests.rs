// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for implicit argument insertion.

use clean_kernel::{BinderData, BinderInfo, Environment, Expr, ExprKind, Name};

use crate::error::ElabError;
use crate::implicit_args::{
    analyze_function_type, count_explicit_params, count_leading_implicits, insert_implicits,
    is_implicit_binder_info, make_implicit_meta, make_instance_meta, resolve_named_arg,
    should_insert_strict, ImplicitConfig,
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

/// `{A}{B}{C} -> A -> B -> C`
fn mk_three_implicit_type() -> Expr {
    Expr::pi(
        bd(BinderInfo::Implicit),
        Expr::type_(),
        Expr::pi(
            bd(BinderInfo::Implicit),
            Expr::type_(),
            Expr::pi(
                bd(BinderInfo::Implicit),
                Expr::type_(),
                Expr::pi(
                    bd(BinderInfo::Default),
                    Expr::bvar(2),
                    Expr::pi(bd(BinderInfo::Default), Expr::bvar(2), Expr::bvar(2)),
                ),
            ),
        ),
    )
}

// ── is_implicit_binder_info ──────────────────────────────────────────

#[test]
fn test_is_implicit_binder_info_default_false() {
    assert!(!is_implicit_binder_info(BinderInfo::Default));
}

#[test]
fn test_is_implicit_binder_info_implicit_true() {
    assert!(is_implicit_binder_info(BinderInfo::Implicit));
}

#[test]
fn test_is_implicit_binder_info_strict_true() {
    assert!(is_implicit_binder_info(BinderInfo::StrictImplicit));
}

#[test]
fn test_is_implicit_binder_info_inst_true() {
    assert!(is_implicit_binder_info(BinderInfo::InstImplicit));
}

// ── count_leading_implicits ──────────────────────────────────────────

#[test]
fn test_count_leading_implicits_none() {
    assert_eq!(count_leading_implicits(&mk_simple_arrow()), 0);
}

#[test]
fn test_count_leading_implicits_one() {
    assert_eq!(count_leading_implicits(&mk_id_type()), 1);
}

#[test]
fn test_count_leading_implicits_two() {
    assert_eq!(count_leading_implicits(&mk_two_implicit_type()), 2);
}

#[test]
fn test_count_leading_implicits_three() {
    assert_eq!(count_leading_implicits(&mk_three_implicit_type()), 3);
}

#[test]
fn test_count_leading_implicits_instance() {
    assert_eq!(count_leading_implicits(&mk_instance_type()), 1);
}

#[test]
fn test_count_leading_implicits_strict() {
    assert_eq!(count_leading_implicits(&mk_strict_type()), 1);
}

#[test]
fn test_count_leading_implicits_non_pi() {
    assert_eq!(count_leading_implicits(&Expr::const_str("Nat")), 0);
}

// ── count_explicit_params ────────────────────────────────────────────

#[test]
fn test_count_explicit_params_id() {
    assert_eq!(count_explicit_params(&mk_id_type()), 1);
}

#[test]
fn test_count_explicit_params_two_implicit() {
    assert_eq!(count_explicit_params(&mk_two_implicit_type()), 2);
}

#[test]
fn test_count_explicit_params_simple_arrow() {
    assert_eq!(count_explicit_params(&mk_simple_arrow()), 1);
}

// ── should_insert_strict ─────────────────────────────────────────────

#[test]
fn test_should_insert_strict_with_remaining_args() {
    assert!(should_insert_strict(bd(BinderInfo::StrictImplicit), 1));
}

#[test]
fn test_should_insert_strict_no_remaining_args() {
    assert!(!should_insert_strict(bd(BinderInfo::StrictImplicit), 0));
}

#[test]
fn test_should_insert_strict_many_remaining() {
    assert!(should_insert_strict(bd(BinderInfo::StrictImplicit), 5));
}

// ── resolve_named_arg ────────────────────────────────────────────────

#[test]
fn test_resolve_named_arg_found() {
    let name = Name::from_string("alpha");
    let val = Expr::const_str("Nat");
    let named = vec![(name.clone(), val.clone())];
    assert_eq!(*resolve_named_arg(&name, &named).unwrap(), val);
}

#[test]
fn test_resolve_named_arg_not_found() {
    let named: Vec<(Name, Expr)> = vec![];
    assert!(resolve_named_arg(&Name::from_string("beta"), &named).is_none());
}

#[test]
fn test_resolve_named_arg_multiple() {
    let a = Name::from_string("a");
    let b = Name::from_string("b");
    let va = Expr::const_str("Nat");
    let vb = Expr::const_str("Bool");
    let named = vec![(a.clone(), va.clone()), (b.clone(), vb.clone())];
    assert_eq!(*resolve_named_arg(&a, &named).unwrap(), va);
    assert_eq!(*resolve_named_arg(&b, &named).unwrap(), vb);
}

// ── make_implicit_meta / make_instance_meta ──────────────────────────

#[test]
fn test_make_implicit_meta_creates_fvar() {
    let env = Environment::new();
    let mut ctx = MetaCtx::new(&env);
    let meta = make_implicit_meta(&Name::from_string("A"), &Expr::type_(), &mut ctx);
    assert!(meta.is_fvar());
}

#[test]
fn test_make_instance_meta_creates_fvar() {
    let env = Environment::new();
    let mut ctx = MetaCtx::new(&env);
    let meta = make_instance_meta(
        &Name::from_string("inst"),
        &Expr::const_str("Add"),
        &mut ctx,
    );
    assert!(meta.is_fvar());
}

// ── analyze_function_type ────────────────────────────────────────────

#[test]
fn test_analyze_no_implicits() {
    let env = Environment::new();
    let mut ctx = MetaCtx::new(&env);
    let analysis = analyze_function_type(
        &mk_simple_arrow(),
        1,
        &[],
        &ImplicitConfig::default(),
        &mut ctx,
    );
    assert_eq!(analysis.inserted.len(), 0);
    assert_eq!(analysis.remaining_explicit.len(), 1);
    assert_eq!(analysis.instance_goals.len(), 0);
}

#[test]
fn test_analyze_single_implicit() {
    let env = Environment::new();
    let mut ctx = MetaCtx::new(&env);
    let analysis =
        analyze_function_type(&mk_id_type(), 1, &[], &ImplicitConfig::default(), &mut ctx);
    assert_eq!(analysis.inserted.len(), 1);
    assert_eq!(analysis.inserted[0].binder_info, BinderInfo::Implicit);
    assert!(analysis.inserted[0].arg_expr.is_fvar());
}

#[test]
fn test_analyze_two_implicits() {
    let env = Environment::new();
    let mut ctx = MetaCtx::new(&env);
    let analysis = analyze_function_type(
        &mk_two_implicit_type(),
        2,
        &[],
        &ImplicitConfig::default(),
        &mut ctx,
    );
    assert_eq!(analysis.inserted.len(), 2);
    assert_eq!(analysis.inserted[0].binder_info, BinderInfo::Implicit);
    assert_eq!(analysis.inserted[1].binder_info, BinderInfo::Implicit);
}

#[test]
fn test_analyze_instance_implicit() {
    let env = Environment::new();
    let mut ctx = MetaCtx::new(&env);
    let analysis = analyze_function_type(
        &mk_instance_type(),
        1,
        &[],
        &ImplicitConfig::default(),
        &mut ctx,
    );
    assert_eq!(analysis.inserted.len(), 1);
    assert_eq!(analysis.inserted[0].binder_info, BinderInfo::InstImplicit);
    assert_eq!(analysis.instance_goals.len(), 1);
}

#[test]
fn test_analyze_strict_with_explicit_args() {
    let env = Environment::new();
    let mut ctx = MetaCtx::new(&env);
    let analysis = analyze_function_type(
        &mk_strict_type(),
        1,
        &[],
        &ImplicitConfig::default(),
        &mut ctx,
    );
    assert_eq!(analysis.inserted.len(), 1);
    assert_eq!(analysis.inserted[0].binder_info, BinderInfo::StrictImplicit);
}

#[test]
fn test_analyze_strict_without_explicit_args() {
    let env = Environment::new();
    let mut ctx = MetaCtx::new(&env);
    let analysis = analyze_function_type(
        &mk_strict_type(),
        0,
        &[],
        &ImplicitConfig::default(),
        &mut ctx,
    );
    assert_eq!(analysis.inserted.len(), 0);
}

#[test]
fn test_analyze_config_disable_implicit() {
    let env = Environment::new();
    let mut ctx = MetaCtx::new(&env);
    let config = ImplicitConfig {
        insert_implicit: false,
        ..Default::default()
    };
    let analysis = analyze_function_type(&mk_id_type(), 1, &[], &config, &mut ctx);
    assert_eq!(analysis.inserted.len(), 0);
}

#[test]
fn test_analyze_config_disable_instance() {
    let env = Environment::new();
    let mut ctx = MetaCtx::new(&env);
    let config = ImplicitConfig {
        insert_instance: false,
        ..Default::default()
    };
    let analysis = analyze_function_type(&mk_instance_type(), 1, &[], &config, &mut ctx);
    assert_eq!(analysis.inserted.len(), 0);
    assert_eq!(analysis.instance_goals.len(), 0);
}

#[test]
fn test_analyze_config_disable_strict() {
    let env = Environment::new();
    let mut ctx = MetaCtx::new(&env);
    let config = ImplicitConfig {
        insert_strict: false,
        ..Default::default()
    };
    let analysis = analyze_function_type(&mk_strict_type(), 1, &[], &config, &mut ctx);
    assert_eq!(analysis.inserted.len(), 0);
}

// ── insert_implicits ─────────────────────────────────────────────────

#[test]
fn test_insert_implicits_simple_arrow_one_arg() {
    let env = Environment::new();
    let mut ctx = MetaCtx::new(&env);
    let config = ImplicitConfig::default();
    let (result, all_args) = insert_implicits(
        Expr::const_str("succ"),
        &mk_simple_arrow(),
        &[Expr::nat_lit(42)],
        &mut ctx,
        &config,
    )
    .expect("should succeed");
    assert!(result.is_app());
    assert_eq!(all_args.len(), 1);
}

#[test]
fn test_insert_implicits_identity_inserts_meta() {
    let env = Environment::new();
    let mut ctx = MetaCtx::new(&env);
    let config = ImplicitConfig::default();
    let (_result, all_args) = insert_implicits(
        Expr::const_str("id"),
        &mk_id_type(),
        &[Expr::nat_lit(42)],
        &mut ctx,
        &config,
    )
    .expect("should succeed");
    assert_eq!(all_args.len(), 2);
    assert!(all_args[0].is_fvar()); // metavar for implicit A
    assert!(matches!(all_args[1].kind(), ExprKind::Lit(_))); // 42
}

#[test]
fn test_insert_implicits_two_implicits() {
    let env = Environment::new();
    let mut ctx = MetaCtx::new(&env);
    let config = ImplicitConfig::default();
    let (_result, all_args) = insert_implicits(
        Expr::const_str("f"),
        &mk_two_implicit_type(),
        &[Expr::nat_lit(1), Expr::nat_lit(2)],
        &mut ctx,
        &config,
    )
    .expect("should succeed");
    assert_eq!(all_args.len(), 4);
    assert!(all_args[0].is_fvar());
    assert!(all_args[1].is_fvar());
}

#[test]
fn test_insert_implicits_instance() {
    let env = Environment::new();
    let mut ctx = MetaCtx::new(&env);
    let config = ImplicitConfig::default();
    let (_result, all_args) = insert_implicits(
        Expr::const_str("g"),
        &mk_instance_type(),
        &[Expr::nat_lit(0)],
        &mut ctx,
        &config,
    )
    .expect("should succeed");
    assert_eq!(all_args.len(), 2);
    assert!(all_args[0].is_fvar()); // instance meta
}

#[test]
fn test_insert_implicits_strict_with_args() {
    let env = Environment::new();
    let mut ctx = MetaCtx::new(&env);
    let config = ImplicitConfig::default();
    let (_result, all_args) = insert_implicits(
        Expr::const_str("h"),
        &mk_strict_type(),
        &[Expr::nat_lit(7)],
        &mut ctx,
        &config,
    )
    .expect("should succeed");
    assert_eq!(all_args.len(), 2);
    assert!(all_args[0].is_fvar());
}

#[test]
fn test_insert_implicits_strict_no_args() {
    let env = Environment::new();
    let mut ctx = MetaCtx::new(&env);
    let config = ImplicitConfig::default();
    let (result, all_args) = insert_implicits(
        Expr::const_str("h"),
        &mk_strict_type(),
        &[],
        &mut ctx,
        &config,
    )
    .expect("should succeed");
    assert_eq!(all_args.len(), 0);
    assert!(!result.is_app());
}

#[test]
fn test_insert_implicits_no_implicits() {
    let env = Environment::new();
    let mut ctx = MetaCtx::new(&env);
    let config = ImplicitConfig::default();
    let (_, all_args) = insert_implicits(
        Expr::const_str("succ"),
        &mk_simple_arrow(),
        &[Expr::nat_lit(0)],
        &mut ctx,
        &config,
    )
    .expect("should succeed");
    assert_eq!(all_args.len(), 1);
}

#[test]
fn test_insert_implicits_over_application() {
    let env = Environment::new();
    let mut ctx = MetaCtx::new(&env);
    let config = ImplicitConfig::default();
    let result = insert_implicits(
        Expr::const_str("succ"),
        &mk_simple_arrow(),
        &[Expr::nat_lit(0), Expr::nat_lit(1)],
        &mut ctx,
        &config,
    );
    assert!(result.is_err());
    match result {
        Err(ElabError::TooManyArguments { remaining_args, .. }) => {
            assert_eq!(remaining_args, 1);
        }
        _ => panic!("expected TooManyArguments error"),
    }
}

#[test]
fn test_insert_implicits_partial_application() {
    let env = Environment::new();
    let mut ctx = MetaCtx::new(&env);
    let config = ImplicitConfig::default();
    let (_, all_args) = insert_implicits(
        Expr::const_str("f"),
        &mk_two_implicit_type(),
        &[Expr::nat_lit(1)],
        &mut ctx,
        &config,
    )
    .expect("should succeed (partial application)");
    // 2 implicits + 1 explicit = 3 args consumed
    assert_eq!(all_args.len(), 3);
}

#[test]
fn test_insert_implicits_all_disabled() {
    let env = Environment::new();
    let mut ctx = MetaCtx::new(&env);
    let config = ImplicitConfig {
        insert_implicit: false,
        insert_instance: false,
        insert_strict: false,
        max_implicit_depth: 128,
    };
    let (_, all_args) = insert_implicits(
        Expr::const_str("id"),
        &mk_id_type(),
        &[Expr::type_(), Expr::nat_lit(42)],
        &mut ctx,
        &config,
    )
    .expect("should succeed");
    assert_eq!(all_args.len(), 0);
}

// ── ImplicitConfig ───────────────────────────────────────────────────

#[test]
fn test_implicit_config_default() {
    let config = ImplicitConfig::default();
    assert!(config.insert_implicit);
    assert!(config.insert_instance);
    assert!(config.insert_strict);
    assert_eq!(config.max_implicit_depth, 128);
}

#[test]
fn test_implicit_config_max_depth_limit() {
    let env = Environment::new();
    let mut ctx = MetaCtx::new(&env);
    let config = ImplicitConfig {
        max_implicit_depth: 0,
        ..Default::default()
    };
    let (_, all_args) = insert_implicits(
        Expr::const_str("id"),
        &mk_id_type(),
        &[Expr::nat_lit(42)],
        &mut ctx,
        &config,
    )
    .expect("should succeed");
    assert_eq!(all_args.len(), 0);
}
