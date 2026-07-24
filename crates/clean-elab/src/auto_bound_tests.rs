// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for auto-bound implicit variable detection and insertion.

use std::collections::HashSet;

use super::auto_bound::*;
use clean_kernel::expr::{BinderInfo, ExprKind};
use clean_kernel::Expr;
use clean_parser::{LevelExpr, SurfaceBinder, SurfaceBinderInfo, SurfaceExpr, UniverseExpr};

// =============================================================================
// Helper
// =============================================================================

fn empty_scope() -> HashSet<String> {
    HashSet::new()
}

fn scope_with(names: &[&str]) -> HashSet<String> {
    names.iter().map(|s| (*s).to_owned()).collect()
}

fn names_of(vars: &[AutoBoundVar]) -> Vec<&str> {
    vars.iter().map(|v| v.name.as_str()).collect()
}

// =============================================================================
// is_type_var_name
// =============================================================================

#[test]
fn test_is_type_var_name_greek_lowercase() {
    assert!(is_type_var_name("\u{03B1}")); // α
    assert!(is_type_var_name("\u{03B2}")); // β
    assert!(is_type_var_name("\u{03B3}")); // γ
    assert!(is_type_var_name("\u{03C9}")); // ω
}

#[test]
fn test_is_type_var_name_greek_uppercase() {
    assert!(is_type_var_name("\u{0391}")); // Α
    assert!(is_type_var_name("\u{03A3}")); // Σ
    assert!(is_type_var_name("\u{03A9}")); // Ω
}

#[test]
fn test_is_type_var_name_multi_char_greek_prefix() {
    // Names starting with a Greek letter are type vars
    assert!(is_type_var_name("\u{03B1}1")); // α1
    assert!(is_type_var_name("\u{03B2}_inner")); // β_inner
}

#[test]
fn test_is_type_var_name_rejects_latin() {
    assert!(!is_type_var_name("x"));
    assert!(!is_type_var_name("foo"));
    assert!(!is_type_var_name("Nat"));
    assert!(!is_type_var_name("T"));
}

#[test]
fn test_is_type_var_name_rejects_dotted() {
    assert!(!is_type_var_name("\u{03B1}.field"));
}

#[test]
fn test_is_type_var_name_rejects_empty() {
    assert!(!is_type_var_name(""));
}

// =============================================================================
// is_universe_var_name
// =============================================================================

#[test]
fn test_is_universe_var_name_single_letters() {
    assert!(is_universe_var_name("u"));
    assert!(is_universe_var_name("v"));
    assert!(is_universe_var_name("w"));
}

#[test]
fn test_is_universe_var_name_indexed() {
    assert!(is_universe_var_name("u_0"));
    assert!(is_universe_var_name("u_1"));
    assert!(is_universe_var_name("v_42"));
    assert!(is_universe_var_name("w_999"));
}

#[test]
fn test_is_universe_var_name_rejects_other_letters() {
    assert!(!is_universe_var_name("x"));
    assert!(!is_universe_var_name("a"));
    assert!(!is_universe_var_name("t"));
}

#[test]
fn test_is_universe_var_name_rejects_long_names() {
    assert!(!is_universe_var_name("universe"));
    assert!(!is_universe_var_name("uv"));
}

#[test]
fn test_is_universe_var_name_rejects_bad_indexed() {
    assert!(!is_universe_var_name("u_"));
    assert!(!is_universe_var_name("u_abc"));
    assert!(!is_universe_var_name("x_1"));
}

#[test]
fn test_is_universe_var_name_rejects_empty() {
    assert!(!is_universe_var_name(""));
}

// =============================================================================
// AutoBoundCollector: type variable detection
// =============================================================================

#[test]
fn test_collect_type_var_from_ident() {
    let mut collector = AutoBoundCollector::new(empty_scope());
    // α used as a free variable
    let expr = SurfaceExpr::ident("\u{03B1}");
    collector.collect_from_expr(&expr);

    let (vars, univs) = collector.finish();
    assert_eq!(vars.len(), 1);
    assert_eq!(vars[0].name, "\u{03B1}");
    assert!(matches!(vars[0].kind, AutoBoundKind::TypeVar { .. }));
    assert_eq!(vars[0].binder_info, BinderInfo::Implicit);
    assert!(univs.is_empty());
}

#[test]
fn test_collect_multiple_greek_vars() {
    let mut collector = AutoBoundCollector::new(empty_scope());
    // fun (x : α) => β
    let body = SurfaceExpr::ident("\u{03B2}");
    let binder = SurfaceBinder::new(
        "x",
        Some(SurfaceExpr::ident("\u{03B1}")),
        SurfaceBinderInfo::Explicit,
    );
    let expr = SurfaceExpr::lambda(vec![binder], body);
    collector.collect_from_expr(&expr);

    let (vars, _) = collector.finish();
    let names: Vec<&str> = names_of(&vars);
    assert_eq!(names, vec!["\u{03B1}", "\u{03B2}"]);
}

// =============================================================================
// AutoBoundCollector: universe variable detection
// =============================================================================

#[test]
fn test_collect_universe_var_from_ident() {
    let mut collector = AutoBoundCollector::new(empty_scope());
    let expr = SurfaceExpr::ident("u");
    collector.collect_from_expr(&expr);

    let (vars, univs) = collector.finish();
    assert_eq!(vars.len(), 1);
    assert_eq!(vars[0].name, "u");
    assert!(matches!(vars[0].kind, AutoBoundKind::UniverseVar));
    assert_eq!(univs, vec!["u"]);
}

#[test]
fn test_collect_universe_from_level_param() {
    let mut collector = AutoBoundCollector::new(empty_scope());
    // Sort u
    let expr = SurfaceExpr::Universe(
        clean_parser::Span::dummy(),
        UniverseExpr::Sort(Box::new(LevelExpr::Param("u".to_owned()))),
    );
    collector.collect_from_expr(&expr);

    let (vars, univs) = collector.finish();
    assert_eq!(univs, vec!["u"]);
    assert_eq!(vars.len(), 1);
    assert!(matches!(vars[0].kind, AutoBoundKind::UniverseVar));
}

#[test]
fn test_collect_universe_from_type_level() {
    let mut collector = AutoBoundCollector::new(empty_scope());
    // Type v
    let expr = SurfaceExpr::Universe(
        clean_parser::Span::dummy(),
        UniverseExpr::TypeLevel(Box::new(LevelExpr::Param("v".to_owned()))),
    );
    collector.collect_from_expr(&expr);

    let (_, univs) = collector.finish();
    assert_eq!(univs, vec!["v"]);
}

// =============================================================================
// AutoBoundCollector: already-bound names skipped
// =============================================================================

#[test]
fn test_already_bound_names_skipped() {
    let mut collector = AutoBoundCollector::new(scope_with(&["\u{03B1}", "u"]));
    // α and u are already in scope
    let expr = SurfaceExpr::app(
        SurfaceExpr::ident("\u{03B1}"),
        vec![SurfaceExpr::ident("u")],
    );
    collector.collect_from_expr(&expr);

    let (vars, univs) = collector.finish();
    assert!(vars.is_empty());
    assert!(univs.is_empty());
}

#[test]
fn test_lambda_binder_names_in_scope() {
    let mut collector = AutoBoundCollector::new(empty_scope());
    // fun (α : Type) => α -- α is bound by the lambda, not auto-bound
    let binder = SurfaceBinder::new(
        "\u{03B1}",
        Some(SurfaceExpr::type_()),
        SurfaceBinderInfo::Explicit,
    );
    let body = SurfaceExpr::ident("\u{03B1}");
    let expr = SurfaceExpr::lambda(vec![binder], body);
    collector.collect_from_expr(&expr);

    let (vars, _) = collector.finish();
    // α appears in the binder type (Type) so nothing to collect,
    // and in the body it's bound by the lambda binder
    assert!(vars.is_empty());
}

// =============================================================================
// AutoBoundCollector: standard names rejected
// =============================================================================

#[test]
fn test_standard_names_not_autobound() {
    let mut collector = AutoBoundCollector::new(empty_scope());
    for &name in &["Nat", "Bool", "Int", "String", "Type", "Prop", "List"] {
        collector.collect_from_expr(&SurfaceExpr::ident(name));
    }
    let (vars, _) = collector.finish();
    assert!(vars.is_empty());
}

#[test]
fn test_dotted_names_not_autobound() {
    let mut collector = AutoBoundCollector::new(empty_scope());
    collector.collect_from_expr(&SurfaceExpr::ident("Nat.add"));
    let (vars, _) = collector.finish();
    assert!(vars.is_empty());
}

// =============================================================================
// AutoBoundCollector: ordering and deduplication
// =============================================================================

#[test]
fn test_ordering_preserved() {
    let mut collector = AutoBoundCollector::new(empty_scope());
    // Encounter γ, then α, then β
    collector.collect_from_expr(&SurfaceExpr::ident("\u{03B3}"));
    collector.collect_from_expr(&SurfaceExpr::ident("\u{03B1}"));
    collector.collect_from_expr(&SurfaceExpr::ident("\u{03B2}"));

    let (vars, _) = collector.finish();
    let names: Vec<&str> = names_of(&vars);
    assert_eq!(names, vec!["\u{03B3}", "\u{03B1}", "\u{03B2}"]);
}

#[test]
fn test_deduplication() {
    let mut collector = AutoBoundCollector::new(empty_scope());
    // α appears twice
    collector.collect_from_expr(&SurfaceExpr::ident("\u{03B1}"));
    collector.collect_from_expr(&SurfaceExpr::ident("\u{03B1}"));

    let (vars, _) = collector.finish();
    assert_eq!(vars.len(), 1);
}

// =============================================================================
// AutoBoundCollector: mixed type + universe vars
// =============================================================================

#[test]
fn test_mixed_type_and_universe_vars() {
    let mut collector = AutoBoundCollector::new(empty_scope());
    // fun (x : α) => Sort u
    let binder = SurfaceBinder::new(
        "x",
        Some(SurfaceExpr::ident("\u{03B1}")),
        SurfaceBinderInfo::Explicit,
    );
    let body = SurfaceExpr::Universe(
        clean_parser::Span::dummy(),
        UniverseExpr::Sort(Box::new(LevelExpr::Param("u".to_owned()))),
    );
    let expr = SurfaceExpr::lambda(vec![binder], body);
    collector.collect_from_expr(&expr);

    let (vars, univs) = collector.finish();
    // α is a type var, u is a universe var
    assert_eq!(vars.len(), 2);
    assert_eq!(vars[0].name, "\u{03B1}");
    assert!(matches!(vars[0].kind, AutoBoundKind::TypeVar { .. }));
    assert_eq!(vars[1].name, "u");
    assert!(matches!(vars[1].kind, AutoBoundKind::UniverseVar));
    assert_eq!(univs, vec!["u"]);
}

// =============================================================================
// AutoBoundCollector: nested expressions
// =============================================================================

#[test]
fn test_nested_app_scanning() {
    let mut collector = AutoBoundCollector::new(empty_scope());
    // f α β where f is a standard identifier
    let expr = SurfaceExpr::app(
        SurfaceExpr::ident("f"),
        vec![
            SurfaceExpr::ident("\u{03B1}"),
            SurfaceExpr::ident("\u{03B2}"),
        ],
    );
    collector.collect_from_expr(&expr);

    let (vars, _) = collector.finish();
    let names: Vec<&str> = names_of(&vars);
    // f is not Greek/universe so not collected
    assert_eq!(names, vec!["\u{03B1}", "\u{03B2}"]);
}

#[test]
fn test_arrow_scanning() {
    let mut collector = AutoBoundCollector::new(empty_scope());
    // α → β
    let expr = SurfaceExpr::arrow(
        SurfaceExpr::ident("\u{03B1}"),
        SurfaceExpr::ident("\u{03B2}"),
    );
    collector.collect_from_expr(&expr);

    let (vars, _) = collector.finish();
    let names: Vec<&str> = names_of(&vars);
    assert_eq!(names, vec!["\u{03B1}", "\u{03B2}"]);
}

#[test]
fn test_pi_scanning() {
    let mut collector = AutoBoundCollector::new(empty_scope());
    // (x : α) → β
    let binder = SurfaceBinder::new(
        "x",
        Some(SurfaceExpr::ident("\u{03B1}")),
        SurfaceBinderInfo::Explicit,
    );
    let body = SurfaceExpr::ident("\u{03B2}");
    let expr = SurfaceExpr::pi(vec![binder], body);
    collector.collect_from_expr(&expr);

    let (vars, _) = collector.finish();
    let names: Vec<&str> = names_of(&vars);
    assert_eq!(names, vec!["\u{03B1}", "\u{03B2}"]);
}

#[test]
fn test_ascription_scanning() {
    let mut collector = AutoBoundCollector::new(empty_scope());
    // (x : α)
    let expr = SurfaceExpr::Ascription(
        clean_parser::Span::dummy(),
        Box::new(SurfaceExpr::ident("x")),
        Box::new(SurfaceExpr::ident("\u{03B1}")),
    );
    collector.collect_from_expr(&expr);

    let (vars, _) = collector.finish();
    assert_eq!(vars.len(), 1);
    assert_eq!(vars[0].name, "\u{03B1}");
}

// =============================================================================
// AutoBoundCollector: edge cases
// =============================================================================

#[test]
fn test_empty_expr_hole() {
    let mut collector = AutoBoundCollector::new(empty_scope());
    collector.collect_from_expr(&SurfaceExpr::hole());
    let (vars, univs) = collector.finish();
    assert!(vars.is_empty());
    assert!(univs.is_empty());
}

#[test]
fn test_literal_no_autobound() {
    let mut collector = AutoBoundCollector::new(empty_scope());
    collector.collect_from_expr(&SurfaceExpr::nat(42));
    let (vars, univs) = collector.finish();
    assert!(vars.is_empty());
    assert!(univs.is_empty());
}

#[test]
fn test_all_bound_no_results() {
    let mut collector =
        AutoBoundCollector::new(scope_with(&["\u{03B1}", "\u{03B2}", "\u{03B3}", "u", "v"]));
    collector.collect_from_expr(&SurfaceExpr::ident("\u{03B1}"));
    collector.collect_from_expr(&SurfaceExpr::ident("\u{03B2}"));
    collector.collect_from_expr(&SurfaceExpr::ident("u"));
    let (vars, univs) = collector.finish();
    assert!(vars.is_empty());
    assert!(univs.is_empty());
}

// =============================================================================
// wrap_with_auto_bounds
// =============================================================================

#[test]
fn test_wrap_with_type_var() {
    let body = Expr::const_str("result");
    let vars = vec![AutoBoundVar {
        name: "\u{03B1}".to_owned(),
        kind: AutoBoundKind::TypeVar { universe: None },
        binder_info: BinderInfo::Implicit,
    }];

    let wrapped = AutoBoundCollector::wrap_with_auto_bounds(body, &vars);
    // Should be Pi {_ : Type} result
    match wrapped.kind() {
        ExprKind::Pi(bd, ty, _body) => {
            assert_eq!(bd.info, BinderInfo::Implicit);
            // Type is Sort 1
            assert!(matches!(ty.kind(), ExprKind::Sort(_)));
        }
        other => panic!("expected Pi, got {other:?}"),
    }
}

#[test]
fn test_wrap_with_instance_var() {
    let body = Expr::const_str("result");
    let vars = vec![AutoBoundVar {
        name: "inst".to_owned(),
        kind: AutoBoundKind::InstanceVar {
            class_name: "Inhabited".to_owned(),
        },
        binder_info: BinderInfo::InstImplicit,
    }];

    let wrapped = AutoBoundCollector::wrap_with_auto_bounds(body, &vars);
    match wrapped.kind() {
        ExprKind::Pi(bd, ty, _body) => {
            assert_eq!(bd.info, BinderInfo::InstImplicit);
            // Type should be const "Inhabited"
            assert!(matches!(ty.kind(), ExprKind::Const(..)));
        }
        other => panic!("expected Pi, got {other:?}"),
    }
}

#[test]
fn test_wrap_universe_var_skipped() {
    let body = Expr::const_str("result");
    let vars = vec![AutoBoundVar {
        name: "u".to_owned(),
        kind: AutoBoundKind::UniverseVar,
        binder_info: BinderInfo::Implicit,
    }];

    let wrapped = AutoBoundCollector::wrap_with_auto_bounds(body.clone(), &vars);
    // Universe vars don't produce Pi wrappers
    assert_eq!(format!("{wrapped}"), format!("{body}"));
}

#[test]
fn test_wrap_multiple_vars_ordering() {
    let body = Expr::const_str("result");
    let vars = vec![
        AutoBoundVar {
            name: "\u{03B1}".to_owned(),
            kind: AutoBoundKind::TypeVar { universe: None },
            binder_info: BinderInfo::Implicit,
        },
        AutoBoundVar {
            name: "\u{03B2}".to_owned(),
            kind: AutoBoundKind::TypeVar { universe: None },
            binder_info: BinderInfo::Implicit,
        },
    ];

    let wrapped = AutoBoundCollector::wrap_with_auto_bounds(body, &vars);
    // Should be Pi {_ : Type} (Pi {_ : Type} result)
    // α is outermost
    match wrapped.kind() {
        ExprKind::Pi(_, _, inner) => {
            assert!(matches!(inner.kind(), ExprKind::Pi(..)));
        }
        other => panic!("expected nested Pi, got {other:?}"),
    }
}

// =============================================================================
// add_universe_params
// =============================================================================

#[test]
fn test_add_universe_params_basic() {
    let mut levels = vec!["u".to_owned()];
    AutoBoundCollector::add_universe_params(&mut levels, &["v".to_owned(), "w".to_owned()]);
    assert_eq!(levels, vec!["u", "v", "w"]);
}

#[test]
fn test_add_universe_params_no_duplicates() {
    let mut levels = vec!["u".to_owned(), "v".to_owned()];
    AutoBoundCollector::add_universe_params(&mut levels, &["v".to_owned(), "w".to_owned()]);
    assert_eq!(levels, vec!["u", "v", "w"]);
}

#[test]
fn test_add_universe_params_empty() {
    let mut levels = Vec::new();
    AutoBoundCollector::add_universe_params(&mut levels, &["u".to_owned()]);
    assert_eq!(levels, vec!["u"]);
}

// =============================================================================
// auto_bound_surface_binders
// =============================================================================

#[test]
fn test_surface_binders_type_var() {
    let vars = vec![AutoBoundVar {
        name: "\u{03B1}".to_owned(),
        kind: AutoBoundKind::TypeVar { universe: None },
        binder_info: BinderInfo::Implicit,
    }];

    let binders = auto_bound_surface_binders(&vars);
    assert_eq!(binders.len(), 1);
    assert_eq!(binders[0].name, "\u{03B1}");
    assert_eq!(binders[0].info, SurfaceBinderInfo::Implicit);
    assert!(binders[0].ty.is_some());
}

#[test]
fn test_surface_binders_universe_var_skipped() {
    let vars = vec![AutoBoundVar {
        name: "u".to_owned(),
        kind: AutoBoundKind::UniverseVar,
        binder_info: BinderInfo::Implicit,
    }];

    let binders = auto_bound_surface_binders(&vars);
    assert!(binders.is_empty());
}

#[test]
fn test_surface_binders_instance_var() {
    let vars = vec![AutoBoundVar {
        name: "inst".to_owned(),
        kind: AutoBoundKind::InstanceVar {
            class_name: "Inhabited".to_owned(),
        },
        binder_info: BinderInfo::InstImplicit,
    }];

    let binders = auto_bound_surface_binders(&vars);
    assert_eq!(binders.len(), 1);
    assert_eq!(binders[0].info, SurfaceBinderInfo::Instance);
}

// =============================================================================
// collect_from_type convenience
// =============================================================================

#[test]
fn test_collect_from_type_delegates_to_expr() {
    let mut collector = AutoBoundCollector::new(empty_scope());
    collector.collect_from_type(&SurfaceExpr::ident("\u{03B1}"));
    let (vars, _) = collector.finish();
    assert_eq!(vars.len(), 1);
    assert_eq!(vars[0].name, "\u{03B1}");
}

// =============================================================================
// Level expression scanning
// =============================================================================

#[test]
fn test_collect_level_succ() {
    let mut collector = AutoBoundCollector::new(empty_scope());
    // Sort (u + 1)
    let expr = SurfaceExpr::Universe(
        clean_parser::Span::dummy(),
        UniverseExpr::Sort(Box::new(LevelExpr::Succ(Box::new(LevelExpr::Param(
            "u".to_owned(),
        ))))),
    );
    collector.collect_from_expr(&expr);
    let (_, univs) = collector.finish();
    assert_eq!(univs, vec!["u"]);
}

#[test]
fn test_collect_level_max() {
    let mut collector = AutoBoundCollector::new(empty_scope());
    // Sort (max u v)
    let expr = SurfaceExpr::Universe(
        clean_parser::Span::dummy(),
        UniverseExpr::Sort(Box::new(LevelExpr::Max(
            Box::new(LevelExpr::Param("u".to_owned())),
            Box::new(LevelExpr::Param("v".to_owned())),
        ))),
    );
    collector.collect_from_expr(&expr);
    let (_, univs) = collector.finish();
    assert_eq!(univs, vec!["u", "v"]);
}
