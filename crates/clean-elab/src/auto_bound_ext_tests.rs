// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for extended auto-bound implicit variable elaboration.

use clean_kernel::expr::{BinderInfo, ExprKind};
use clean_kernel::level::Level;
use clean_kernel::name::Name;
use clean_kernel::Expr;

use super::auto_bound_ext::*;
use crate::error::ElabError;

// =============================================================================
// Helpers
// =============================================================================

fn name(s: &str) -> Name {
    Name::from_string(s)
}

fn mk_entry(n: &str, ty: Expr) -> AutoBoundEntry {
    AutoBoundEntry {
        name: name(n),
        type_expr: ty,
        binder_info: BinderInfo::Implicit,
        source_span: None,
    }
}

fn mk_entry_with_info(n: &str, ty: Expr, info: BinderInfo) -> AutoBoundEntry {
    AutoBoundEntry {
        name: name(n),
        type_expr: ty,
        binder_info: info,
        source_span: None,
    }
}

fn entry_names(entries: &[AutoBoundEntry]) -> Vec<String> {
    entries.iter().map(|e| format!("{}", e.name)).collect()
}

// =============================================================================
// AutoBoundConfig
// =============================================================================

#[test]
fn test_config_default_values() {
    let config = AutoBoundConfig::default();
    assert_eq!(config.max_depth, 8);
    assert!(config.allow_sort_vars);
    assert!(!config.warn_on_ambiguity);
}

#[test]
fn test_config_custom_values() {
    let config = AutoBoundConfig {
        max_depth: 16,
        allow_sort_vars: false,
        warn_on_ambiguity: true,
    };
    assert_eq!(config.max_depth, 16);
    assert!(!config.allow_sort_vars);
    assert!(config.warn_on_ambiguity);
}

// =============================================================================
// AutoBoundEntry
// =============================================================================

#[test]
fn test_entry_equality() {
    let e1 = mk_entry("alpha", Expr::type_());
    let e2 = mk_entry("alpha", Expr::type_());
    assert_eq!(e1, e2);
}

#[test]
fn test_entry_inequality_name() {
    let e1 = mk_entry("alpha", Expr::type_());
    let e2 = mk_entry("beta", Expr::type_());
    assert_ne!(e1, e2);
}

#[test]
fn test_entry_with_source_span() {
    let mut entry = mk_entry("alpha", Expr::type_());
    entry.source_span = Some((10, 15));
    assert_eq!(entry.source_span, Some((10, 15)));
}

// =============================================================================
// AutoBoundContext: scope management
// =============================================================================

#[test]
fn test_context_new_has_root_scope() {
    let ctx = AutoBoundContext::new();
    assert_eq!(ctx.depth(), 1);
    assert!(ctx.get_auto_bounds().is_empty());
}

#[test]
fn test_context_enter_leave_scope() {
    let mut ctx = AutoBoundContext::new();
    ctx.enter_scope();
    assert_eq!(ctx.depth(), 2);

    ctx.register_free_variable(&name("alpha"), None);
    assert_eq!(ctx.get_auto_bounds().len(), 1);

    let collected = ctx.leave_scope();
    assert_eq!(collected.len(), 1);
    assert_eq!(ctx.depth(), 1);
    // Root scope should still be empty.
    assert!(ctx.get_auto_bounds().is_empty());
}

#[test]
fn test_context_nested_scopes() {
    let mut ctx = AutoBoundContext::new();
    ctx.register_free_variable(&name("root_var"), None);

    ctx.enter_scope();
    ctx.register_free_variable(&name("inner_var"), None);
    assert_eq!(ctx.get_auto_bounds().len(), 1);

    let inner = ctx.leave_scope();
    assert_eq!(inner.len(), 1);
    assert_eq!(format!("{}", inner[0].name), "inner_var");

    // Root scope retains its variable.
    assert_eq!(ctx.get_auto_bounds().len(), 1);
}

#[test]
fn test_context_leave_root_scope_returns_empty() {
    let mut ctx = AutoBoundContext::new();
    ctx.register_free_variable(&name("alpha"), None);
    // Trying to leave the root scope should return empty and not pop it.
    let result = ctx.leave_scope();
    assert!(result.is_empty());
    assert_eq!(ctx.depth(), 1);
    assert_eq!(ctx.get_auto_bounds().len(), 1);
}

#[test]
fn test_context_deduplication_within_scope() {
    let mut ctx = AutoBoundContext::new();
    ctx.register_free_variable(&name("alpha"), None);
    ctx.register_free_variable(&name("alpha"), None);
    assert_eq!(ctx.get_auto_bounds().len(), 1);
}

#[test]
fn test_context_different_names_not_deduped() {
    let mut ctx = AutoBoundContext::new();
    ctx.register_free_variable(&name("alpha"), None);
    ctx.register_free_variable(&name("beta"), None);
    assert_eq!(ctx.get_auto_bounds().len(), 2);
}

#[test]
fn test_context_with_config() {
    let config = AutoBoundConfig {
        max_depth: 4,
        allow_sort_vars: false,
        warn_on_ambiguity: true,
    };
    let ctx = AutoBoundContext::with_config(config);
    assert_eq!(ctx.config().max_depth, 4);
    assert!(!ctx.config().allow_sort_vars);
}

#[test]
fn test_context_register_with_expected_type() {
    let mut ctx = AutoBoundContext::new();
    ctx.register_free_variable(&name("alpha"), Some(&Expr::prop()));
    let bounds = ctx.get_auto_bounds();
    assert_eq!(bounds.len(), 1);
    assert!(matches!(bounds[0].type_expr.kind(), ExprKind::Sort(l) if *l == Level::zero()));
}

#[test]
fn test_context_register_without_expected_type_defaults_to_type() {
    let mut ctx = AutoBoundContext::new();
    ctx.register_free_variable(&name("alpha"), None);
    let bounds = ctx.get_auto_bounds();
    assert_eq!(bounds.len(), 1);
    // Type is Sort 1
    assert!(
        matches!(bounds[0].type_expr.kind(), ExprKind::Sort(l) if *l == Level::succ(Level::zero()))
    );
}

// =============================================================================
// collect_free_variables
// =============================================================================

#[test]
fn test_collect_free_vars_const() {
    // Expr::const_str("alpha") has name "alpha"
    let expr = Expr::const_str("alpha");
    let free = collect_free_variables(&expr, &[]);
    assert_eq!(free.len(), 1);
    assert_eq!(free[0], name("alpha"));
}

#[test]
fn test_collect_free_vars_declared_excluded() {
    let expr = Expr::const_str("alpha");
    let declared = vec![name("alpha")];
    let free = collect_free_variables(&expr, &declared);
    assert!(free.is_empty());
}

#[test]
fn test_collect_free_vars_multiple_consts() {
    // App(const "f", const "alpha")
    let expr = Expr::app(Expr::const_str("f"), Expr::const_str("alpha"));
    let free = collect_free_variables(&expr, &[]);
    assert_eq!(free.len(), 2);
    assert_eq!(free[0], name("f"));
    assert_eq!(free[1], name("alpha"));
}

#[test]
fn test_collect_free_vars_deduplication() {
    // App(const "alpha", const "alpha")
    let expr = Expr::app(Expr::const_str("alpha"), Expr::const_str("alpha"));
    let free = collect_free_variables(&expr, &[]);
    assert_eq!(free.len(), 1);
}

#[test]
fn test_collect_free_vars_nested_pi() {
    // Pi (_ : alpha) beta
    let expr = Expr::pi(
        BinderInfo::Default,
        Expr::const_str("alpha"),
        Expr::const_str("beta"),
    );
    let free = collect_free_variables(&expr, &[]);
    assert_eq!(free.len(), 2);
    assert_eq!(free[0], name("alpha"));
    assert_eq!(free[1], name("beta"));
}

#[test]
fn test_collect_free_vars_lambda() {
    // Lam (_ : alpha) body
    let expr = Expr::lam(BinderInfo::Default, Expr::const_str("alpha"), Expr::bvar(0));
    let free = collect_free_variables(&expr, &[]);
    assert_eq!(free.len(), 1);
    assert_eq!(free[0], name("alpha"));
}

#[test]
fn test_collect_free_vars_bvar_ignored() {
    let expr = Expr::bvar(0);
    let free = collect_free_variables(&expr, &[]);
    assert!(free.is_empty());
}

#[test]
fn test_collect_free_vars_sort_ignored() {
    let expr = Expr::type_();
    let free = collect_free_variables(&expr, &[]);
    assert!(free.is_empty());
}

#[test]
fn test_collect_free_vars_lit_ignored() {
    let expr = Expr::nat_lit(42);
    let free = collect_free_variables(&expr, &[]);
    assert!(free.is_empty());
}

#[test]
fn test_collect_free_vars_no_free_vars() {
    let declared = vec![name("Nat"), name("Bool")];
    let expr = Expr::app(Expr::const_str("Nat"), Expr::const_str("Bool"));
    let free = collect_free_variables(&expr, &declared);
    assert!(free.is_empty());
}

// =============================================================================
// infer_binder_type
// =============================================================================

#[test]
fn test_infer_binder_type_default_is_type() {
    let result = infer_binder_type(&name("alpha"), &[]);
    assert!(matches!(result.kind(), ExprKind::Sort(l) if *l == Level::succ(Level::zero())));
}

#[test]
fn test_infer_binder_type_from_sort_zero_is_prop() {
    let prop_expr = Expr::prop();
    let result = infer_binder_type(&name("p"), &[&prop_expr]);
    assert!(matches!(result.kind(), ExprKind::Sort(l) if *l == Level::zero()));
}

#[test]
fn test_infer_binder_type_from_non_sort_is_type() {
    let nat = Expr::const_str("Nat");
    let result = infer_binder_type(&name("n"), &[&nat]);
    assert!(matches!(result.kind(), ExprKind::Sort(l) if *l == Level::succ(Level::zero())));
}

// =============================================================================
// sort_by_dependency
// =============================================================================

#[test]
fn test_sort_by_dependency_independent() {
    // alpha : Type, beta : Type -- no dependencies, order preserved
    let mut bounds = vec![
        mk_entry("alpha", Expr::type_()),
        mk_entry("beta", Expr::type_()),
    ];
    sort_by_dependency(&mut bounds);
    let names = entry_names(&bounds);
    assert_eq!(names, vec!["alpha", "beta"]);
}

#[test]
fn test_sort_by_dependency_linear_chain() {
    // alpha : Type, beta : alpha
    // beta depends on alpha, so alpha must come first
    let mut bounds = vec![
        mk_entry("beta", Expr::const_str("alpha")),
        mk_entry("alpha", Expr::type_()),
    ];
    sort_by_dependency(&mut bounds);
    let names = entry_names(&bounds);
    assert_eq!(names, vec!["alpha", "beta"]);
}

#[test]
fn test_sort_by_dependency_three_chain() {
    // gamma depends on beta, beta depends on alpha
    let mut bounds = vec![
        mk_entry("gamma", Expr::const_str("beta")),
        mk_entry("beta", Expr::const_str("alpha")),
        mk_entry("alpha", Expr::type_()),
    ];
    sort_by_dependency(&mut bounds);
    let names = entry_names(&bounds);
    assert_eq!(names[0], "alpha");
    assert_eq!(names[1], "beta");
    assert_eq!(names[2], "gamma");
}

#[test]
fn test_sort_by_dependency_diamond() {
    // gamma depends on alpha and beta; alpha and beta are independent
    let mut bounds = vec![
        mk_entry(
            "gamma",
            Expr::app(Expr::const_str("alpha"), Expr::const_str("beta")),
        ),
        mk_entry("alpha", Expr::type_()),
        mk_entry("beta", Expr::type_()),
    ];
    sort_by_dependency(&mut bounds);
    let names = entry_names(&bounds);
    // gamma must be last; alpha and beta can be in either order
    assert_eq!(names[2], "gamma");
    assert!(names[0] == "alpha" || names[0] == "beta");
    assert!(names[1] == "alpha" || names[1] == "beta");
}

#[test]
fn test_sort_by_dependency_single_entry() {
    let mut bounds = vec![mk_entry("alpha", Expr::type_())];
    sort_by_dependency(&mut bounds);
    assert_eq!(entry_names(&bounds), vec!["alpha"]);
}

#[test]
fn test_sort_by_dependency_empty() {
    let mut bounds: Vec<AutoBoundEntry> = Vec::new();
    sort_by_dependency(&mut bounds);
    assert!(bounds.is_empty());
}

#[test]
fn test_sort_by_dependency_self_referential_ignored() {
    // alpha : alpha -- self-reference is not a cross-dependency
    let mut bounds = vec![mk_entry("alpha", Expr::const_str("alpha"))];
    sort_by_dependency(&mut bounds);
    assert_eq!(entry_names(&bounds), vec!["alpha"]);
}

// =============================================================================
// check_no_cycles
// =============================================================================

#[test]
fn test_no_cycles_independent() {
    let bounds = vec![
        mk_entry("alpha", Expr::type_()),
        mk_entry("beta", Expr::type_()),
    ];
    assert!(check_no_cycles(&bounds).is_ok());
}

#[test]
fn test_no_cycles_linear() {
    let bounds = vec![
        mk_entry("alpha", Expr::type_()),
        mk_entry("beta", Expr::const_str("alpha")),
    ];
    assert!(check_no_cycles(&bounds).is_ok());
}

#[test]
fn test_cycle_detected_two_node() {
    // alpha depends on beta, beta depends on alpha
    let bounds = vec![
        mk_entry("alpha", Expr::const_str("beta")),
        mk_entry("beta", Expr::const_str("alpha")),
    ];
    let result = check_no_cycles(&bounds);
    assert!(result.is_err());
}

#[test]
fn test_cycle_detected_three_node() {
    // alpha -> beta -> gamma -> alpha
    let bounds = vec![
        mk_entry("alpha", Expr::const_str("beta")),
        mk_entry("beta", Expr::const_str("gamma")),
        mk_entry("gamma", Expr::const_str("alpha")),
    ];
    let result = check_no_cycles(&bounds);
    assert!(result.is_err());
}

#[test]
fn test_no_cycles_single() {
    let bounds = vec![mk_entry("alpha", Expr::type_())];
    assert!(check_no_cycles(&bounds).is_ok());
}

#[test]
fn test_no_cycles_empty() {
    let bounds: Vec<AutoBoundEntry> = Vec::new();
    assert!(check_no_cycles(&bounds).is_ok());
}

#[test]
fn test_no_cycles_self_reference() {
    // Self-reference is not a cycle in the dependency graph (self-loops
    // are excluded by the j != i check).
    let bounds = vec![mk_entry("alpha", Expr::const_str("alpha"))];
    assert!(check_no_cycles(&bounds).is_ok());
}

// =============================================================================
// abstract_auto_bounds_pi
// =============================================================================

#[test]
fn test_abstract_pi_single_implicit() {
    let body = Expr::const_str("result");
    let bounds = vec![mk_entry("alpha", Expr::type_())];
    let wrapped = abstract_auto_bounds_pi(body, &bounds);

    match wrapped.kind() {
        ExprKind::Pi(bd, ty, _inner) => {
            assert_eq!(bd.info, BinderInfo::Implicit);
            assert!(matches!(ty.kind(), ExprKind::Sort(_)));
        }
        other => panic!("expected Pi, got {other:?}"),
    }
}

#[test]
fn test_abstract_pi_two_entries_ordering() {
    let body = Expr::const_str("result");
    let bounds = vec![
        mk_entry("alpha", Expr::type_()),
        mk_entry("beta", Expr::prop()),
    ];
    let wrapped = abstract_auto_bounds_pi(body, &bounds);

    // alpha is outermost
    match wrapped.kind() {
        ExprKind::Pi(_bd, ty_outer, inner) => {
            // outer type is Type (Sort 1)
            assert!(
                matches!(ty_outer.kind(), ExprKind::Sort(l) if *l == Level::succ(Level::zero()))
            );
            // inner is another Pi
            match inner.kind() {
                ExprKind::Pi(_bd2, ty_inner, _) => {
                    // inner type is Prop (Sort 0)
                    assert!(matches!(ty_inner.kind(), ExprKind::Sort(l) if *l == Level::zero()));
                }
                other => panic!("expected inner Pi, got {other:?}"),
            }
        }
        other => panic!("expected Pi, got {other:?}"),
    }
}

#[test]
fn test_abstract_pi_empty_bounds() {
    let body = Expr::const_str("result");
    let wrapped = abstract_auto_bounds_pi(body.clone(), &[]);
    // No wrapping -- result unchanged
    assert_eq!(format!("{wrapped}"), format!("{body}"));
}

#[test]
fn test_abstract_pi_inst_implicit() {
    let body = Expr::const_str("result");
    let bounds = vec![mk_entry_with_info(
        "inst",
        Expr::const_str("Inhabited"),
        BinderInfo::InstImplicit,
    )];
    let wrapped = abstract_auto_bounds_pi(body, &bounds);
    match wrapped.kind() {
        ExprKind::Pi(bd, _ty, _inner) => {
            assert_eq!(bd.info, BinderInfo::InstImplicit);
        }
        other => panic!("expected Pi, got {other:?}"),
    }
}

// =============================================================================
// abstract_auto_bounds_lam
// =============================================================================

#[test]
fn test_abstract_lam_single() {
    let body = Expr::bvar(0);
    let bounds = vec![mk_entry("alpha", Expr::type_())];
    let wrapped = abstract_auto_bounds_lam(body, &bounds);

    match wrapped.kind() {
        ExprKind::Lam(bd, ty, _inner) => {
            assert_eq!(bd.info, BinderInfo::Implicit);
            assert!(matches!(ty.kind(), ExprKind::Sort(_)));
        }
        other => panic!("expected Lam, got {other:?}"),
    }
}

#[test]
fn test_abstract_lam_empty_bounds() {
    let body = Expr::const_str("result");
    let wrapped = abstract_auto_bounds_lam(body.clone(), &[]);
    assert_eq!(format!("{wrapped}"), format!("{body}"));
}

#[test]
fn test_abstract_lam_two_entries() {
    let body = Expr::bvar(0);
    let bounds = vec![
        mk_entry("alpha", Expr::type_()),
        mk_entry("beta", Expr::type_()),
    ];
    let wrapped = abstract_auto_bounds_lam(body, &bounds);

    // alpha outermost -> Lam(alpha, Lam(beta, body))
    match wrapped.kind() {
        ExprKind::Lam(_, _, inner) => {
            assert!(matches!(inner.kind(), ExprKind::Lam(..)));
        }
        other => panic!("expected nested Lam, got {other:?}"),
    }
}

// =============================================================================
// Integration: sort + check + abstract
// =============================================================================

#[test]
fn test_integration_sort_check_abstract() {
    // beta depends on alpha
    let mut bounds = vec![
        mk_entry("beta", Expr::const_str("alpha")),
        mk_entry("alpha", Expr::type_()),
    ];

    check_no_cycles(&bounds).expect("no cycles");
    sort_by_dependency(&mut bounds);

    // alpha should now be first
    assert_eq!(format!("{}", bounds[0].name), "alpha");
    assert_eq!(format!("{}", bounds[1].name), "beta");

    let body = Expr::const_str("result");
    let wrapped = abstract_auto_bounds_pi(body, &bounds);

    // Outermost: Pi {alpha : Type}, inner: Pi {beta : alpha}, result
    match wrapped.kind() {
        ExprKind::Pi(_, ty_outer, inner) => {
            // outer type is Type
            assert!(matches!(ty_outer.kind(), ExprKind::Sort(_)));
            match inner.kind() {
                ExprKind::Pi(_, ty_inner, _) => {
                    // inner type references alpha
                    assert!(matches!(ty_inner.kind(), ExprKind::Const(..)));
                }
                other => panic!("expected inner Pi, got {other:?}"),
            }
        }
        other => panic!("expected Pi, got {other:?}"),
    }
}

#[test]
fn test_integration_cycle_rejected() {
    let bounds = vec![
        mk_entry("alpha", Expr::const_str("beta")),
        mk_entry("beta", Expr::const_str("alpha")),
    ];
    let result = check_no_cycles(&bounds);
    assert!(result.is_err());
    match result {
        Err(ElabError::NotImplemented(msg)) => {
            assert!(msg.contains("cyclic"));
        }
        other => panic!("expected NotImplemented error, got {other:?}"),
    }
}

// =============================================================================
// Edge cases
// =============================================================================

#[test]
fn test_shadowed_names_in_scope() {
    let mut ctx = AutoBoundContext::new();
    ctx.register_free_variable(&name("alpha"), None);
    ctx.enter_scope();
    // Same name in inner scope -- allowed (separate scope).
    ctx.register_free_variable(&name("alpha"), Some(&Expr::prop()));

    let inner = ctx.leave_scope();
    assert_eq!(inner.len(), 1);
    // Inner alpha has Prop type
    assert!(matches!(inner[0].type_expr.kind(), ExprKind::Sort(l) if *l == Level::zero()));

    // Root alpha has Type
    let root = ctx.get_auto_bounds();
    assert_eq!(root.len(), 1);
    assert!(
        matches!(root[0].type_expr.kind(), ExprKind::Sort(l) if *l == Level::succ(Level::zero()))
    );
}

#[test]
fn test_collect_free_vars_let_binding() {
    // let _ : alpha := beta in gamma
    let expr = Expr::let_named(
        Name::anon(),
        Expr::const_str("alpha"),
        Expr::const_str("beta"),
        Expr::const_str("gamma"),
        false,
    );
    let free = collect_free_variables(&expr, &[]);
    assert_eq!(free.len(), 3);
    assert!(free.contains(&name("alpha")));
    assert!(free.contains(&name("beta")));
    assert!(free.contains(&name("gamma")));
}

#[test]
fn test_collect_free_vars_proj() {
    let inner = Expr::const_str("s");
    let expr = Expr::proj(name("MyStruct"), 0, inner);
    let free = collect_free_variables(&expr, &[]);
    assert_eq!(free.len(), 1);
    assert_eq!(free[0], name("s"));
}

#[test]
fn test_deeply_nested_expr_respects_depth_limit() {
    // Build a chain of apps 100 deep; the default max_depth (64) should
    // prevent infinite recursion but still find some variables.
    let mut expr = Expr::const_str("base");
    for i in 0..100 {
        expr = Expr::app(Expr::const_str(&format!("f{i}")), expr);
    }
    let free = collect_free_variables(&expr, &[]);
    // Should find names without panic/stack overflow.
    assert!(!free.is_empty());
}
