// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the extended macro hygiene module.
//!
//! Covers: ScopeId basics, HygieneContext scope management, fresh name
//! generation, accessibility checks, binding visibility, colorize_expr,
//! resolve_hygienic, alpha_rename_avoiding, check_hygiene_violation,
//! nested scopes, edge cases, and violation detection.

use clean_kernel::{Expr, ExprKind, Level, Name};

use crate::error::ElabError;
use crate::macro_hygiene_ext::{
    alpha_rename_avoiding, check_hygiene_violation, colorize_expr, resolve_hygienic,
    HygieneContext, ScopeId, ViolationKind,
};

// ═══════════════════════════════════════════════════════════════════════════
// ScopeId basics
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn test_scope_id_root_is_zero() {
    let root = ScopeId::root();
    assert_eq!(root.id(), 0);
    assert!(root.is_root());
}

#[test]
fn test_scope_id_non_root() {
    let mut ctx = HygieneContext::new();
    let m = Name::from_string("m");
    let s = ctx.enter_macro_scope(&m);
    assert_ne!(s.id(), 0);
    assert!(!s.is_root());
}

#[test]
fn test_scope_id_display() {
    let mut ctx = HygieneContext::new();
    let m = Name::from_string("m");
    let s = ctx.enter_macro_scope(&m);
    let display = format!("{s}");
    assert!(display.starts_with("ScopeId("), "got: {display}");
    assert!(display.ends_with(')'), "got: {display}");
}

#[test]
fn test_scope_id_equality() {
    let mut ctx = HygieneContext::new();
    let m = Name::from_string("m");
    let s1 = ctx.enter_macro_scope(&m);
    ctx.leave_macro_scope();
    let s2 = ctx.enter_macro_scope(&m);
    assert_ne!(s1, s2);
    assert_eq!(ScopeId::root(), ScopeId::root());
}

// ═══════════════════════════════════════════════════════════════════════════
// HygieneContext scope management
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn test_new_context_has_root_scope() {
    let ctx = HygieneContext::new();
    assert_eq!(ctx.scope_depth(), 1);
    assert!(ctx.current_scope().is_root());
}

#[test]
fn test_enter_macro_scope_pushes() {
    let mut ctx = HygieneContext::new();
    let name = Name::from_string("myMacro");
    let s = ctx.enter_macro_scope(&name);
    assert!(!s.is_root());
    assert_eq!(ctx.scope_depth(), 2);
    assert_eq!(ctx.current_scope(), s);
}

#[test]
fn test_leave_macro_scope_pops() {
    let mut ctx = HygieneContext::new();
    let name = Name::from_string("m");
    let s = ctx.enter_macro_scope(&name);
    let popped = ctx.leave_macro_scope();
    assert_eq!(popped, Some(s));
    assert_eq!(ctx.scope_depth(), 1);
    assert!(ctx.current_scope().is_root());
}

#[test]
fn test_cannot_pop_root() {
    let mut ctx = HygieneContext::new();
    assert_eq!(ctx.leave_macro_scope(), None);
    assert_eq!(ctx.scope_depth(), 1);
}

#[test]
fn test_nested_scopes() {
    let mut ctx = HygieneContext::new();
    let m1 = Name::from_string("outer");
    let m2 = Name::from_string("inner");
    let s1 = ctx.enter_macro_scope(&m1);
    let s2 = ctx.enter_macro_scope(&m2);
    assert_eq!(ctx.scope_depth(), 3);
    assert_eq!(ctx.current_scope(), s2);
    ctx.leave_macro_scope();
    assert_eq!(ctx.current_scope(), s1);
    ctx.leave_macro_scope();
    assert!(ctx.current_scope().is_root());
}

#[test]
fn test_scope_ids_are_unique() {
    let mut ctx = HygieneContext::new();
    let name = Name::from_string("m");
    let mut ids = Vec::new();
    for _ in 0..100 {
        let s = ctx.enter_macro_scope(&name);
        assert!(!ids.contains(&s));
        ids.push(s);
        ctx.leave_macro_scope();
    }
}

#[test]
fn test_scope_info_stored() {
    let mut ctx = HygieneContext::new();
    let name = Name::from_string("testMacro");
    let s = ctx.enter_macro_scope(&name);
    let info = ctx.info_for_scope(s).expect("info should exist");
    assert_eq!(info.scope, s);
    assert!(info.macro_name.is_some());
}

#[test]
fn test_enter_macro_scope_with_site() {
    let mut ctx = HygieneContext::new();
    let name = Name::from_string("sited");
    let s = ctx.enter_macro_scope_with_site(&name, 10, 5);
    let info = ctx.info_for_scope(s).expect("info");
    assert_eq!(info.definition_site, Some((10, 5)));
}

// ═══════════════════════════════════════════════════════════════════════════
// Fresh name generation
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn test_fresh_name_contains_base() {
    let mut ctx = HygieneContext::new();
    let n = ctx.fresh_name("x");
    let s = n.to_string();
    assert!(s.starts_with("x_hyg_"), "got: {s}");
}

#[test]
fn test_fresh_names_are_unique() {
    let mut ctx = HygieneContext::new();
    let n1 = ctx.fresh_name("a");
    let n2 = ctx.fresh_name("a");
    let n3 = ctx.fresh_name("a");
    let s1 = n1.to_string();
    let s2 = n2.to_string();
    let s3 = n3.to_string();
    assert_ne!(s1, s2);
    assert_ne!(s2, s3);
    assert_ne!(s1, s3);
}

#[test]
fn test_fresh_name_auto_binds_in_current_scope() {
    let mut ctx = HygieneContext::new();
    let name = Name::from_string("m");
    let s = ctx.enter_macro_scope(&name);
    let fresh = ctx.fresh_name("tmp");
    assert!(ctx.is_accessible(&fresh, s));
}

// ═══════════════════════════════════════════════════════════════════════════
// Binding and accessibility
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn test_bind_and_access_in_root() {
    let mut ctx = HygieneContext::new();
    let name = Name::from_string("foo");
    ctx.bind_name(&name, ScopeId::root());
    assert!(ctx.is_accessible(&name, ScopeId::root()));
}

#[test]
fn test_bind_in_child_not_accessible_from_root() {
    let mut ctx = HygieneContext::new();
    let macro_name = Name::from_string("m");
    let s = ctx.enter_macro_scope(&macro_name);
    let name = Name::from_string("local_var");
    ctx.bind_name(&name, s);
    ctx.leave_macro_scope();
    assert!(!ctx.is_accessible(&name, ScopeId::root()));
}

#[test]
fn test_root_binding_accessible_from_child() {
    let mut ctx = HygieneContext::new();
    let name = Name::from_string("global");
    ctx.bind_name(&name, ScopeId::root());
    let macro_name = Name::from_string("m");
    let s = ctx.enter_macro_scope(&macro_name);
    assert!(ctx.is_accessible(&name, s));
}

#[test]
fn test_unbound_name_not_accessible() {
    let ctx = HygieneContext::new();
    let name = Name::from_string("nope");
    assert!(!ctx.is_accessible(&name, ScopeId::root()));
}

#[test]
fn test_mark_captured() {
    let mut ctx = HygieneContext::new();
    let name = Name::from_string("cap");
    ctx.bind_name(&name, ScopeId::root());
    ctx.mark_captured(&name, ScopeId::root());
    let bindings = ctx.bindings_for(&name);
    assert_eq!(bindings.len(), 1);
    assert!(bindings[0].is_captured);
}

#[test]
fn test_duplicate_bind_same_scope_deduplicates() {
    let mut ctx = HygieneContext::new();
    let name = Name::from_string("dup");
    ctx.bind_name(&name, ScopeId::root());
    ctx.bind_name(&name, ScopeId::root());
    assert_eq!(ctx.bindings_for(&name).len(), 1);
}

#[test]
fn test_bind_same_name_different_scopes() {
    let mut ctx = HygieneContext::new();
    let name = Name::from_string("x");
    let macro_name = Name::from_string("m");
    ctx.bind_name(&name, ScopeId::root());
    let s = ctx.enter_macro_scope(&macro_name);
    ctx.bind_name(&name, s);
    assert_eq!(ctx.bindings_for(&name).len(), 2);
}

// ═══════════════════════════════════════════════════════════════════════════
// resolve_hygienic
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn test_resolve_single_binding() {
    let mut ctx = HygieneContext::new();
    let name = Name::from_string("x");
    ctx.bind_name(&name, ScopeId::root());
    let resolved = resolve_hygienic(&name, &ctx).expect("should resolve");
    assert_eq!(resolved.to_string(), "x");
}

#[test]
fn test_resolve_unbound_fails() {
    let ctx = HygieneContext::new();
    let name = Name::from_string("unknown");
    let err = resolve_hygienic(&name, &ctx).unwrap_err();
    assert!(matches!(err, ElabError::UnknownIdent(_)));
}

#[test]
fn test_resolve_ambiguous_fails() {
    let mut ctx = HygieneContext::new();
    let name = Name::from_string("x");
    ctx.bind_name(&name, ScopeId::root());
    let macro_name = Name::from_string("m");
    let s = ctx.enter_macro_scope(&macro_name);
    ctx.bind_name(&name, s);
    // Both root and child scope are visible -> ambiguous.
    let err = resolve_hygienic(&name, &ctx).unwrap_err();
    assert!(matches!(err, ElabError::MacroError(_)));
}

#[test]
fn test_resolve_same_scope_not_ambiguous() {
    let mut ctx = HygieneContext::new();
    let name = Name::from_string("y");
    ctx.bind_name(&name, ScopeId::root());
    ctx.bind_name(&name, ScopeId::root());
    resolve_hygienic(&name, &ctx).expect("single scope, not ambiguous");
}

// ═══════════════════════════════════════════════════════════════════════════
// colorize_expr
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn test_colorize_const_adds_mdata() {
    let mut ctx = HygieneContext::new();
    let name = Name::from_string("f");
    let macro_name = Name::from_string("m");
    let s = ctx.enter_macro_scope(&macro_name);
    ctx.bind_name(&name, s);

    let expr = Expr::const_str("f");
    let colored = colorize_expr(&expr, &ctx);
    // colorize annotates tracked Const names with MData.
    assert!(
        matches!(colored.kind(), ExprKind::MData(md, _) if !md.is_empty()),
        "expected MData wrapper, got {:?}",
        colored.kind()
    );
}

#[test]
fn test_colorize_untracked_const_unchanged() {
    let ctx = HygieneContext::new();
    let expr = Expr::const_str("untracked");
    let colored = colorize_expr(&expr, &ctx);
    assert!(matches!(colored.kind(), ExprKind::Const(..)));
}

#[test]
fn test_colorize_app_recurses() {
    let mut ctx = HygieneContext::new();
    let name = Name::from_string("g");
    ctx.bind_name(&name, ScopeId::root());

    let f = Expr::const_str("g");
    let a = Expr::bvar(0);
    let app = Expr::app(f, a);
    let colored = colorize_expr(&app, &ctx);
    if let ExprKind::App(func, _) = colored.kind() {
        assert!(matches!(func.kind(), ExprKind::MData(..)));
    } else {
        panic!("expected App");
    }
}

#[test]
fn test_colorize_lam_recurses() {
    let mut ctx = HygieneContext::new();
    let name = Name::from_string("h");
    ctx.bind_name(&name, ScopeId::root());

    let ty = Expr::const_str("h");
    let body = Expr::bvar(0);
    let lam = Expr::lam(clean_kernel::BinderInfo::Default, ty, body);
    let colored = colorize_expr(&lam, &ctx);
    if let ExprKind::Lam(_, ty_out, _) = colored.kind() {
        assert!(matches!(ty_out.kind(), ExprKind::MData(..)));
    } else {
        panic!("expected Lam");
    }
}

#[test]
fn test_colorize_bvar_is_leaf() {
    let ctx = HygieneContext::new();
    let expr = Expr::bvar(0);
    let colored = colorize_expr(&expr, &ctx);
    assert!(matches!(colored.kind(), ExprKind::BVar(0)));
}

// ═══════════════════════════════════════════════════════════════════════════
// alpha_rename_avoiding
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn test_rename_let_avoids_name() {
    let mut ctx = HygieneContext::new();
    let avoid = vec![Name::from_string("x")];
    let ty = Expr::sort(Level::zero());
    let val = Expr::bvar(0);
    let body = Expr::bvar(0);
    let expr = Expr::let_named(Name::from_string("x"), ty, val, body, false);

    let renamed = alpha_rename_avoiding(expr, &avoid, &mut ctx);
    if let ExprKind::Let(nm, _, _, _, _) = renamed.kind() {
        assert_ne!(nm.to_string(), "x", "should have been renamed");
        assert!(nm.to_string().contains("_hyg_"), "should be hygienic name");
    } else {
        panic!("expected Let");
    }
}

#[test]
fn test_rename_preserves_non_colliding() {
    let mut ctx = HygieneContext::new();
    let avoid = vec![Name::from_string("y")];
    let ty = Expr::sort(Level::zero());
    let val = Expr::bvar(0);
    let body = Expr::bvar(0);
    let expr = Expr::let_named(Name::from_string("x"), ty, val, body, false);

    let renamed = alpha_rename_avoiding(expr, &avoid, &mut ctx);
    if let ExprKind::Let(nm, _, _, _, _) = renamed.kind() {
        assert_eq!(nm.to_string(), "x", "non-colliding name should be kept");
    } else {
        panic!("expected Let");
    }
}

#[test]
fn test_rename_const_avoids_name() {
    let mut ctx = HygieneContext::new();
    let avoid = vec![Name::from_string("collide")];
    let expr = Expr::const_str("collide");
    let renamed = alpha_rename_avoiding(expr, &avoid, &mut ctx);
    if let ExprKind::Const(nm, _) = renamed.kind() {
        assert_ne!(nm.to_string(), "collide");
        assert!(nm.to_string().contains("_hyg_"));
    } else {
        panic!("expected Const");
    }
}

#[test]
fn test_rename_app_recurses() {
    let mut ctx = HygieneContext::new();
    let avoid = vec![Name::from_string("collide")];
    let f = Expr::const_str("collide");
    let a = Expr::bvar(0);
    let app = Expr::app(f, a);
    let renamed = alpha_rename_avoiding(app, &avoid, &mut ctx);
    if let ExprKind::App(func, _) = renamed.kind() {
        if let ExprKind::Const(nm, _) = func.kind() {
            assert!(nm.to_string().contains("_hyg_"));
        } else {
            panic!("expected Const in func");
        }
    } else {
        panic!("expected App");
    }
}

#[test]
fn test_rename_empty_avoid_is_identity() {
    let mut ctx = HygieneContext::new();
    let ty = Expr::sort(Level::zero());
    let val = Expr::bvar(0);
    let body = Expr::bvar(0);
    let expr = Expr::let_named(Name::from_string("x"), ty, val, body, false);
    let renamed = alpha_rename_avoiding(expr, &[], &mut ctx);
    if let ExprKind::Let(nm, _, _, _, _) = renamed.kind() {
        assert_eq!(nm.to_string(), "x");
    } else {
        panic!("expected Let");
    }
}

// ═══════════════════════════════════════════════════════════════════════════
// check_hygiene_violation
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn test_no_violations_in_clean_expr() {
    let ctx = HygieneContext::new();
    let expr = Expr::const_str("clean");
    let violations = check_hygiene_violation(&expr, &ctx);
    assert!(violations.is_empty());
}

#[test]
fn test_unresolved_macro_var_detected() {
    let ctx = HygieneContext::new();
    let expr = Expr::const_str("$unresolved");
    let violations = check_hygiene_violation(&expr, &ctx);
    assert_eq!(violations.len(), 1);
    assert_eq!(violations[0].kind, ViolationKind::UnresolvedMacroVar);
}

#[test]
fn test_captured_name_violation() {
    let mut ctx = HygieneContext::new();
    let name = Name::from_string("cap");
    ctx.bind_name(&name, ScopeId::root());
    ctx.mark_captured(&name, ScopeId::root());

    let expr = Expr::const_str("cap");
    let violations = check_hygiene_violation(&expr, &ctx);
    assert_eq!(violations.len(), 1);
    assert_eq!(violations[0].kind, ViolationKind::NameCapture);
}

#[test]
fn test_violation_in_app_subexpression() {
    let ctx = HygieneContext::new();
    let f = Expr::const_str("$leaked");
    let a = Expr::bvar(0);
    let app = Expr::app(f, a);
    let violations = check_hygiene_violation(&app, &ctx);
    assert_eq!(violations.len(), 1);
    assert_eq!(violations[0].kind, ViolationKind::UnresolvedMacroVar);
}

#[test]
fn test_multiple_violations_detected() {
    let ctx = HygieneContext::new();
    let e1 = Expr::const_str("$a");
    let e2 = Expr::const_str("$b");
    let app = Expr::app(e1, e2);
    let violations = check_hygiene_violation(&app, &ctx);
    assert_eq!(violations.len(), 2);
}

// ═══════════════════════════════════════════════════════════════════════════
// Integration and combined scenarios
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn test_scope_stack_returns_all() {
    let mut ctx = HygieneContext::new();
    let m = Name::from_string("m");
    let s1 = ctx.enter_macro_scope(&m);
    let s2 = ctx.enter_macro_scope(&m);
    let stack = ctx.scope_stack();
    assert_eq!(stack.len(), 3);
    assert_eq!(stack[0], ScopeId::root());
    assert_eq!(stack[1], s1);
    assert_eq!(stack[2], s2);
}

#[test]
fn test_default_trait_impl() {
    let ctx = HygieneContext::default();
    assert_eq!(ctx.scope_depth(), 1);
}

#[test]
fn test_violation_kind_display() {
    assert_eq!(format!("{}", ViolationKind::ScopeLeak), "ScopeLeak");
    assert_eq!(format!("{}", ViolationKind::NameCapture), "NameCapture");
    assert_eq!(
        format!("{}", ViolationKind::UnresolvedMacroVar),
        "UnresolvedMacroVar"
    );
}

#[test]
fn test_colorize_then_check_clean() {
    let mut ctx = HygieneContext::new();
    let macro_name = Name::from_string("m");
    let s = ctx.enter_macro_scope(&macro_name);
    let name = Name::from_string("local");
    ctx.bind_name(&name, s);

    let expr = Expr::const_str("local");
    let colored = colorize_expr(&expr, &ctx);
    // While still in scope s, no violations expected.
    let violations = check_hygiene_violation(&colored, &ctx);
    assert!(
        violations.is_empty(),
        "no violations while in defining scope"
    );
}

#[test]
fn test_fresh_name_then_resolve() {
    let mut ctx = HygieneContext::new();
    let macro_name = Name::from_string("m");
    ctx.enter_macro_scope(&macro_name);
    let fresh = ctx.fresh_name("tmp");
    let resolved = resolve_hygienic(&fresh, &ctx).expect("should resolve");
    assert_eq!(resolved.to_string(), fresh.to_string());
}

#[test]
fn test_deeply_nested_scopes() {
    let mut ctx = HygieneContext::new();
    let m = Name::from_string("nest");
    for _ in 0..10 {
        ctx.enter_macro_scope(&m);
    }
    assert_eq!(ctx.scope_depth(), 11);
    for _ in 0..10 {
        ctx.leave_macro_scope();
    }
    assert_eq!(ctx.scope_depth(), 1);
    assert!(ctx.current_scope().is_root());
}

#[test]
fn test_bindings_for_nonexistent() {
    let ctx = HygieneContext::new();
    let name = Name::from_string("ghost");
    assert!(ctx.bindings_for(&name).is_empty());
}

#[test]
fn test_info_for_nonexistent_scope() {
    // Create a scope in one context, look it up in a fresh context where it
    // was never registered.
    let mut ctx1 = HygieneContext::new();
    let m = Name::from_string("m");
    let s = ctx1.enter_macro_scope(&m);

    let ctx2 = HygieneContext::new();
    assert!(ctx2.info_for_scope(s).is_none());
}

#[test]
fn test_colorize_let_recurses_into_children() {
    let mut ctx = HygieneContext::new();
    let name = Name::from_string("tracked");
    ctx.bind_name(&name, ScopeId::root());

    let ty = Expr::const_str("tracked");
    let val = Expr::bvar(0);
    let body = Expr::bvar(0);
    let expr = Expr::let_named(Name::from_string("x"), ty, val, body, false);
    let colored = colorize_expr(&expr, &ctx);

    if let ExprKind::Let(_, ty_out, _, _, _) = colored.kind() {
        assert!(matches!(ty_out.kind(), ExprKind::MData(..)));
    } else {
        panic!("expected Let");
    }
}

#[test]
fn test_scope_info_for_root_exists() {
    let ctx = HygieneContext::new();
    let info = ctx.info_for_scope(ScopeId::root()).expect("root info");
    assert_eq!(info.scope, ScopeId::root());
    assert!(info.macro_name.is_none());
}

#[test]
fn test_fresh_name_different_scopes_are_unique() {
    let mut ctx = HygieneContext::new();
    let n1 = ctx.fresh_name("x");
    let m = Name::from_string("m");
    ctx.enter_macro_scope(&m);
    let n2 = ctx.fresh_name("x");
    assert_ne!(n1.to_string(), n2.to_string());
}

#[test]
fn test_rename_nested_let() {
    let mut ctx = HygieneContext::new();
    let avoid = vec![Name::from_string("x")];
    let ty = Expr::sort(Level::zero());
    let inner_let = Expr::let_named(
        Name::from_string("x"),
        Expr::sort(Level::zero()),
        Expr::bvar(0),
        Expr::bvar(0),
        false,
    );
    let expr = Expr::let_named(Name::from_string("x"), ty, Expr::bvar(0), inner_let, false);
    let renamed = alpha_rename_avoiding(expr, &avoid, &mut ctx);
    // Both outer and inner Let should be renamed.
    if let ExprKind::Let(outer_nm, _, _, inner, _) = renamed.kind() {
        assert!(outer_nm.to_string().contains("_hyg_"));
        if let ExprKind::Let(inner_nm, _, _, _, _) = inner.kind() {
            assert!(inner_nm.to_string().contains("_hyg_"));
        } else {
            panic!("expected inner Let");
        }
    } else {
        panic!("expected outer Let");
    }
}

#[test]
fn test_colorize_preserves_sort_leaf() {
    let ctx = HygieneContext::new();
    let expr = Expr::sort(Level::zero());
    let colored = colorize_expr(&expr, &ctx);
    assert!(matches!(colored.kind(), ExprKind::Sort(_)));
}

#[test]
fn test_resolve_after_leave_scope_fails() {
    let mut ctx = HygieneContext::new();
    let m = Name::from_string("m");
    let s = ctx.enter_macro_scope(&m);
    let name = Name::from_string("inner_only");
    ctx.bind_name(&name, s);
    ctx.leave_macro_scope();
    // Name was bound only in child scope, now at root.
    // resolve_hygienic finds bindings but none visible from root.
    let err = resolve_hygienic(&name, &ctx).unwrap_err();
    assert!(
        matches!(err, ElabError::UnknownIdent(_)),
        "expected UnknownIdent, got {err:?}"
    );
}
