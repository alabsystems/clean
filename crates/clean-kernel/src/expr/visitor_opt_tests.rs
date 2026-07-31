// Copyright 2026 Andrew Yates Apache 2.0.
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Tests for ExprFolderOpt trait.
// Included via include!() from visitor_opt.rs.

use super::*;
use crate::expr::types::{BinderInfo, FVarId, Literal};
use crate::name::Name;

/// No-op ExprFolderOpt: all defaults return None (no change).
struct NoopFolderOpt;
impl ExprFolderOpt for NoopFolderOpt {}

#[test]
fn test_folder_opt_noop_returns_none() {
    let mut f = NoopFolderOpt;
    assert_eq!(f.fold_expr_opt(&Expr::bvar(42)), None);
    assert_eq!(f.fold_expr_opt(&Expr::fvar(FVarId::new(1))), None);
    assert_eq!(f.fold_expr_opt(&Expr::const_str("Nat")), None);
}

#[test]
fn test_folder_opt_noop_app_returns_none() {
    let mut f = NoopFolderOpt;
    let expr = Expr::app(Expr::const_str("Nat.add"), Expr::bvar(0));
    assert_eq!(f.fold_expr_opt(&expr), None);
}

#[test]
fn test_folder_opt_noop_nested_returns_none() {
    let mut f = NoopFolderOpt;
    let expr = Expr::lam(
        BinderInfo::Default,
        Expr::const_str("Nat"),
        Expr::app(Expr::bvar(0), Expr::bvar(1)),
    );
    assert_eq!(f.fold_expr_opt(&expr), None);
}

#[test]
fn test_folder_opt_noop_let_returns_none() {
    let mut f = NoopFolderOpt;
    let expr = Expr::let_named(
        Name::anon(),
        Expr::const_str("Nat"),
        Expr::nat_lit(5),
        Expr::bvar(0),
        false,
    );
    assert_eq!(f.fold_expr_opt(&expr), None);
}

#[test]
fn test_folder_opt_noop_proj_returns_none() {
    let mut f = NoopFolderOpt;
    let expr = Expr::proj(Name::from_string("Prod"), 0, Expr::bvar(0));
    assert_eq!(f.fold_expr_opt(&expr), None);
}

/// Leaf override: increment all BVars by 1.
struct IncrBVarsOpt;
impl ExprFolderOpt for IncrBVarsOpt {
    fn fold_bvar_opt(&mut self, idx: u32) -> Option<Expr> {
        Some(Expr::bvar(idx + 1))
    }
}

#[test]
fn test_folder_opt_leaf_override_simple() {
    let mut f = IncrBVarsOpt;
    let expr = Expr::bvar(3);
    let result = f
        .fold_expr_opt(&expr)
        .expect("BVar(3) should be incremented");
    assert_eq!(*result.kind(), ExprKind::BVar(4));
}

#[test]
fn test_folder_opt_leaf_override_propagates_through_app() {
    let mut f = IncrBVarsOpt;
    let expr = Expr::app(Expr::bvar(0), Expr::bvar(1));
    let result = f.fold_expr_opt(&expr).expect("should change");
    if let ExprKind::App(func, arg) = result.kind() {
        assert_eq!(*func.kind(), ExprKind::BVar(1));
        assert_eq!(*arg.kind(), ExprKind::BVar(2));
    } else {
        panic!("expected App");
    }
}

#[test]
fn test_folder_opt_unchanged_child_preserves_sharing() {
    // App(Const("Nat"), BVar(0)) — only BVar changes.
    let nat = Expr::const_str("Nat");
    let expr = Expr::app(nat.clone(), Expr::bvar(0));
    let mut f = IncrBVarsOpt;
    let result = f
        .fold_expr_opt(&expr)
        .expect("BVar changed, so App changed");
    if let ExprKind::App(func, arg) = result.kind() {
        assert_eq!(*func.kind(), *nat.kind());
        assert_eq!(*arg.kind(), ExprKind::BVar(1));
    } else {
        panic!("expected App");
    }
}

#[test]
fn test_folder_opt_or_clone_unchanged() {
    let mut f = NoopFolderOpt;
    let expr = Expr::bvar(42);
    let result = f.fold_expr_or_clone(&expr);
    assert_eq!(result.kind(), expr.kind());
}

#[test]
fn test_folder_opt_or_clone_changed() {
    let mut f = IncrBVarsOpt;
    let expr = Expr::bvar(42);
    let result = f.fold_expr_or_clone(&expr);
    assert_eq!(*result.kind(), ExprKind::BVar(43));
}

/// Binder depth tracking: count enter/exit calls.
struct BinderDepthTracker {
    depth: u32,
    max_depth: u32,
}
impl ExprFolderOpt for BinderDepthTracker {
    fn enter_binder(&mut self) {
        self.depth += 1;
        self.max_depth = self.max_depth.max(self.depth);
    }
    fn exit_binder(&mut self) {
        self.depth -= 1;
    }
    fn fold_bvar_opt(&mut self, idx: u32) -> Option<Expr> {
        Some(Expr::bvar(idx))
    }
}

#[test]
fn test_folder_opt_binder_depth_lam() {
    let mut f = BinderDepthTracker {
        depth: 0,
        max_depth: 0,
    };
    let expr = Expr::lam(BinderInfo::Default, Expr::bvar(0), Expr::bvar(0));
    f.fold_expr_opt(&expr);
    assert_eq!(f.depth, 0, "depth should return to 0 after fold");
    assert_eq!(f.max_depth, 1, "should enter 1 binder");
}

#[test]
fn test_folder_opt_binder_depth_nested() {
    let mut f = BinderDepthTracker {
        depth: 0,
        max_depth: 0,
    };
    let inner = Expr::lam(BinderInfo::Default, Expr::const_str("Bool"), Expr::bvar(0));
    let expr = Expr::lam(BinderInfo::Default, Expr::const_str("Nat"), inner);
    f.fold_expr_opt(&expr);
    assert_eq!(f.depth, 0);
    assert_eq!(f.max_depth, 2, "should enter 2 nested binders");
}

#[test]
fn test_folder_opt_binder_depth_pi() {
    let mut f = BinderDepthTracker {
        depth: 0,
        max_depth: 0,
    };
    let expr = Expr::pi(BinderInfo::Default, Expr::bvar(0), Expr::bvar(0));
    f.fold_expr_opt(&expr);
    assert_eq!(f.depth, 0);
    assert_eq!(f.max_depth, 1);
}

#[test]
fn test_folder_opt_binder_depth_let() {
    let mut f = BinderDepthTracker {
        depth: 0,
        max_depth: 0,
    };
    let expr = Expr::let_named(
        Name::anon(),
        Expr::bvar(0),
        Expr::bvar(0),
        Expr::bvar(0),
        false,
    );
    f.fold_expr_opt(&expr);
    assert_eq!(f.depth, 0);
    assert_eq!(f.max_depth, 1, "Let body is inside a binder");
}

/// should_skip guard test.
struct SkipEverything;
impl ExprFolderOpt for SkipEverything {
    fn should_skip(&self, _expr: &Expr) -> bool {
        true
    }
    fn fold_bvar_opt(&mut self, _idx: u32) -> Option<Expr> {
        panic!("should not be called when skipped");
    }
}

#[test]
fn test_folder_opt_should_skip() {
    let mut f = SkipEverything;
    assert_eq!(f.fold_expr_opt(&Expr::bvar(42)), None);
    assert_eq!(
        f.fold_expr_opt(&Expr::app(Expr::bvar(0), Expr::bvar(1))),
        None
    );
}

/// FVar substitution (like subst_fvar_opt).
struct SubstFVarOpt {
    target: FVarId,
    replacement: Expr,
}
impl ExprFolderOpt for SubstFVarOpt {
    fn should_skip(&self, expr: &Expr) -> bool {
        !expr.has_fvar_quick()
    }
    fn fold_fvar_opt(&mut self, id: FVarId) -> Option<Expr> {
        if id == self.target {
            Some(self.replacement.clone())
        } else {
            None
        }
    }
}

#[test]
fn test_folder_opt_subst_fvar() {
    let target = FVarId::new(42);
    let mut f = SubstFVarOpt {
        target,
        replacement: Expr::nat_lit(7),
    };
    let expr = Expr::app(Expr::fvar(target), Expr::bvar(0));
    let result = f.fold_expr_opt(&expr).expect("FVar changed");
    if let ExprKind::App(func, _arg) = result.kind() {
        assert_eq!(*func.kind(), ExprKind::Lit(Literal::Nat(7u64.into())));
    } else {
        panic!("expected App");
    }
}

#[test]
fn test_folder_opt_subst_fvar_no_match() {
    let mut f = SubstFVarOpt {
        target: FVarId::new(42),
        replacement: Expr::nat_lit(7),
    };
    let expr = Expr::app(Expr::fvar(FVarId::new(99)), Expr::bvar(0));
    assert_eq!(
        f.fold_expr_opt(&expr),
        None,
        "non-matching FVar should return None"
    );
}
