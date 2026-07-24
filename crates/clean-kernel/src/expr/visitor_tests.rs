// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for ExprFolder, ExprVisitor, and ExprFolderOpt traits.

use super::*;
use crate::expr::BinderInfo;
use crate::level::Level;
use crate::name::Name;
use std::sync::Arc;

/// Identity folder: fold_expr should return a structurally equal expression.
struct IdentityFolder;
impl ExprFolder for IdentityFolder {}

#[test]
fn test_identity_fold_bvar() {
    let expr = Expr::bvar(3);
    let mut folder = IdentityFolder;
    let result = folder.fold_expr(&expr);
    assert_eq!(result, expr);
}

#[test]
fn test_identity_fold_app_lam() {
    let body = Expr::bvar(0);
    let lam = Expr::lam(BinderInfo::Default, Expr::prop(), body);
    let app = Expr::app(lam.clone(), Expr::prop());

    let mut folder = IdentityFolder;
    let result = folder.fold_expr(&app);
    assert_eq!(result, app);
}

#[test]
fn test_identity_fold_cubical() {
    let path = Expr::from_kind(ExprKind::CubicalPath {
        ty: Arc::new(Expr::prop()),
        left: Arc::new(Expr::bvar(0)),
        right: Arc::new(Expr::bvar(1)),
    });
    let mut folder = IdentityFolder;
    let result = folder.fold_expr(&path);
    assert_eq!(result, path);
}

#[test]
fn test_identity_fold_zfc() {
    let set = Expr::from_kind(ExprKind::ZFCSet(ZFCSetExpr::Pair(
        Arc::new(Expr::bvar(0)),
        Arc::new(Expr::bvar(1)),
    )));
    let mut folder = IdentityFolder;
    let result = folder.fold_expr(&set);
    assert_eq!(result, set);
}

/// Visitor that collects all free variable IDs.
struct FreeVarCollector {
    fvars: Vec<FVarId>,
}

impl ExprVisitor for FreeVarCollector {
    type Result = ();

    fn combine(&self, _a: (), _b: ()) {}

    fn visit_fvar(&mut self, id: FVarId) {
        self.fvars.push(id);
    }
}

#[test]
fn test_visitor_collect_fvars() {
    let fv1 = FVarId::new(100);
    let fv2 = FVarId::new(200);
    let expr = Expr::app(
        Expr::fvar(fv1),
        Expr::lam(BinderInfo::Default, Expr::prop(), Expr::fvar(fv2)),
    );

    let mut collector = FreeVarCollector { fvars: vec![] };
    collector.visit_expr(&expr);
    assert_eq!(collector.fvars, vec![fv1, fv2]);
}

#[test]
fn test_visitor_no_fvars_in_bvar_expr() {
    let expr = Expr::app(Expr::bvar(0), Expr::bvar(1));
    let mut collector = FreeVarCollector { fvars: vec![] };
    collector.visit_expr(&expr);
    assert!(collector.fvars.is_empty());
}

/// Folder that replaces Sort levels with a fixed level.
struct SortReplacer {
    replacement: Level,
}

impl ExprFolder for SortReplacer {
    fn fold_sort(&mut self, _level: &Level) -> Expr {
        Expr::sort(self.replacement.clone())
    }
}

#[test]
fn test_sort_replacer() {
    let level42 = Level::zero().add_offset(42);
    let expr = Expr::pi(BinderInfo::Default, Expr::prop(), Expr::type_());

    let mut replacer = SortReplacer {
        replacement: level42.clone(),
    };
    let result = replacer.fold_expr(&expr);

    let expected = Expr::pi(
        BinderInfo::Default,
        Expr::sort(level42.clone()),
        Expr::sort(level42),
    );
    assert_eq!(result, expected);
}

/// Visitor that checks if any FVar matches a target.
struct OccursCheck {
    target: FVarId,
}

impl ExprVisitor for OccursCheck {
    type Result = bool;

    fn combine(&self, a: bool, b: bool) -> bool {
        a || b
    }

    fn visit_fvar(&mut self, id: FVarId) -> bool {
        id == self.target
    }
}

#[test]
fn test_occurs_check_found() {
    let target = FVarId::new(42);
    let expr = Expr::app(Expr::bvar(0), Expr::fvar(target));

    let mut checker = OccursCheck { target };
    assert!(checker.visit_expr(&expr));
}

#[test]
fn test_occurs_check_not_found() {
    let target = FVarId::new(42);
    let expr = Expr::app(Expr::bvar(0), Expr::fvar(FVarId::new(99)));

    let mut checker = OccursCheck { target };
    assert!(!checker.visit_expr(&expr));
}

#[test]
fn test_identity_fold_let() {
    let expr = Expr::let_named(
        Name::from_string("x"),
        Expr::prop(),
        Expr::bvar(0),
        Expr::bvar(0),
        false,
    );
    let mut folder = IdentityFolder;
    let result = folder.fold_expr(&expr);
    assert_eq!(result, expr);
}

#[test]
fn test_visitor_cubical_hcomp() {
    let fv = FVarId::new(777);
    let hcomp = Expr::from_kind(ExprKind::CubicalHComp {
        ty: Arc::new(Expr::prop()),
        phi: Arc::new(Expr::fvar(fv)),
        u: Arc::new(Expr::bvar(0)),
        base: Arc::new(Expr::bvar(1)),
    });

    let mut collector = FreeVarCollector { fvars: vec![] };
    collector.visit_expr(&hcomp);
    assert_eq!(collector.fvars, vec![fv]);
}

// ════════════════════════════════════════════════════════════════════════════════
// ExprFolderOpt tests
// ════════════════════════════════════════════════════════════════════════════════

/// Identity fold_opt: all defaults return None (unchanged).
struct IdentityFolderOpt;
impl ExprFolderOpt for IdentityFolderOpt {}

#[test]
fn test_folder_opt_identity_returns_none() {
    let expr = Expr::app(
        Expr::lam(BinderInfo::Default, Expr::prop(), Expr::bvar(0)),
        Expr::fvar(FVarId::new(42)),
    );
    let mut folder = IdentityFolderOpt;
    assert!(
        folder.fold_expr_opt(&expr).is_none(),
        "identity opt folder should return None"
    );
}

#[test]
fn test_folder_opt_identity_cubical_returns_none() {
    let path = Expr::from_kind(ExprKind::CubicalPath {
        ty: Arc::new(Expr::prop()),
        left: Arc::new(Expr::bvar(0)),
        right: Arc::new(Expr::bvar(1)),
    });
    let mut folder = IdentityFolderOpt;
    assert_eq!(folder.fold_expr_opt(&path), None);
}

#[test]
fn test_folder_opt_identity_zfc_returns_none() {
    let set = Expr::from_kind(ExprKind::ZFCSet(ZFCSetExpr::Pair(
        Arc::new(Expr::bvar(0)),
        Arc::new(Expr::bvar(1)),
    )));
    let mut folder = IdentityFolderOpt;
    assert_eq!(folder.fold_expr_opt(&set), None);
}

/// BVar replacer: replaces BVar(0) with an FVar.
struct BVarReplacerOpt {
    target: u32,
    replacement: FVarId,
}

impl ExprFolderOpt for BVarReplacerOpt {
    fn fold_bvar_opt(&mut self, idx: u32) -> Option<Expr> {
        if idx == self.target {
            Some(Expr::fvar(self.replacement))
        } else {
            None
        }
    }
}

#[test]
fn test_folder_opt_bvar_replace() {
    let fv = FVarId::new(999);
    let expr = Expr::app(Expr::bvar(0), Expr::bvar(1));
    let mut folder = BVarReplacerOpt {
        target: 0,
        replacement: fv,
    };
    let result = folder.fold_expr_opt(&expr).expect("should change BVar(0)");
    let expected = Expr::app(Expr::fvar(fv), Expr::bvar(1));
    assert_eq!(result, expected);
}

#[test]
fn test_folder_opt_bvar_no_match_returns_none() {
    let expr = Expr::app(Expr::bvar(5), Expr::bvar(6));
    let mut folder = BVarReplacerOpt {
        target: 0,
        replacement: FVarId::new(1),
    };
    assert_eq!(
        folder.fold_expr_opt(&expr),
        None,
        "no matching BVars should return None"
    );
}

#[test]
fn test_folder_opt_sharing_preserved() {
    // Build App(BVar(5), Lam(_, Prop, BVar(0)))
    // When BVar replacer targets BVar(0), only the Lam body changes.
    // The left child (BVar(5)) should be None -> Arc reused.
    let inner_body = Expr::bvar(0);
    let lam = Expr::lam(BinderInfo::Default, Expr::prop(), inner_body);
    let expr = Expr::app(Expr::bvar(5), lam);

    let fv = FVarId::new(42);
    let mut folder = BVarReplacerOpt {
        target: 0,
        replacement: fv,
    };
    let result = folder
        .fold_expr_opt(&expr)
        .expect("should change BVar(0) in Lam body");
    // The left child (BVar(5)) is unchanged, right child (Lam body) changed.
    let expected = Expr::app(
        Expr::bvar(5),
        Expr::lam(BinderInfo::Default, Expr::prop(), Expr::fvar(fv)),
    );
    assert_eq!(result, expected);
}

/// Binder depth tracker: test that fold_binder_body_opt is called for binders.
struct DepthTracker {
    depth: u32,
    max_depth: u32,
    target_depth: u32,
}

impl ExprFolderOpt for DepthTracker {
    fn fold_bvar_opt(&mut self, idx: u32) -> Option<Expr> {
        if idx == 0 && self.depth == self.target_depth {
            Some(Expr::fvar(FVarId::new(self.depth as u64)))
        } else {
            None
        }
    }

    fn fold_binder_body_opt(&mut self, expr: &Expr) -> Option<Expr> {
        self.depth += 1;
        if self.depth > self.max_depth {
            self.max_depth = self.depth;
        }
        let result = self.fold_expr_opt(expr);
        self.depth -= 1;
        result
    }
}

#[test]
fn test_folder_opt_binder_depth_tracking() {
    // Lam(_, Prop, Lam(_, Prop, BVar(0)))
    // At depth 2, BVar(0) should be replaced.
    let inner = Expr::lam(BinderInfo::Default, Expr::prop(), Expr::bvar(0));
    let outer = Expr::lam(BinderInfo::Default, Expr::prop(), inner);

    let mut tracker = DepthTracker {
        depth: 0,
        max_depth: 0,
        target_depth: 2,
    };
    let result = tracker
        .fold_expr_opt(&outer)
        .expect("should replace at depth 2");
    assert_eq!(tracker.max_depth, 2);

    // Inner BVar(0) at depth=2 replaced with FVar(2)
    let expected = Expr::lam(
        BinderInfo::Default,
        Expr::prop(),
        Expr::lam(
            BinderInfo::Default,
            Expr::prop(),
            Expr::fvar(FVarId::new(2)),
        ),
    );
    assert_eq!(result, expected);
}

#[test]
fn test_folder_opt_should_descend_prunes() {
    struct NeverDescend;
    impl ExprFolderOpt for NeverDescend {
        fn should_descend(&self, _expr: &Expr) -> bool {
            false
        }
        fn fold_bvar_opt(&mut self, _idx: u32) -> Option<Expr> {
            panic!("should not be called");
        }
    }

    let expr = Expr::app(Expr::bvar(0), Expr::bvar(1));
    let mut folder = NeverDescend;
    assert_eq!(folder.fold_expr_opt(&expr), None);
}

#[test]
fn test_fold_opt_convenience_methods() {
    let expr = Expr::bvar(0);
    let fv = FVarId::new(1);
    let mut folder = BVarReplacerOpt {
        target: 0,
        replacement: fv,
    };

    let result = expr.fold_opt(&mut folder).expect("should replace");
    assert_eq!(result, Expr::fvar(fv));

    let mut folder2 = BVarReplacerOpt {
        target: 99,
        replacement: fv,
    };
    let result2 = expr.fold_opt_or_clone(&mut folder2);
    assert_eq!(
        result2, expr,
        "fold_opt_or_clone should return clone when unchanged"
    );
}
