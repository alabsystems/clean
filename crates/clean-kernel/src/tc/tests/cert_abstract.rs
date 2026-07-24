// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for `abstract_fvar_in_expr` — AC2: all ExprKind variants.

use crate::expr::{BinderInfo, Expr, ExprKind, FVarId};
use crate::level::Level;
use crate::name::Name;
use crate::tc::cert::abstract_fvar_in_expr;
use std::sync::Arc;

#[test]
fn test_abstract_fvar_replaces_matching_fvar_with_bvar() {
    let fvar_id = FVarId::new(42);
    let e = Expr::from_kind(ExprKind::FVar(fvar_id));
    let result = abstract_fvar_in_expr(e, fvar_id, 0);
    assert_eq!(result.kind, ExprKind::BVar(0));
}

#[test]
fn test_abstract_fvar_leaves_non_matching_fvar() {
    let target = FVarId::new(42);
    let other = FVarId::new(99);
    let e = Expr::from_kind(ExprKind::FVar(other));
    let result = abstract_fvar_in_expr(e, target, 0);
    assert_eq!(result.kind, ExprKind::FVar(other));
}

#[test]
fn test_abstract_fvar_shifts_bvar_at_depth() {
    let fvar_id = FVarId::new(1);
    // BVar(0) at depth 0 should be shifted to BVar(1)
    let e = Expr::from_kind(ExprKind::BVar(0));
    let result = abstract_fvar_in_expr(e, fvar_id, 0);
    assert_eq!(result.kind, ExprKind::BVar(1));
}

#[test]
fn test_abstract_fvar_no_shift_bvar_below_depth() {
    let fvar_id = FVarId::new(1);
    // BVar(0) at depth 1 should NOT be shifted (0 < 1)
    let e = Expr::from_kind(ExprKind::BVar(0));
    let result = abstract_fvar_in_expr(e, fvar_id, 1);
    assert_eq!(result.kind, ExprKind::BVar(0));
}

#[test]
fn test_abstract_fvar_sort_unchanged() {
    let fvar_id = FVarId::new(1);
    let e = Expr::from_kind(ExprKind::Sort(Level::zero()));
    let result = abstract_fvar_in_expr(e.clone(), fvar_id, 0);
    assert_eq!(result.kind, e.kind);
}

#[test]
fn test_abstract_fvar_const_unchanged() {
    let fvar_id = FVarId::new(1);
    let e = Expr::const_str("Nat");
    let result = abstract_fvar_in_expr(e.clone(), fvar_id, 0);
    assert_eq!(result.kind, e.kind);
}

#[test]
fn test_abstract_fvar_lit_unchanged() {
    let fvar_id = FVarId::new(1);
    let e = Expr::nat_lit(42);
    let result = abstract_fvar_in_expr(e.clone(), fvar_id, 0);
    assert_eq!(result.kind, e.kind);
}

#[test]
fn test_abstract_fvar_in_app() {
    let fvar_id = FVarId::new(10);
    let f = Expr::from_kind(ExprKind::FVar(fvar_id));
    let a = Expr::from_kind(ExprKind::FVar(fvar_id));
    let e = Expr::from_kind(ExprKind::App(Arc::new(f), Arc::new(a)));
    let result = abstract_fvar_in_expr(e, fvar_id, 0);
    match &result.kind {
        ExprKind::App(rf, ra) => {
            assert_eq!(rf.kind, ExprKind::BVar(0));
            assert_eq!(ra.kind, ExprKind::BVar(0));
        }
        other => panic!("expected App, got {:?}", other),
    }
}

#[test]
fn test_abstract_fvar_in_lam_increments_depth() {
    let fvar_id = FVarId::new(20);
    let body = Expr::from_kind(ExprKind::FVar(fvar_id));
    let ty = Expr::from_kind(ExprKind::Sort(Level::zero()));
    let e = Expr::from_kind(ExprKind::Lam(
        BinderInfo::Default.into(),
        Arc::new(ty),
        Arc::new(body),
    ));
    let result = abstract_fvar_in_expr(e, fvar_id, 0);
    match &result.kind {
        ExprKind::Lam(_, _, body) => {
            assert_eq!(body.kind, ExprKind::BVar(1));
        }
        other => panic!("expected Lam, got {:?}", other),
    }
}

#[test]
fn test_abstract_fvar_in_pi_increments_depth() {
    let fvar_id = FVarId::new(30);
    let body = Expr::from_kind(ExprKind::FVar(fvar_id));
    let ty = Expr::from_kind(ExprKind::FVar(fvar_id));
    let e = Expr::from_kind(ExprKind::Pi(
        BinderInfo::Default.into(),
        Arc::new(ty),
        Arc::new(body),
    ));
    let result = abstract_fvar_in_expr(e, fvar_id, 0);
    match &result.kind {
        ExprKind::Pi(_, ty, body) => {
            assert_eq!(ty.kind, ExprKind::BVar(0), "type at depth 0 → BVar(0)");
            assert_eq!(body.kind, ExprKind::BVar(1), "body at depth 1 → BVar(1)");
        }
        other => panic!("expected Pi, got {:?}", other),
    }
}

#[test]
fn test_abstract_fvar_in_let_increments_depth_in_body() {
    let fvar_id = FVarId::new(40);
    let fvar_expr = Expr::from_kind(ExprKind::FVar(fvar_id));
    let ty = Expr::from_kind(ExprKind::Sort(Level::zero()));
    let val = fvar_expr.clone();
    let body = fvar_expr;
    let e = Expr::from_kind(ExprKind::Let(
        Name::anon(),
        Arc::new(ty),
        Arc::new(val),
        Arc::new(body),
        false,
    ));
    let result = abstract_fvar_in_expr(e, fvar_id, 0);
    match &result.kind {
        ExprKind::Let(_, _ty, val, body, _) => {
            assert_eq!(val.kind, ExprKind::BVar(0), "val at depth 0 → BVar(0)");
            assert_eq!(body.kind, ExprKind::BVar(1), "body at depth 1 → BVar(1)");
        }
        other => panic!("expected Let, got {:?}", other),
    }
}

#[test]
fn test_abstract_fvar_in_proj() {
    let fvar_id = FVarId::new(50);
    let inner = Expr::from_kind(ExprKind::FVar(fvar_id));
    let e = Expr::from_kind(ExprKind::Proj(
        Name::from_string("Prod"),
        0,
        Arc::new(inner),
    ));
    let result = abstract_fvar_in_expr(e, fvar_id, 0);
    match &result.kind {
        ExprKind::Proj(_, _, inner) => {
            assert_eq!(inner.kind, ExprKind::BVar(0));
        }
        other => panic!("expected Proj, got {:?}", other),
    }
}

#[test]
fn test_abstract_fvar_in_mdata() {
    let fvar_id = FVarId::new(60);
    let inner = Expr::from_kind(ExprKind::FVar(fvar_id));
    let e = Expr::from_kind(ExprKind::MData(vec![], Arc::new(inner)));
    let result = abstract_fvar_in_expr(e, fvar_id, 0);
    match &result.kind {
        ExprKind::MData(_, inner) => {
            assert_eq!(inner.kind, ExprKind::BVar(0));
        }
        other => panic!("expected MData, got {:?}", other),
    }
}

#[test]
fn test_abstract_fvar_sprop_unchanged() {
    let fvar_id = FVarId::new(1);
    let e = Expr::from_kind(ExprKind::SProp);
    let result = abstract_fvar_in_expr(e.clone(), fvar_id, 0);
    assert_eq!(result.kind, e.kind);
}

#[test]
fn test_abstract_fvar_in_squash() {
    let fvar_id = FVarId::new(70);
    let inner = Expr::from_kind(ExprKind::FVar(fvar_id));
    let e = Expr::from_kind(ExprKind::Squash(Arc::new(inner)));
    let result = abstract_fvar_in_expr(e, fvar_id, 0);
    match &result.kind {
        ExprKind::Squash(inner) => {
            assert_eq!(inner.kind, ExprKind::BVar(0));
        }
        other => panic!("expected Squash, got {:?}", other),
    }
}

#[test]
fn test_abstract_fvar_cubical_interval_unchanged() {
    let fvar_id = FVarId::new(1);
    let e = Expr::from_kind(ExprKind::CubicalInterval);
    let result = abstract_fvar_in_expr(e.clone(), fvar_id, 0);
    assert_eq!(result.kind, e.kind);
}

#[test]
fn test_abstract_fvar_cubical_i0_i1_unchanged() {
    let fvar_id = FVarId::new(1);
    let e0 = Expr::from_kind(ExprKind::CubicalI0);
    let e1 = Expr::from_kind(ExprKind::CubicalI1);
    assert_eq!(abstract_fvar_in_expr(e0.clone(), fvar_id, 0).kind, e0.kind);
    assert_eq!(abstract_fvar_in_expr(e1.clone(), fvar_id, 0).kind, e1.kind);
}

#[test]
fn test_abstract_fvar_in_cubical_path() {
    let fvar_id = FVarId::new(80);
    let fvar = Expr::from_kind(ExprKind::FVar(fvar_id));
    let e = Expr::from_kind(ExprKind::CubicalPath {
        ty: Arc::new(fvar.clone()),
        left: Arc::new(fvar.clone()),
        right: Arc::new(fvar),
    });
    let result = abstract_fvar_in_expr(e, fvar_id, 0);
    match &result.kind {
        ExprKind::CubicalPath { ty, left, right } => {
            assert_eq!(ty.kind, ExprKind::BVar(0));
            assert_eq!(left.kind, ExprKind::BVar(0));
            assert_eq!(right.kind, ExprKind::BVar(0));
        }
        other => panic!("expected CubicalPath, got {:?}", other),
    }
}

#[test]
fn test_abstract_fvar_in_cubical_path_lam_increments_depth() {
    let fvar_id = FVarId::new(81);
    let fvar = Expr::from_kind(ExprKind::FVar(fvar_id));
    let e = Expr::from_kind(ExprKind::CubicalPathLam {
        body: Arc::new(fvar),
    });
    let result = abstract_fvar_in_expr(e, fvar_id, 0);
    match &result.kind {
        ExprKind::CubicalPathLam { body } => {
            assert_eq!(
                body.kind,
                ExprKind::BVar(1),
                "path lam body depth incremented"
            );
        }
        other => panic!("expected CubicalPathLam, got {:?}", other),
    }
}

#[test]
fn test_abstract_fvar_in_cubical_path_app() {
    let fvar_id = FVarId::new(82);
    let fvar = Expr::from_kind(ExprKind::FVar(fvar_id));
    let e = Expr::from_kind(ExprKind::CubicalPathApp {
        path: Arc::new(fvar.clone()),
        arg: Arc::new(fvar),
    });
    let result = abstract_fvar_in_expr(e, fvar_id, 0);
    match &result.kind {
        ExprKind::CubicalPathApp { path, arg } => {
            assert_eq!(path.kind, ExprKind::BVar(0));
            assert_eq!(arg.kind, ExprKind::BVar(0));
        }
        other => panic!("expected CubicalPathApp, got {:?}", other),
    }
}

#[test]
fn test_abstract_fvar_in_cubical_hcomp() {
    let fvar_id = FVarId::new(83);
    let fvar = Expr::from_kind(ExprKind::FVar(fvar_id));
    let e = Expr::from_kind(ExprKind::CubicalHComp {
        ty: Arc::new(fvar.clone()),
        phi: Arc::new(fvar.clone()),
        u: Arc::new(fvar.clone()),
        base: Arc::new(fvar),
    });
    let result = abstract_fvar_in_expr(e, fvar_id, 0);
    match &result.kind {
        ExprKind::CubicalHComp {
            ty, phi, u, base, ..
        } => {
            assert_eq!(ty.kind, ExprKind::BVar(0));
            assert_eq!(phi.kind, ExprKind::BVar(0));
            assert_eq!(u.kind, ExprKind::BVar(0));
            assert_eq!(base.kind, ExprKind::BVar(0));
        }
        other => panic!("expected CubicalHComp, got {:?}", other),
    }
}

#[test]
fn test_abstract_fvar_in_cubical_transp() {
    let fvar_id = FVarId::new(84);
    let fvar = Expr::from_kind(ExprKind::FVar(fvar_id));
    let e = Expr::from_kind(ExprKind::CubicalTransp {
        ty: Arc::new(fvar.clone()),
        phi: Arc::new(fvar.clone()),
        base: Arc::new(fvar),
    });
    let result = abstract_fvar_in_expr(e, fvar_id, 0);
    match &result.kind {
        ExprKind::CubicalTransp { ty, phi, base } => {
            assert_eq!(ty.kind, ExprKind::BVar(0));
            assert_eq!(phi.kind, ExprKind::BVar(0));
            assert_eq!(base.kind, ExprKind::BVar(0));
        }
        other => panic!("expected CubicalTransp, got {:?}", other),
    }
}

#[test]
fn test_abstract_fvar_in_zfc_mem() {
    let fvar_id = FVarId::new(85);
    let fvar = Expr::from_kind(ExprKind::FVar(fvar_id));
    let e = Expr::from_kind(ExprKind::ZFCMem {
        element: Arc::new(fvar.clone()),
        set: Arc::new(fvar),
    });
    let result = abstract_fvar_in_expr(e, fvar_id, 0);
    match &result.kind {
        ExprKind::ZFCMem { element, set } => {
            assert_eq!(element.kind, ExprKind::BVar(0));
            assert_eq!(set.kind, ExprKind::BVar(0));
        }
        other => panic!("expected ZFCMem, got {:?}", other),
    }
}

#[test]
fn test_abstract_fvar_in_zfc_comprehension_increments_depth() {
    let fvar_id = FVarId::new(86);
    let fvar = Expr::from_kind(ExprKind::FVar(fvar_id));
    let e = Expr::from_kind(ExprKind::ZFCComprehension {
        domain: Arc::new(fvar.clone()),
        pred: Arc::new(fvar),
    });
    let result = abstract_fvar_in_expr(e, fvar_id, 0);
    match &result.kind {
        ExprKind::ZFCComprehension { domain, pred } => {
            assert_eq!(
                domain.kind,
                ExprKind::BVar(0),
                "domain at depth 0 → BVar(0)"
            );
            assert_eq!(
                pred.kind,
                ExprKind::BVar(1),
                "pred under comprehension binder → BVar(depth+1)"
            );
        }
        other => panic!("expected ZFCComprehension, got {:?}", other),
    }
}
