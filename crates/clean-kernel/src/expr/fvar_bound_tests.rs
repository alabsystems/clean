// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::{BinderInfo, Name};
use std::mem::{align_of, size_of};
use std::sync::Arc;

fn f(id: u64) -> Expr {
    Expr::fvar(FVarId::new(id))
}
fn all_children(x: Arc<Expr>) -> Vec<Expr> {
    let z = Arc::new(Expr::prop());
    let mut cases = vec![
        Expr::app_arc(x.clone(), z.clone()),
        Expr::app_arc(z.clone(), x.clone()),
    ];
    for binder in [false, true] {
        for (a, b) in [(x.clone(), z.clone()), (z.clone(), x.clone())] {
            cases.push(Expr::from_kind(if binder {
                ExprKind::Pi(BinderInfo::Default.into(), a, b)
            } else {
                ExprKind::Lam(BinderInfo::Default.into(), a, b)
            }));
        }
    }
    for (ty, value, body) in [
        (x.clone(), z.clone(), z.clone()),
        (z.clone(), x.clone(), z.clone()),
        (z.clone(), z.clone(), x.clone()),
    ] {
        cases.push(Expr::from_kind(ExprKind::Let(
            Name::anon(),
            ty,
            value,
            body,
            false,
        )));
    }
    cases.extend([
        Expr::from_kind(ExprKind::Proj(Name::anon(), 0, x.clone())),
        Expr::from_kind(ExprKind::MData(Default::default(), x.clone())),
        Expr::from_kind(ExprKind::Squash(x.clone())),
        Expr::from_kind(ExprKind::CubicalPathLam { body: x.clone() }),
        Expr::from_kind(ExprKind::CubicalPathApp {
            path: x.clone(),
            arg: z.clone(),
        }),
        Expr::from_kind(ExprKind::CubicalPathApp {
            path: z.clone(),
            arg: x.clone(),
        }),
        Expr::from_kind(ExprKind::ZFCSet(crate::expr::ZFCSetExpr::Singleton(
            x.clone(),
        ))),
        Expr::from_kind(ExprKind::ZFCMem {
            element: x.clone(),
            set: z.clone(),
        }),
        Expr::from_kind(ExprKind::ZFCMem {
            element: z.clone(),
            set: x.clone(),
        }),
        Expr::from_kind(ExprKind::ZFCComprehension {
            domain: x.clone(),
            pred: z.clone(),
        }),
        Expr::from_kind(ExprKind::ZFCComprehension {
            domain: z.clone(),
            pred: x.clone(),
        }),
    ]);
    for (a, b, c) in [
        (x.clone(), z.clone(), z.clone()),
        (z.clone(), x.clone(), z.clone()),
        (z.clone(), z.clone(), x.clone()),
    ] {
        cases.push(Expr::from_kind(ExprKind::CubicalPath {
            ty: a.clone(),
            left: b.clone(),
            right: c.clone(),
        }));
        cases.push(Expr::from_kind(ExprKind::CubicalTransp {
            ty: a,
            phi: b,
            base: c,
        }));
    }
    for (a, b, c, d) in [
        (x.clone(), z.clone(), z.clone(), z.clone()),
        (z.clone(), x.clone(), z.clone(), z.clone()),
        (z.clone(), z.clone(), x.clone(), z.clone()),
        (z.clone(), z.clone(), z.clone(), x),
    ] {
        cases.push(Expr::from_kind(ExprKind::CubicalHComp {
            ty: a.clone(),
            phi: b.clone(),
            u: c.clone(),
            base: d.clone(),
        }));
        cases.push(Expr::from_kind(ExprKind::CubicalCoe {
            ty: a,
            r: b,
            s: c,
            base: d,
        }));
    }
    cases
}

#[test]
fn every_structural_child_preserves_present_targets_and_matches_unhinted_folds() {
    for id in [0, 42, u64::MAX] {
        let target = FVarId::new(id);
        for term in all_children(Arc::new(f(id))) {
            assert!(term.may_contain_fvar(target));
            assert_eq!(
                term.abstract_fvar(target),
                without_hint(|| term.abstract_fvar(target))
            );
            assert_eq!(
                term.subst_fvar(target, &Expr::nat_lit(17)),
                without_hint(|| term.subst_fvar(target, &Expr::nat_lit(17)))
            );
        }
    }
}

#[test]
fn absent_fvar_never_skips_required_loose_bvar_shifts() {
    let target = FVarId::new(9);
    let body = Expr::app(f(1), Expr::bvar(0));
    assert_eq!(body.abstract_fvar(target), Expr::app(f(1), Expr::bvar(1)));
    let under = Expr::lam(
        BinderInfo::Default,
        Expr::prop(),
        Expr::app(f(1), Expr::bvar(1)),
    );
    assert_eq!(
        under.abstract_fvar(target),
        Expr::lam(
            BinderInfo::Default,
            Expr::prop(),
            Expr::app(f(1), Expr::bvar(2))
        )
    );
    assert_eq!(
        under.abstract_fvar(target),
        without_hint(|| under.abstract_fvar(target))
    );
}

#[test]
fn arbitrary_ids_max_and_removing_the_largest_keep_conservative_bounds() {
    assert!(f(0).may_contain_fvar(FVarId::new(0)));
    assert!(!Expr::prop().may_contain_fvar(FVarId::new(0)));
    let term = Expr::apps(f(999), [f(2), f(42)]);
    assert!(
        term.may_contain_fvar(FVarId::new(7)),
        "false-positive support hints are allowed"
    );
    assert!(!term.may_contain_fvar(FVarId::new(1000)));
    let reduced = term.abstract_fvar(FVarId::new(999));
    assert!(!reduced.may_contain_fvar(FVarId::new(999)));
    assert!(reduced.may_contain_fvar(FVarId::new(42)));
    assert_eq!(
        f(u64::MAX).abstract_fvar(FVarId::new(u64::MAX)),
        Expr::bvar(0)
    );
}

#[test]
fn clone_precomputed_meta_and_serde_recompute_or_preserve_the_actual_hint() {
    let term = Expr::app(f(900), f(3));
    let clone = term.clone();
    let with_meta = Expr::with_meta(term.kind().clone(), term.meta());
    let bytes = serde_json::to_vec(&term).unwrap();
    assert!(!String::from_utf8_lossy(&bytes).contains("upper_bound"));
    let restored: Expr = serde_json::from_slice(&bytes).unwrap();
    for actual in [clone, with_meta, restored] {
        assert_eq!(actual.fvar_upper_bound, 900);
        assert_eq!(serde_json::to_vec(&actual).unwrap(), bytes);
        assert_eq!(
            actual.abstract_fvar(FVarId::new(900)),
            without_hint(|| term.abstract_fvar(FVarId::new(900)))
        );
    }
}

#[test]
fn shared_dag_at_many_depths_avoids_repeated_absent_target_work() {
    let mut shared = Arc::new(f(1));
    for _ in 0..64 {
        shared = Arc::new(Expr::app_arc(
            shared.clone(),
            Arc::new(Expr::lam_arc(
                BinderInfo::Default,
                Arc::new(Expr::prop()),
                shared,
            )),
        ));
    }
    let _ = crate::work_meter::stats::take();
    for id in 2..18 {
        assert_eq!(shared.abstract_fvar(FVarId::new(id)), *shared);
    }
    let hinted = crate::work_meter::stats::take().fold_nodes;
    without_hint(|| {
        for id in 2..18 {
            assert_eq!(shared.abstract_fvar(FVarId::new(id)), *shared);
        }
    });
    let unhinted = crate::work_meter::stats::take().fold_nodes;
    eprintln!("FVar hint diagnostic: hinted={hinted}, unhinted={unhinted}");
    assert!(unhinted > 1000);
    assert!(hinted < unhinted / 50);
}

#[test]
fn expression_layout_and_contextual_fallback_are_explicit() {
    eprintln!(
        "Expr layout: size={}, align={}",
        size_of::<Expr>(),
        align_of::<Expr>()
    );
    let unknown = Expr::from_kind(ExprKind::ZFCSet(crate::expr::ZFCSetExpr::Singleton(
        Arc::new(f(1)),
    )));
    assert_eq!(unknown.fvar_upper_bound, u64::MAX);
    assert!(unknown.may_contain_fvar(FVarId::new(u64::MAX)));
    assert_eq!(
        unknown.abstract_fvar(FVarId::new(2)),
        without_hint(|| unknown.abstract_fvar(FVarId::new(2)))
    );
}
