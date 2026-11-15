// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Structural FVar-context guard regressions, not typing rules for these terms.
//! The shallow oracle deliberately preserves the current opaque ZFC behavior.
//! Deep fixtures use ordinary Expr/Arc destruction; no nodes are leaked and no
//! larger thread stack or checker resource limit is requested by these tests.

use super::*;
use crate::env::Environment;
use crate::expr::{BinderInfo, FVarId, ZFCSetExpr};
use std::sync::Arc;

const DEEP: usize = 50_000;

fn push(tc: &TypeChecker<'_>, name: &str) -> FVarId {
    tc.push_binder_local(Name::from_string(name), Expr::type_(), BinderInfo::Default)
}

#[test]
fn fvar_context_walk_handles_50000_app_nodes_and_rechecks_after_pop() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);
    let id = push(&tc, "app_leaf");
    let mut root = Arc::new(Expr::fvar(id));
    let leaf = Arc::downgrade(&root);
    let closed = Arc::new(Expr::bvar(0));
    for _ in 0..DEEP {
        root = Arc::new(Expr::app_arc(root, closed.clone()));
    }
    assert!(tc.all_fvars_in_context(&root));
    tc.pop_binder_local();
    assert!(!tc.all_fvars_in_context(&root));
    let sibling = push(&tc, "new_app_leaf");
    assert_ne!(id, sibling);
    assert!(
        !tc.all_fvars_in_context(&root),
        "same context length is not membership"
    );
    tc.pop_binder_local();
    drop(root); // Expr's existing iterative Drop owns the deep cleanup.
    assert!(
        leaf.upgrade().is_none(),
        "the deepest Arc was actually released"
    );
}

#[test]
fn fvar_context_walk_handles_50000_mixed_binders_and_rechecks_after_pop() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);
    let id = push(&tc, "binder_leaf");
    let mut root = Arc::new(Expr::fvar(id));
    let leaf = Arc::downgrade(&root);
    let closed = Arc::new(Expr::bvar(0));
    for depth in 0..DEEP {
        root = Arc::new(match depth % 3 {
            0 => Expr::lam_arc(BinderInfo::Default, closed.clone(), root),
            1 => Expr::pi_arc(BinderInfo::Default, closed.clone(), root),
            _ => Expr::let_named_arc(Name::anon(), closed.clone(), closed.clone(), root, false),
        });
    }
    assert!(tc.all_fvars_in_context(&root));
    tc.pop_binder_local();
    assert!(!tc.all_fvars_in_context(&root));
    drop(root);
    assert!(
        leaf.upgrade().is_none(),
        "binder teardown must not leak its leaf"
    );
}

#[test]
fn fvar_context_walk_preserves_diamond_sharing_and_checks_a_stale_late_branch() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);
    let live = push(&tc, "shared");
    let stale = push(&tc, "late");
    let mut diamond = Arc::new(Expr::fvar(live));
    let shared_leaf = Arc::downgrade(&diamond);
    // A tree walk would revisit the same leaf 2^48 times. Each pair really
    // shares one Arc; no structural-equality or timing threshold is assumed.
    for _ in 0..48 {
        diamond = Arc::new(Expr::app_arc(diamond.clone(), diamond));
    }
    let ExprKind::App(left, right) = diamond.kind() else {
        panic!("diamond")
    };
    assert!(Arc::ptr_eq(left, right));
    let late = Arc::new(Expr::fvar(stale));
    let late_leaf = Arc::downgrade(&late);
    let root = Expr::app_arc(diamond.clone(), late);
    let reversed = Expr::app_arc(Arc::new(Expr::fvar(stale)), diamond.clone());
    assert!(tc.all_fvars_in_context(&root));
    assert!(tc.all_fvars_in_context(&reversed));
    tc.pop_binder_local();
    assert!(
        tc.all_fvars_in_context(&diamond),
        "the shared prefix is still live"
    );
    assert!(
        !tc.all_fvars_in_context(&root),
        "do not skip the later unique child"
    );
    assert!(
        !tc.all_fvars_in_context(&reversed),
        "both child positions matter"
    );
    let sibling = push(&tc, "replacement");
    assert_ne!(sibling, stale);
    assert!(
        !tc.all_fvars_in_context(&root),
        "walk state is per invocation"
    );
    tc.pop_binder_local();
    tc.pop_binder_local();
    assert!(!tc.all_fvars_in_context(&diamond));
    drop(root);
    drop(reversed);
    drop(diamond);
    assert!(shared_leaf.upgrade().is_none());
    assert!(late_leaf.upgrade().is_none());
}

// Independent recursive tree oracle, used ONLY on the shallow fixture below.
// No pointer set, Expr metadata, TypeChecker walk, or checker context lookup is
// reused here. The explicit active-id list is the test's independent context.
fn oracle(expr: &Expr, active: &[FVarId]) -> bool {
    let child = |expr: &Expr| oracle(expr, active);
    match expr.kind() {
        ExprKind::FVar(id) => active.contains(id),
        ExprKind::App(a, b) => child(a) && child(b),
        ExprKind::Lam(_, domain, body) | ExprKind::Pi(_, domain, body) => {
            child(domain) && child(body)
        }
        ExprKind::Let(_, ty, value, body, _) => child(ty) && child(value) && child(body),
        ExprKind::Proj(_, _, expr) | ExprKind::MData(_, expr) | ExprKind::Squash(expr) => {
            child(expr)
        }
        ExprKind::CubicalPath { ty, left, right } => child(ty) && child(left) && child(right),
        ExprKind::CubicalPathLam { body } => child(body),
        ExprKind::CubicalPathApp { path, arg } => child(path) && child(arg),
        ExprKind::CubicalHComp { ty, phi, u, base } => {
            child(ty) && child(phi) && child(u) && child(base)
        }
        ExprKind::CubicalTransp { ty, phi, base } => child(ty) && child(phi) && child(base),
        ExprKind::CubicalCoe { ty, r, s, base } => child(ty) && child(r) && child(s) && child(base),
        ExprKind::BVar(_)
        | ExprKind::Sort(_)
        | ExprKind::Const(_, _)
        | ExprKind::Lit(_)
        | ExprKind::SProp
        | ExprKind::CubicalInterval
        | ExprKind::CubicalI0
        | ExprKind::CubicalI1
        | ExprKind::ZFCSet(_)
        | ExprKind::ZFCMem { .. }
        | ExprKind::ZFCComprehension { .. } => true,
    }
}

// Exactly one selected non-closed child in each currently traversed slot.
// The other children contain BVars, which this context guard must not reject.
fn child_slots(needle: &Expr) -> Vec<(&'static str, Expr)> {
    let n = || Arc::new(needle.clone());
    let z = || Arc::new(Expr::bvar(0));
    let bd = BinderInfo::Default;
    vec![
        ("app.function", Expr::app_arc(n(), z())),
        ("app.argument", Expr::app_arc(z(), n())),
        ("lam.domain", Expr::lam_arc(bd, n(), z())),
        ("lam.body", Expr::lam_arc(bd, z(), n())),
        ("pi.domain", Expr::pi_arc(bd, n(), z())),
        ("pi.body", Expr::pi_arc(bd, z(), n())),
        (
            "let.type",
            Expr::let_named_arc(Name::anon(), n(), z(), z(), false),
        ),
        (
            "let.value",
            Expr::let_named_arc(Name::anon(), z(), n(), z(), true),
        ),
        (
            "let.body",
            Expr::let_named_arc(Name::anon(), z(), z(), n(), false),
        ),
        (
            "proj.expression",
            Expr::proj_arc(Name::from_string("S"), 0, n()),
        ),
        ("mdata.expression", Expr::mdata(vec![], needle.clone())),
        ("squash.expression", Expr::from_kind(ExprKind::Squash(n()))),
        (
            "path.type",
            Expr::from_kind(ExprKind::CubicalPath {
                ty: n(),
                left: z(),
                right: z(),
            }),
        ),
        (
            "path.left",
            Expr::from_kind(ExprKind::CubicalPath {
                ty: z(),
                left: n(),
                right: z(),
            }),
        ),
        (
            "path.right",
            Expr::from_kind(ExprKind::CubicalPath {
                ty: z(),
                left: z(),
                right: n(),
            }),
        ),
        (
            "path_lam.body",
            Expr::from_kind(ExprKind::CubicalPathLam { body: n() }),
        ),
        (
            "path_app.path",
            Expr::from_kind(ExprKind::CubicalPathApp {
                path: n(),
                arg: z(),
            }),
        ),
        (
            "path_app.argument",
            Expr::from_kind(ExprKind::CubicalPathApp {
                path: z(),
                arg: n(),
            }),
        ),
        (
            "hcomp.type",
            Expr::from_kind(ExprKind::CubicalHComp {
                ty: n(),
                phi: z(),
                u: z(),
                base: z(),
            }),
        ),
        (
            "hcomp.phi",
            Expr::from_kind(ExprKind::CubicalHComp {
                ty: z(),
                phi: n(),
                u: z(),
                base: z(),
            }),
        ),
        (
            "hcomp.u",
            Expr::from_kind(ExprKind::CubicalHComp {
                ty: z(),
                phi: z(),
                u: n(),
                base: z(),
            }),
        ),
        (
            "hcomp.base",
            Expr::from_kind(ExprKind::CubicalHComp {
                ty: z(),
                phi: z(),
                u: z(),
                base: n(),
            }),
        ),
        (
            "transp.type",
            Expr::from_kind(ExprKind::CubicalTransp {
                ty: n(),
                phi: z(),
                base: z(),
            }),
        ),
        (
            "transp.phi",
            Expr::from_kind(ExprKind::CubicalTransp {
                ty: z(),
                phi: n(),
                base: z(),
            }),
        ),
        (
            "transp.base",
            Expr::from_kind(ExprKind::CubicalTransp {
                ty: z(),
                phi: z(),
                base: n(),
            }),
        ),
        (
            "coe.type",
            Expr::from_kind(ExprKind::CubicalCoe {
                ty: n(),
                r: z(),
                s: z(),
                base: z(),
            }),
        ),
        (
            "coe.r",
            Expr::from_kind(ExprKind::CubicalCoe {
                ty: z(),
                r: n(),
                s: z(),
                base: z(),
            }),
        ),
        (
            "coe.s",
            Expr::from_kind(ExprKind::CubicalCoe {
                ty: z(),
                r: z(),
                s: n(),
                base: z(),
            }),
        ),
        (
            "coe.base",
            Expr::from_kind(ExprKind::CubicalCoe {
                ty: z(),
                r: z(),
                s: z(),
                base: n(),
            }),
        ),
    ]
}

fn opaque_and_closed_cases(needle: &Expr) -> Vec<Expr> {
    let n = || Arc::new(needle.clone());
    let mut cases = vec![
        Expr::bvar(70),
        Expr::prop(),
        Expr::const_str("unresolved_but_childless"),
        Expr::nat_lit(42),
        Expr::str_lit("childless"),
        Expr::from_kind(ExprKind::SProp),
        Expr::from_kind(ExprKind::CubicalInterval),
        Expr::from_kind(ExprKind::CubicalI0),
        Expr::from_kind(ExprKind::CubicalI1),
        Expr::from_kind(ExprKind::ZFCMem {
            element: n(),
            set: n(),
        }),
        Expr::from_kind(ExprKind::ZFCComprehension {
            domain: n(),
            pred: n(),
        }),
    ];
    for set in [
        ZFCSetExpr::Empty,
        ZFCSetExpr::Singleton(n()),
        ZFCSetExpr::Pair(n(), n()),
        ZFCSetExpr::Union(n()),
        ZFCSetExpr::PowerSet(n()),
        ZFCSetExpr::Separation {
            set: n(),
            pred: n(),
        },
        ZFCSetExpr::Replacement {
            set: n(),
            func: n(),
        },
        ZFCSetExpr::Infinity,
        ZFCSetExpr::Choice(n()),
    ] {
        cases.push(Expr::from_kind(ExprKind::ZFCSet(set)));
    }
    cases
}

#[test]
fn fvar_context_walk_matches_shallow_oracle_for_every_child_slot_and_opaque_zfc() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);
    let fresh = TypeChecker::new(&env);
    let id = push(&tc, "selected_child");
    // A shallow two-edge route prevents the slot tests from only recognizing
    // immediate FVar children; the recursive oracle remains deliberately tiny.
    let needle = Expr::mdata(vec![], Expr::app(Expr::bvar(0), Expr::fvar(id)));
    let slots = child_slots(&needle);
    assert_eq!(slots.len(), 29);
    let opaque = opaque_and_closed_cases(&needle);
    assert_eq!(opaque.len(), 20);
    let check = |checker: &TypeChecker<'_>, active: &[FVarId], expected: bool| {
        assert_eq!(checker.all_fvars_in_context(&Expr::fvar(id)), expected);
        for (slot, expression) in &slots {
            let independent = oracle(expression, active);
            assert_eq!(independent, expected, "oracle fixture must exercise {slot}");
            assert_eq!(
                checker.all_fvars_in_context(expression),
                independent,
                "{slot}"
            );
        }
        for expression in &opaque {
            assert!(oracle(expression, active));
            assert!(
                checker.all_fvars_in_context(expression),
                "current ZFC policy is opaque"
            );
        }
    };
    check(&fresh, &[], false);
    check(&tc, &[id], true);
    tc.pop_binder_local();
    check(&tc, &[], false);
    let sibling = push(&tc, "sibling_child");
    assert_ne!(sibling, id);
    check(&tc, &[sibling], false);
    tc.pop_binder_local();
}

#[test]
fn fvar_context_negative_cache_hits_live_and_recomputes_after_context_pop() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);
    let retained = push(&tc, "retained");
    let popped = push(&tc, "popped");
    let a = Expr::fvar(retained);
    let b = Expr::fvar(popped);
    // Both are in-context inhabitants of Type, not proof-irrelevant Prop terms.
    assert!(!tc.is_def_eq(&a, &b));
    assert!(!tc.heartbeat_spent());
    let key = DefEqCacheKey::new(&a, &b, tc.transparency);
    assert_eq!(tc.def_eq_cache.borrow_mut().get(&key), Some(false));
    let before_hit = tc.heartbeat_remaining();
    assert!(!tc.is_def_eq(&a, &b));
    assert_eq!(
        tc.heartbeat_remaining(),
        before_hit,
        "live negative cache hit"
    );
    tc.pop_binder_local();
    assert_eq!(
        tc.def_eq_cache.borrow_mut().get(&key),
        Some(false),
        "entry was not cleared"
    );
    assert!(tc.all_fvars_in_context(&a));
    assert!(!tc.all_fvars_in_context(&b));
    let before_recompute = tc.heartbeat_remaining();
    // Deliberately re-query a popped variable to exercise the robustness guard,
    // not to claim the stale term is a well-typed public input.
    assert!(!tc.is_def_eq(&a, &b));
    assert!(
        tc.heartbeat_remaining() < before_recompute,
        "stale hit must reach real def-eq work"
    );
    assert!(
        !tc.heartbeat_spent(),
        "resource exhaustion is not a refusal witness"
    );
    let fresh = TypeChecker::new(&env);
    assert_eq!(tc.is_def_eq(&a, &b), fresh.is_def_eq(&a, &b));
    tc.pop_binder_local();
}
