// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `find_undef_level_param` walks the DAG, not the tree it unfolds to, and
//! still returns the FIRST undefined parameter in the old depth-first order.

use super::{find_undef_level_param, find_undef_level_param_in_level};
use crate::expr::{Expr, ExprKind};
use crate::level::Level;
use crate::name::Name;
use std::sync::Arc;

fn n(s: &str) -> Name {
    Name::from_string(s)
}

/// `e_{k+1} = e_k e_k` through one shared `Arc`, over the leaf `leaf`.
fn shared_tower(leaf: Expr, depth: u32) -> Expr {
    let mut e = Arc::new(leaf);
    for _ in 0..depth {
        e = Arc::new(Expr::app_arc(Arc::clone(&e), Arc::clone(&e)));
    }
    Arc::unwrap_or_clone(e)
}

/// The pre-2026-09-26 walk's order (App/Const/Sort only), as the reference.
fn reference(e: &Expr, allowed: &[Name]) -> Option<Name> {
    let mut stack = vec![e];
    while let Some(curr) = stack.pop() {
        match curr.kind() {
            ExprKind::Sort(l) => {
                if let Some(u) = find_undef_level_param_in_level(l, allowed) {
                    return Some(u);
                }
            }
            ExprKind::Const(_, ls) => {
                for l in ls.iter() {
                    if let Some(u) = find_undef_level_param_in_level(l, allowed) {
                        return Some(u);
                    }
                }
            }
            ExprKind::App(f, a) => {
                stack.push(a);
                stack.push(f);
            }
            _ => {}
        }
    }
    None
}

#[test]
fn test_find_undef_level_param_shared_tower_is_linear_and_finds_the_param() {
    let bad = Expr::const_(n("c"), vec![Level::param(n("v"))]);
    // 2^80 leaves as a tree: only a DAG walk finishes.
    let e = shared_tower(bad, 80);
    assert_eq!(find_undef_level_param(&e, &[n("u")]), Some(n("v")));
    assert_eq!(find_undef_level_param(&e, &[n("v")]), None);
}

#[test]
fn test_find_undef_level_param_parameter_free_term_is_none() {
    let e = shared_tower(Expr::const_(n("c"), vec![Level::Zero]), 80);
    assert_eq!(find_undef_level_param(&e, &[]), None);
}

#[test]
fn test_find_undef_level_param_first_hit_matches_reference_order() {
    // Two different undefined parameters, each inside a shared subterm that
    // occurs on both sides: the answer must be the one the old depth-first
    // walk met first.
    let left = Arc::new(Expr::const_(n("a"), vec![Level::param(n("p"))]));
    let right = Arc::new(Expr::const_(n("b"), vec![Level::param(n("q"))]));
    let lr = Arc::new(Expr::app_arc(Arc::clone(&left), Arc::clone(&right)));
    let rl = Arc::new(Expr::app_arc(Arc::clone(&right), Arc::clone(&left)));
    for (x, y) in [(&lr, &rl), (&rl, &lr)] {
        let e = Expr::app_arc(Arc::clone(x), Arc::clone(y));
        let unshared = Expr::app((**x).clone(), (**y).clone());
        assert_eq!(find_undef_level_param(&e, &[]), reference(&unshared, &[]));
        assert_eq!(
            find_undef_level_param(&e, &[n("p")]),
            reference(&unshared, &[n("p")])
        );
        assert_eq!(find_undef_level_param(&e, &[n("p"), n("q")]), None);
    }
}

#[test]
fn test_find_undef_level_param_later_sibling_shared_subterm_keeps_first_hit() {
    // `x` is SHARED and occurs twice: as the root's RIGHT child, and inside the
    // root's LEFT child ahead of `late`. The tree walk goes left first and meets
    // `x` (undefined `q`) before `late` (undefined `p`). A walk that marks a
    // shared subterm as seen when it is PUSHED (as the root pushes its right
    // child before descending left) skips `x` inside the left child, meets
    // `late` first and answers `p`: the same verdict, a different first hit.
    let x = Arc::new(Expr::const_(n("b"), vec![Level::param(n("q"))]));
    let late = Arc::new(Expr::const_(n("a"), vec![Level::param(n("p"))]));
    let left = Arc::new(Expr::app_arc(Arc::clone(&x), Arc::clone(&late)));
    let e = Expr::app_arc(Arc::clone(&left), Arc::clone(&x));
    assert_eq!(
        reference(&e, &[]),
        Some(n("q")),
        "the tree walk's first hit"
    );
    assert_eq!(find_undef_level_param(&e, &[]), reference(&e, &[]));
    assert_eq!(
        find_undef_level_param(&e, &[n("q")]),
        reference(&e, &[n("q")])
    );
    assert_eq!(find_undef_level_param(&e, &[n("p"), n("q")]), None);
}
