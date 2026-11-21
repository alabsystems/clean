// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0

//! Exact verdict, ordered-prefix and completion parity against the old walker.
//! These structural controls provide no type-checker, proof or speedup claim.

use super::super::arc_eq_tests::{gcd_step_operand, one_of_each_variant};
use super::super::ZFCSetExpr;
use super::*;
use crate::expr::BinderInfo;
use crate::level::Level;
use crate::name::Name;

#[path = "eq_walk_old_oracle.rs"]
mod old_oracle;
use old_oracle::OldWalk;

#[derive(Clone, Copy)]
enum Entry {
    Expr,
    Kind,
}

fn parity(left: &Expr, right: &Expr, entry: Entry) -> (ExprEqWalk, OldWalk) {
    let mut new = ExprEqWalk::new();
    let mut old = OldWalk::new();
    let (actual, expected) = match entry {
        Entry::Expr => (new.root_exprs(left, right), old.root_exprs(left, right)),
        Entry::Kind => (
            new.kind_pair(&left.kind, &right.kind),
            old.kind_pair(&left.kind, &right.kind),
        ),
    };
    assert_eq!(actual, expected, "same structural verdict");
    assert_eq!(new.visits, old.visits, "same ordered node-entry prefix");
    assert_eq!(
        new.completed, old.completed,
        "same true postorder completions"
    );
    assert_eq!(new.proven, old.proven, "same exact completed address pairs");
    match entry {
        Entry::Expr => {
            assert_eq!(left == right, actual);
            assert_eq!(OldWalk::exprs(left, right), actual);
        }
        Entry::Kind => {
            assert_eq!(left.kind == right.kind, actual);
            assert_eq!(OldWalk::kinds(&left.kind, &right.kind), actual);
        }
    }
    (new, old)
}

#[test]
fn test_iterative_eq_every_variant_and_forced_metadata_collision_match_old() {
    let left = one_of_each_variant();
    let right = one_of_each_variant();
    assert_eq!(left.len(), 25);
    for (i, a) in left.iter().enumerate() {
        for (j, b) in right.iter().enumerate() {
            parity(a, b, Entry::Expr);
            parity(a, b, Entry::Kind);
            // Synthetic metadata collision, not a claim about valid metadata.
            // Exact structure, rather than metadata alone, decides equality.
            let mut colliding = b.clone();
            colliding.meta = a.meta;
            let (new, _) = parity(a, &colliding, Entry::Expr);
            assert_eq!(i == j, a == &colliding);
            assert!(new.max_pending <= 8 && !new.spilled);
        }
    }
}

fn shared_unary(depth: usize) -> (Expr, Vec<Arc<Expr>>) {
    let mut current = Arc::new(Expr::bvar(0));
    let mut keep = vec![current.clone()];
    for _ in 0..depth {
        current = Arc::new(Expr::from_kind(ExprKind::Squash(current)));
        keep.push(current.clone());
    }
    ((*current).clone(), keep)
}

#[test]
fn test_iterative_eq_inline_boundary_skips_the_transient_kind_task() {
    let (left, _keep_left) = shared_unary(7);
    let (right, _keep_right) = shared_unary(7);
    let (walk, _) = parity(&left, &right, Entry::Expr);
    assert_eq!(walk.visits, 8);
    assert!(walk.max_pending <= 8 && !walk.spilled);
}

#[test]
fn test_iterative_eq_completion_threshold_63_64_65_is_unchanged() {
    for depth in [63, 64, 65] {
        let (left, keep_left) = shared_unary(depth);
        let (right, keep_right) = shared_unary(depth);
        assert_eq!(keep_left.len(), depth + 1);
        assert_eq!(keep_right.len(), depth + 1);
        let (new, _) = parity(&left, &right, Entry::Kind);
        assert_eq!(new.completed, depth as u32);
        assert_eq!(new.visits, depth as u64);
        assert_eq!(
            new.proven.as_ref().map_or(0, |pairs| pairs.len()),
            usize::from(depth > 64)
        );
        assert_eq!(new.proven.is_some(), depth > 64);
        // Root Expr is not memoizable; its completion still counts last.
        let (new, _) = parity(&left, &right, Entry::Expr);
        assert_eq!(new.completed, depth as u32 + 1);
        assert_eq!(
            new.proven.as_ref().map_or(0, |pairs| pairs.len()),
            usize::from(depth > 64)
        );
    }
}

fn let_expr(name: &str, body: Expr, flag: bool) -> Expr {
    Expr::from_kind(ExprKind::Let(
        Name::from_string(name),
        Arc::new(gcd_step_operand(7)),
        Arc::new(gcd_step_operand(7)),
        Arc::new(body),
        flag,
    ))
}

#[test]
fn test_iterative_eq_let_flag_stays_after_body_and_early_fields_short_circuit() {
    let left = let_expr("x", gcd_step_operand(12), false);
    let late_flag = let_expr("x", gcd_step_operand(12), true);
    let (new, _) = parity(&left, &late_flag, Entry::Kind);
    assert!(new.proven.is_some() && new.completed > 64);
    assert!(!(left.kind == late_flag.kind));

    let early_name = let_expr("other", gcd_step_operand(12), true);
    let (new, _) = parity(&left, &early_name, Entry::Kind);
    assert_eq!((new.visits, new.completed), (0, 0));

    let bad_body = let_expr("x", Expr::bvar(1), false);
    let (new, _) = parity(&left, &bad_body, Entry::Kind);
    assert!(
        new.completed > 64,
        "type and value prefix completed before body"
    );
    assert!(!(left.kind == bad_body.kind));
}

#[test]
fn test_iterative_eq_shared_diamonds_and_late_unequal_prefix_retain_exact_memo() {
    for depth in [3, 7, 12, 24, 48] {
        let (a, b) = (
            Arc::new(gcd_step_operand(depth)),
            Arc::new(gcd_step_operand(depth)),
        );
        let root = |prefix: &Arc<Expr>, suffix| {
            Expr::from_kind(ExprKind::App(
                Arc::new(Expr::from_kind(ExprKind::App(
                    prefix.clone(),
                    prefix.clone(),
                ))),
                Arc::new(Expr::bvar(suffix)),
            ))
        };
        let left = root(&a, 0);
        let equal = root(&b, 0);
        let unequal = root(&b, 1);
        let counts = (Arc::strong_count(&a), Arc::strong_count(&b));
        for right in [&equal, &unequal] {
            parity(&left, right, Entry::Expr);
            parity(&left, right, Entry::Kind);
        }
        assert_eq!(counts, (Arc::strong_count(&a), Arc::strong_count(&b)));
        assert_eq!(left, equal);
        assert_ne!(left, unequal);
    }
}

fn seeded(seed: u64, count: usize) -> Vec<Arc<Expr>> {
    let mut random = seed;
    let mut nodes = (0..8).map(|n| Arc::new(Expr::bvar(n))).collect::<Vec<_>>();
    for n in 0..count {
        random = random.wrapping_mul(6364136223846793005).wrapping_add(1);
        let a = nodes[(random as usize >> 8) % nodes.len()].clone();
        let b = nodes[(random as usize >> 24) % nodes.len()].clone();
        let kind = match random % 5 {
            0 => ExprKind::App(a, b),
            1 => ExprKind::Lam(BinderInfo::Default.into(), a, b),
            2 => ExprKind::Pi(BinderInfo::Implicit.into(), a, b),
            3 => ExprKind::Let(Name::from_string("seed"), a.clone(), b, a, n % 2 == 0),
            _ => ExprKind::CubicalPathApp { path: a, arg: b },
        };
        nodes.push(Arc::new(Expr::from_kind(kind)));
    }
    nodes
}

#[test]
fn test_iterative_eq_seeded_shared_graphs_keep_old_verdict_and_accounting() {
    for seed in [1, 29, 20261010] {
        let a = seeded(seed, 96);
        let b = seeded(seed, 96);
        for index in 8..a.len() {
            parity(&a[index], &b[index], Entry::Expr);
            parity(&a[index], &b[(index + 7) % b.len()], Entry::Kind);
        }
    }
}

#[test]
fn test_iterative_eq_deep_distinct_arc_chain_uses_borrowed_worklist() {
    std::thread::Builder::new()
        .stack_size(256 * 1024)
        .spawn(|| {
            const DEPTH: usize = 32_000;
            let build = || {
                let mut expression = Expr::bvar(0);
                for _ in 0..DEPTH {
                    expression = Expr::from_kind(ExprKind::Squash(Arc::new(expression)));
                }
                expression
            };
            let (left, right) = (build(), build());
            let mut walk = ExprEqWalk::new();
            assert!(walk.root_exprs(&left, &right));
            assert_eq!(walk.visits, DEPTH as u64 + 1);
            assert_eq!(walk.completed, DEPTH as u32 + 1);
            assert!(walk.spilled && walk.max_pending <= DEPTH + 2);
            assert!(walk.proven.is_none(), "unshared chain is not memoized");
            assert_eq!(left, right, "production entry reaches the same worklist");
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn test_iterative_eq_small_probes_keep_inline_storage_and_delegated_leaf_scope() {
    let same = Expr::bvar(0);
    let different = Expr::bvar(1);
    for (left, right) in [(&same, &same), (&same, &different)] {
        let (new, _) = parity(left, right, Entry::Expr);
        assert!(!new.spilled && new.proven.is_none());
    }
    let leaf = || Arc::new(Expr::bvar(0));
    let zfc = || {
        vec![
            ZFCSetExpr::Empty,
            ZFCSetExpr::Infinity,
            ZFCSetExpr::Singleton(leaf()),
            ZFCSetExpr::Pair(leaf(), leaf()),
            ZFCSetExpr::Union(leaf()),
            ZFCSetExpr::PowerSet(leaf()),
            ZFCSetExpr::Separation {
                set: leaf(),
                pred: leaf(),
            },
            ZFCSetExpr::Replacement {
                set: leaf(),
                func: leaf(),
            },
            ZFCSetExpr::Choice(leaf()),
        ]
    };
    for (a, b) in zfc().into_iter().zip(zfc()) {
        let (left, right) = (
            Expr::from_kind(ExprKind::ZFCSet(a)),
            Expr::from_kind(ExprKind::ZFCSet(b)),
        );
        let (new, _) = parity(&left, &right, Entry::Expr);
        assert_eq!(
            new.completed, 1,
            "delegated comparisons have separate walks"
        );
        assert_eq!(format!("{left:?}"), format!("{right:?}"));
    }
    let level = || Level::Max(Level::succ(Level::zero()).into(), Level::zero().into());
    let (left, right) = (Expr::sort(level()), Expr::sort(level()));
    let (new, _) = parity(&left, &right, Entry::Expr);
    assert_eq!(
        new.completed, 1,
        "Level delegation is deliberately unchanged"
    );
    let zfc_chain = || {
        let mut term = Expr::from_kind(ExprKind::ZFCSet(ZFCSetExpr::Empty));
        for _ in 0..512 {
            term = Expr::from_kind(ExprKind::ZFCSet(ZFCSetExpr::PowerSet(Arc::new(term))));
        }
        term
    };
    let (left, right) = (zfc_chain(), zfc_chain());
    assert_eq!(
        left, right,
        "nested delegated ZFC still has segmented-stack protection"
    );
}

/// The work meter records a `false` after equal root metadata words as a
/// collision of that word: the only case a wider hash could refuse in O(1).
#[test]
fn test_metadata_collision_walk_is_charged_and_recorded_as_a_collision() {
    let mut left = Expr::const_(Name::from_string("x"), vec![]);
    for _ in 0..500 {
        left = Expr::app(Expr::const_(Name::from_string("f"), vec![]), left);
    }
    let mut colliding = Expr::app(
        Expr::const_(Name::from_string("f"), vec![]),
        Expr::const_(Name::from_string("y"), vec![]),
    );
    // Synthetic collision of the full metadata word, not valid metadata.
    colliding.meta = left.meta;
    let _ = crate::work_meter::stats::take();
    let before = crate::work_meter::charged();
    assert!(left != colliding);
    let stats = crate::work_meter::stats::take();
    assert_eq!(stats.collided_walks, 1);
    assert_eq!(stats.collided_visits, stats.equality_visits);
    assert!(stats.collided_visits >= 1);
    assert_eq!(
        crate::work_meter::charged().wrapping_sub(before),
        stats.equality_visits
    );
}
