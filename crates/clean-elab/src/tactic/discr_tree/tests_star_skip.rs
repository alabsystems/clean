// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Star subtree-skip regression pins (g_simp probe 27, 2026-08-28): a stored
//! `Star`/`Other` is a whole-subterm placeholder, so the query walk must skip
//! the query's complete leading subtree — arity-aware — not one key.

use clean_kernel::{Expr, Name};

use super::tests::{discr_tree_state, mk_app1, mk_app2, sorted_values};
use super::{DiscrKey, DiscrTree, IndexMode};

// ============================================================================
// Star subtree-skip tests (g_simp probe 27 regression, 2026-08-28)
// ============================================================================

#[test]
fn test_subtree_key_count_arity_walk() {
    use super::key::subtree_key_count;
    // g a  ->  [Const(g,1), Const(a,0)] : one complete subtree = 2 keys
    let path = vec![
        DiscrKey::Const(Name::from_string("g"), 1),
        DiscrKey::Const(Name::from_string("a"), 0),
        DiscrKey::Const(Name::from_string("b"), 0),
    ];
    assert_eq!(
        subtree_key_count(&path),
        2,
        "the first subtree of [g(1), a, b] is g a — 2 keys"
    );
    // A leaf star is its own subtree.
    assert_eq!(subtree_key_count(&[DiscrKey::Star]), 1);
    // Truncated path: clamp to length instead of panicking.
    assert_eq!(
        subtree_key_count(&[DiscrKey::Const(Name::from_string("f"), 2)]),
        1,
        "a path cut mid-subterm clamps to what is present"
    );
}

#[test]
fn test_star_entry_matches_compound_argument() {
    let (state, goal) = discr_tree_state();
    let mut tree = DiscrTree::default();

    // Pattern `f ?x b` — path [f(2), Star, b]. The exact shape that starved
    // `Nat.succ ?n` at `Nat.succ (List.length l)`: a Star must swallow the
    // query's whole compound subtree, not one key.
    let pattern = Expr::app(
        Expr::app(Expr::const_(Name::from_string("f"), vec![]), Expr::bvar(0)),
        Expr::const_(Name::from_string("b"), vec![]),
    );
    assert!(tree.insert_if_specific(&state, &goal, &pattern, IndexMode::Normal, 7usize));

    // Query `f (g a) b` — the star argument position holds a COMPOUND term.
    let query = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("f"), vec![]),
            mk_app1("g", "a"),
        ),
        Expr::const_(Name::from_string("b"), vec![]),
    );
    let matches = tree.get_match_with_extra(&state, &goal, &query);
    assert_eq!(
        sorted_values(&matches),
        vec![7],
        "a star entry must match a compound argument (arity-aware subtree skip)"
    );

    // Negative control: `f (g a) c` — the key AFTER the skipped subtree still
    // discriminates, so the same entry must NOT be offered.
    let query_c = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("f"), vec![]),
            mk_app1("g", "a"),
        ),
        Expr::const_(Name::from_string("c"), vec![]),
    );
    let matches_c = tree.get_match_with_extra(&state, &goal, &query_c);
    assert!(
        sorted_values(&matches_c).is_empty(),
        "the subtree skip must land ON the next argument, not inside it"
    );
}

#[test]
fn test_no_index_at_args_entry_matches_compound_arguments() {
    let (state, goal) = discr_tree_state();
    let mut tree = DiscrTree::default();

    // f a b stored as f(*, *) — both stars must swallow compound query args.
    let f_a_b = mk_app2("f", "a", "b");
    assert!(tree.insert_if_specific(&state, &goal, &f_a_b, IndexMode::NoIndexAtArgs, 3usize));

    let query = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("f"), vec![]),
            mk_app1("g", "a"),
        ),
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("h"), vec![]),
                    Expr::const_(Name::from_string("a"), vec![]),
                ),
                Expr::const_(Name::from_string("b"), vec![]),
            ),
            Expr::const_(Name::from_string("c"), vec![]),
        ),
    );
    let matches = tree.get_match_with_extra(&state, &goal, &query);
    assert_eq!(
        sorted_values(&matches),
        vec![3],
        "NoIndexAtArgs stars must each skip one complete compound subtree"
    );
}

#[test]
fn test_root_level_star_no_longer_offers_across_subtree_boundary() {
    let (state, goal) = discr_tree_state();
    let mut tree: DiscrTree<usize> = DiscrTree::default();
    // Hand-built [Star, b]: a root star followed by a sibling key (not
    // refused by the insert-side generic-path rules — only [Star] alone is).
    // No mk_path-produced query has more than ONE root subtree, so with the
    // arity-aware skip this entry is unreachable; under the one-key skip it
    // was spuriously offered to any `<one-key-head> b` query (the star ate
    // `g`, leaving its ARGUMENT `b` to satisfy the sibling key).
    assert!(tree.insert_path_if_specific(
        &[DiscrKey::Star, DiscrKey::Const(Name::from_string("b"), 0)],
        9usize
    ));
    let query = mk_app1("g", "b");
    let matches = tree.get_match_with_extra(&state, &goal, &query);
    assert!(
        sorted_values(&matches).is_empty(),
        "a root star must swallow the query's whole (single) root subtree"
    );
}
