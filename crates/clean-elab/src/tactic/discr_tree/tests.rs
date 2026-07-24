// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use clean_kernel::env::Declaration;
use clean_kernel::{BinderInfo, Environment, Expr, FVarId, Level, Name};

use super::key::Match;
use super::path::query_path_is_too_generic;
use super::trie::Trie;
use super::{mk_path, DiscrKey, DiscrTree, IndexMode};
use crate::tactic::{Goal, ProofState};

// ============================================================================
// Helpers
// ============================================================================

fn add_axiom(env: &mut Environment, name: &str, type_: Expr) {
    env.add_decl(Declaration::Axiom {
        name: Name::from_string(name),
        level_params: vec![],
        type_,
    })
    .unwrap();
}

fn mk_eq(nat_ty: &Expr, lhs: Expr, rhs: Expr) -> Expr {
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                nat_ty.clone(),
            ),
            lhs,
        ),
        rhs,
    )
}

fn discr_tree_state() -> (ProofState, Goal) {
    let mut env = Environment::new();
    env.init_nat().unwrap();
    env.init_eq().unwrap();

    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    add_axiom(
        &mut env,
        "f",
        Expr::arrow(nat_ty.clone(), Expr::arrow(nat_ty.clone(), nat_ty.clone())),
    );
    add_axiom(&mut env, "g", Expr::arrow(nat_ty.clone(), nat_ty.clone()));
    add_axiom(
        &mut env,
        "h",
        Expr::arrow(
            nat_ty.clone(),
            Expr::arrow(nat_ty.clone(), Expr::arrow(nat_ty.clone(), nat_ty.clone())),
        ),
    );
    add_axiom(&mut env, "a", nat_ty.clone());
    add_axiom(&mut env, "b", nat_ty.clone());
    add_axiom(&mut env, "c", nat_ty.clone());

    let target = mk_eq(
        &nat_ty,
        Expr::const_(Name::from_string("a"), vec![]),
        Expr::const_(Name::from_string("a"), vec![]),
    );
    let state = ProofState::new(env, target);
    let goal = state.current_goal().expect("goal should exist").clone();
    (state, goal)
}

/// Helper: create `f a b` from name strings.
fn mk_app2(head: &str, arg1: &str, arg2: &str) -> Expr {
    Expr::app(
        Expr::app(
            Expr::const_(Name::from_string(head), vec![]),
            Expr::const_(Name::from_string(arg1), vec![]),
        ),
        Expr::const_(Name::from_string(arg2), vec![]),
    )
}

/// Helper: create `g a` from name strings.
fn mk_app1(head: &str, arg: &str) -> Expr {
    Expr::app(
        Expr::const_(Name::from_string(head), vec![]),
        Expr::const_(Name::from_string(arg), vec![]),
    )
}

fn sorted_values<T: Clone + Ord>(matches: &[Match<T>]) -> Vec<T> {
    let mut vals: Vec<T> = matches.iter().map(|m| m.value.clone()).collect();
    vals.sort();
    vals
}

// ============================================================================
// Path construction tests
// ============================================================================

#[test]
fn test_mk_path_tracks_constants_literals_arrows_and_wildcards() {
    let (state, goal) = discr_tree_state();

    let app = Expr::app(
        Expr::app(Expr::const_(Name::from_string("f"), vec![]), Expr::bvar(0)),
        Expr::nat_lit(7),
    );
    assert_eq!(
        mk_path(&state, &goal, &app, IndexMode::Normal),
        vec![
            DiscrKey::Const(Name::from_string("f"), 2),
            DiscrKey::Star,
            DiscrKey::Lit(clean_kernel::Literal::nat(7)),
        ],
        "application paths should keep the head key and encode loose binders as stars"
    );

    let arrow = Expr::pi(
        BinderInfo::Default,
        Expr::const_(Name::from_string("Nat"), vec![]),
        Expr::bvar(0),
    );
    assert_eq!(
        mk_path(&state, &goal, &arrow, IndexMode::Normal),
        vec![
            DiscrKey::Arrow,
            DiscrKey::Const(Name::from_string("Nat"), 0),
        ],
        "Pi paths should index the domain under Arrow"
    );
}

#[test]
fn test_mk_path_no_index_at_args_uses_star_placeholders() {
    let (state, goal) = discr_tree_state();
    let app = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("f"), vec![]),
            Expr::const_(Name::from_string("a"), vec![]),
        ),
        Expr::app(
            Expr::const_(Name::from_string("g"), vec![]),
            Expr::const_(Name::from_string("a"), vec![]),
        ),
    );

    assert_eq!(
        mk_path(&state, &goal, &app, IndexMode::NoIndexAtArgs),
        vec![
            DiscrKey::Const(Name::from_string("f"), 2),
            DiscrKey::Star,
            DiscrKey::Star,
        ],
        "NoIndexAtArgs should wildcard the entire argument positions"
    );
}

#[test]
fn test_mk_path_bare_constant_has_zero_arity() {
    let (state, goal) = discr_tree_state();
    let bare = Expr::const_(Name::from_string("a"), vec![]);
    assert_eq!(
        mk_path(&state, &goal, &bare, IndexMode::Normal),
        vec![DiscrKey::Const(Name::from_string("a"), 0)],
        "bare constants should produce a single key with arity 0"
    );
}

#[test]
fn test_mk_path_nested_application_encodes_subexpressions() {
    let (state, goal) = discr_tree_state();
    // f (g a) b
    let nested = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("f"), vec![]),
            mk_app1("g", "a"),
        ),
        Expr::const_(Name::from_string("b"), vec![]),
    );
    let path = mk_path(&state, &goal, &nested, IndexMode::Normal);
    assert_eq!(
        path,
        vec![
            DiscrKey::Const(Name::from_string("f"), 2),
            DiscrKey::Const(Name::from_string("g"), 1),
            DiscrKey::Const(Name::from_string("a"), 0),
            DiscrKey::Const(Name::from_string("b"), 0),
        ],
        "nested applications should recursively encode all subexpressions"
    );
}

#[test]
fn test_mk_path_nat_literal_is_encoded_as_lit_key() {
    let (state, goal) = discr_tree_state();
    let lit = Expr::nat_lit(42);
    assert_eq!(
        mk_path(&state, &goal, &lit, IndexMode::Normal),
        vec![DiscrKey::Lit(clean_kernel::Literal::nat(42))],
        "nat literals should produce a Lit key"
    );
}

#[test]
fn test_mk_path_fvar_is_encoded_with_arity() {
    let (state, goal) = discr_tree_state();
    let fvar_expr = Expr::fvar(FVarId::new(99));
    let path = mk_path(&state, &goal, &fvar_expr, IndexMode::Normal);
    assert_eq!(
        path,
        vec![DiscrKey::FVar(FVarId::new(99), 0)],
        "free variables should produce an FVar key with arity"
    );
}

#[test]
fn test_mk_path_sort_produces_other() {
    let (state, goal) = discr_tree_state();
    let sort = Expr::sort(Level::zero());
    let path = mk_path(&state, &goal, &sort, IndexMode::Normal);
    assert_eq!(
        path,
        vec![DiscrKey::Other],
        "sorts should produce an Other key"
    );
}

#[test]
fn test_mk_path_lambda_produces_other() {
    let (state, goal) = discr_tree_state();
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let lam = Expr::lam(BinderInfo::Default, nat_ty, Expr::bvar(0));
    let path = mk_path(&state, &goal, &lam, IndexMode::Normal);
    assert_eq!(
        path,
        vec![DiscrKey::Other],
        "lambda expressions should produce an Other key"
    );
}

#[test]
fn test_mk_path_projection_encodes_struct_field_and_inner() {
    let (state, goal) = discr_tree_state();
    let inner = Expr::const_(Name::from_string("a"), vec![]);
    let proj = Expr::proj(Name::from_string("Prod"), 0, inner);
    let path = mk_path(&state, &goal, &proj, IndexMode::Normal);
    assert_eq!(
        path,
        vec![
            DiscrKey::Proj(Name::from_string("Prod"), 0, 0),
            DiscrKey::Const(Name::from_string("a"), 0),
        ],
        "projections should encode struct name, field index, arity, and inner expr"
    );
}

// ============================================================================
// query_path_is_too_generic tests
// ============================================================================

#[test]
fn test_query_path_is_too_generic_empty() {
    assert!(
        query_path_is_too_generic(&[]),
        "empty paths are too generic"
    );
}

#[test]
fn test_query_path_is_too_generic_single_star() {
    assert!(
        query_path_is_too_generic(&[DiscrKey::Star]),
        "a single Star path is too generic"
    );
}

#[test]
fn test_query_path_is_too_generic_star_head() {
    assert!(
        query_path_is_too_generic(&[DiscrKey::Star, DiscrKey::Const(Name::from_string("a"), 0)]),
        "paths starting with Star are too generic"
    );
}

#[test]
fn test_query_path_is_too_generic_other_head() {
    assert!(
        query_path_is_too_generic(&[DiscrKey::Other, DiscrKey::Const(Name::from_string("a"), 0)]),
        "paths starting with Other are too generic"
    );
}

#[test]
fn test_query_path_is_too_generic_half_star() {
    // 2 of 4 are generic => 2*2 >= 4 => too generic
    assert!(
        query_path_is_too_generic(&[
            DiscrKey::Const(Name::from_string("f"), 2),
            DiscrKey::Star,
            DiscrKey::Other,
            DiscrKey::Const(Name::from_string("a"), 0),
        ]),
        "paths with >=50% generic keys should be too generic"
    );
}

#[test]
fn test_query_path_is_not_too_generic_mostly_concrete() {
    assert!(
        !query_path_is_too_generic(&[
            DiscrKey::Const(Name::from_string("f"), 2),
            DiscrKey::Const(Name::from_string("a"), 0),
            DiscrKey::Star,
        ]),
        "paths with <50% generic keys are not too generic"
    );
}

#[test]
fn test_query_path_is_too_generic_eq_star_star_star() {
    let path = vec![
        DiscrKey::Const(Name::from_string("Eq"), 3),
        DiscrKey::Star,
        DiscrKey::Star,
        DiscrKey::Star,
    ];
    assert!(
        query_path_is_too_generic(&path),
        "Eq(3) Star Star Star is a special trivially-generic pattern"
    );
}

// ============================================================================
// Trie direct tests
// ============================================================================

#[test]
fn test_trie_insert_and_match_exact_path() {
    let mut trie = Trie::default();
    let path = [
        DiscrKey::Const(Name::from_string("f"), 2),
        DiscrKey::Const(Name::from_string("a"), 0),
        DiscrKey::Const(Name::from_string("b"), 0),
    ];
    trie.insert_path(&path, 10usize);

    let mut out = Vec::new();
    trie.match_path(&path, &mut out);
    assert_eq!(out, vec![10], "exact path should match the inserted value");
}

#[test]
fn test_trie_match_star_wildcard_matches_any_key() {
    let mut trie = Trie::default();
    // Insert with Star in argument position
    let insert_path = [DiscrKey::Const(Name::from_string("g"), 1), DiscrKey::Star];
    trie.insert_path(&insert_path, 20usize);

    // Query with concrete argument
    let query_path = [
        DiscrKey::Const(Name::from_string("g"), 1),
        DiscrKey::Const(Name::from_string("a"), 0),
    ];
    let mut out = Vec::new();
    trie.match_path(&query_path, &mut out);
    assert!(
        out.contains(&20),
        "Star in the trie should match a concrete query key"
    );
}

#[test]
fn test_trie_match_concrete_query_against_star_entry() {
    let mut trie = Trie::default();
    // Insert specific entry: f a b = 1
    let specific = [
        DiscrKey::Const(Name::from_string("f"), 2),
        DiscrKey::Const(Name::from_string("a"), 0),
        DiscrKey::Const(Name::from_string("b"), 0),
    ];
    trie.insert_path(&specific, 1usize);

    // Insert wildcard entry: f * * = 2
    let wildcard = [
        DiscrKey::Const(Name::from_string("f"), 2),
        DiscrKey::Star,
        DiscrKey::Star,
    ];
    trie.insert_path(&wildcard, 2usize);

    // Query for f a b — both should match
    let mut out = Vec::new();
    trie.match_path(&specific, &mut out);
    out.sort();
    assert_eq!(
        out,
        vec![1, 2],
        "both exact and wildcard entries should match a concrete query"
    );
}

#[test]
fn test_trie_no_match_returns_empty() {
    let mut trie = Trie::default();
    let insert_path = [
        DiscrKey::Const(Name::from_string("f"), 2),
        DiscrKey::Const(Name::from_string("a"), 0),
    ];
    trie.insert_path(&insert_path, 1usize);

    // Query for completely different head
    let query_path = [
        DiscrKey::Const(Name::from_string("g"), 1),
        DiscrKey::Const(Name::from_string("a"), 0),
    ];
    let mut out = Vec::new();
    trie.match_path(&query_path, &mut out);
    assert!(
        out.is_empty(),
        "non-matching paths should return no results"
    );
}

#[test]
fn test_trie_multiple_values_at_same_path() {
    let mut trie = Trie::default();
    let path = [DiscrKey::Const(Name::from_string("a"), 0)];
    trie.insert_path(&path, 1usize);
    trie.insert_path(&path, 2usize);
    trie.insert_path(&path, 3usize);

    let mut out = Vec::new();
    trie.match_path(&path, &mut out);
    out.sort();
    assert_eq!(
        out,
        vec![1, 2, 3],
        "multiple values stored at the same path should all be returned"
    );
}

#[test]
fn test_trie_collect_all_gathers_entire_subtree() {
    let mut trie = Trie::default();
    trie.insert_path(&[DiscrKey::Const(Name::from_string("a"), 0)], 1usize);
    trie.insert_path(
        &[
            DiscrKey::Const(Name::from_string("f"), 1),
            DiscrKey::Const(Name::from_string("b"), 0),
        ],
        2usize,
    );
    trie.insert_path(&[], 3usize); // value at root

    let mut out = Vec::new();
    trie.collect_all(&mut out);
    out.sort();
    assert_eq!(
        out,
        vec![1, 2, 3],
        "collect_all should gather all values from the entire trie"
    );
}

#[test]
fn test_trie_empty_path_inserts_at_root() {
    let mut trie = Trie::default();
    trie.insert_path(&[], 42usize);

    let mut out = Vec::new();
    trie.match_path(&[], &mut out);
    assert_eq!(
        out,
        vec![42],
        "empty path should store and retrieve values at the root node"
    );
}

// ============================================================================
// DiscrTree insert tests
// ============================================================================

#[test]
fn test_insert_if_specific_skips_all_star_and_eq_star_paths() {
    let (state, goal) = discr_tree_state();
    let mut tree = DiscrTree::default();

    assert!(
        !tree.insert_if_specific(&state, &goal, &Expr::bvar(0), IndexMode::Normal, 1usize),
        "all-star paths should be dropped"
    );
    assert!(
        !tree.insert_if_specific(
            &state,
            &goal,
            &Expr::app(
                Expr::app(
                    Expr::app(Expr::const_(Name::from_string("Eq"), vec![]), Expr::bvar(2)),
                    Expr::bvar(1),
                ),
                Expr::bvar(0),
            ),
            IndexMode::Normal,
            2usize,
        ),
        "Eq * * * paths should be dropped"
    );
    assert!(
        tree.is_empty(),
        "generic entries should not populate the tree"
    );
}

#[test]
fn test_insert_if_specific_accepts_concrete_expression() {
    let (state, goal) = discr_tree_state();
    let mut tree = DiscrTree::default();
    let expr = mk_app2("f", "a", "b");
    assert!(
        tree.insert_if_specific(&state, &goal, &expr, IndexMode::Normal, 1usize),
        "concrete expressions should be accepted into the tree"
    );
    assert!(
        !tree.is_empty(),
        "tree should not be empty after successful insert"
    );
}

#[test]
fn test_insert_if_specific_accepts_bare_constant() {
    let (state, goal) = discr_tree_state();
    let mut tree = DiscrTree::default();
    let bare = Expr::const_(Name::from_string("a"), vec![]);
    assert!(
        tree.insert_if_specific(&state, &goal, &bare, IndexMode::Normal, 5usize),
        "bare constants should be accepted"
    );
}

// ============================================================================
// DiscrTree query tests — exact matching
// ============================================================================

#[test]
fn test_get_match_exact_finds_inserted_entry() {
    let (state, goal) = discr_tree_state();
    let mut tree = DiscrTree::default();

    let expr = mk_app2("f", "a", "b");
    assert!(tree.insert_if_specific(&state, &goal, &expr, IndexMode::Normal, 42usize));

    let matches = tree.get_match_with_extra(&state, &goal, &expr);
    assert_eq!(
        sorted_values(&matches),
        vec![42],
        "exact query should find the inserted entry"
    );
    assert!(
        matches.iter().all(|m| m.extra_args == 0),
        "exact match should have zero extra args"
    );
}

#[test]
fn test_get_match_discriminates_different_arguments() {
    let (state, goal) = discr_tree_state();
    let mut tree = DiscrTree::default();

    let f_a_b = mk_app2("f", "a", "b");
    let f_b_a = mk_app2("f", "b", "a");
    assert!(tree.insert_if_specific(&state, &goal, &f_a_b, IndexMode::Normal, 1usize));
    assert!(tree.insert_if_specific(&state, &goal, &f_b_a, IndexMode::Normal, 2usize));

    // Query f a b should match only entry 1
    let matches_ab = tree.get_match_with_extra(&state, &goal, &f_a_b);
    assert_eq!(
        sorted_values(&matches_ab),
        vec![1],
        "f a b should match only the f a b entry, not f b a"
    );

    // Query f b a should match only entry 2
    let matches_ba = tree.get_match_with_extra(&state, &goal, &f_b_a);
    assert_eq!(
        sorted_values(&matches_ba),
        vec![2],
        "f b a should match only the f b a entry, not f a b"
    );
}

#[test]
fn test_get_match_discriminates_different_heads() {
    let (state, goal) = discr_tree_state();
    let mut tree = DiscrTree::default();

    let f_a_b = mk_app2("f", "a", "b");
    let g_a = mk_app1("g", "a");
    assert!(tree.insert_if_specific(&state, &goal, &f_a_b, IndexMode::Normal, 1usize));
    assert!(tree.insert_if_specific(&state, &goal, &g_a, IndexMode::Normal, 2usize));

    let matches_f = tree.get_match_with_extra(&state, &goal, &f_a_b);
    assert_eq!(
        sorted_values(&matches_f),
        vec![1],
        "f-headed query should not match g-headed entry"
    );

    let matches_g = tree.get_match_with_extra(&state, &goal, &g_a);
    assert_eq!(
        sorted_values(&matches_g),
        vec![2],
        "g-headed query should not match f-headed entry"
    );
}

// ============================================================================
// DiscrTree query tests — wildcard matching
// ============================================================================

#[test]
fn test_get_match_star_entry_matches_any_query_argument() {
    let (state, goal) = discr_tree_state();
    let mut tree = DiscrTree::default();

    // Insert f(bvar 0, a) — the bvar(0) becomes Star
    let pattern = Expr::app(
        Expr::app(Expr::const_(Name::from_string("f"), vec![]), Expr::bvar(0)),
        Expr::const_(Name::from_string("a"), vec![]),
    );
    assert!(tree.insert_if_specific(&state, &goal, &pattern, IndexMode::Normal, 10usize));

    // Query f(b, a) should match since Star matches b
    let query = mk_app2("f", "b", "a");
    let matches = tree.get_match_with_extra(&state, &goal, &query);
    assert_eq!(
        sorted_values(&matches),
        vec![10],
        "Star in the index should match any concrete argument in the query"
    );
}

#[test]
fn test_get_match_star_and_concrete_both_returned() {
    let (state, goal) = discr_tree_state();
    let mut tree = DiscrTree::default();

    // Insert wildcard pattern: f(*, a) = 1
    let wildcard = Expr::app(
        Expr::app(Expr::const_(Name::from_string("f"), vec![]), Expr::bvar(0)),
        Expr::const_(Name::from_string("a"), vec![]),
    );
    assert!(tree.insert_if_specific(&state, &goal, &wildcard, IndexMode::Normal, 1usize));

    // Insert concrete pattern: f(b, a) = 2
    let concrete = mk_app2("f", "b", "a");
    assert!(tree.insert_if_specific(&state, &goal, &concrete, IndexMode::Normal, 2usize));

    // Query f(b, a) should match both wildcard and concrete
    let matches = tree.get_match_with_extra(&state, &goal, &concrete);
    assert_eq!(
        sorted_values(&matches),
        vec![1, 2],
        "both wildcard and concrete entries should match"
    );
}

// ============================================================================
// DiscrTree query tests — prefix matching (extra args)
// ============================================================================

#[test]
fn test_get_match_with_extra_reports_prefix_matches() {
    let (state, goal) = discr_tree_state();
    let mut tree = DiscrTree::default();
    let partial = Expr::app(
        Expr::const_(Name::from_string("f"), vec![]),
        Expr::const_(Name::from_string("a"), vec![]),
    );
    let query = Expr::app(
        partial.clone(),
        Expr::const_(Name::from_string("b"), vec![]),
    );

    assert!(
        tree.insert_if_specific(&state, &goal, &partial, IndexMode::Normal, 7usize),
        "partial applications should be indexable"
    );

    let matches = tree.get_match_with_extra(&state, &goal, &query);
    assert!(
        matches
            .iter()
            .any(|entry| entry.value == 7 && entry.extra_args == 1),
        "prefix matches should report the ignored trailing application depth"
    );
}

#[test]
fn test_get_match_with_extra_zero_for_exact_match() {
    let (state, goal) = discr_tree_state();
    let mut tree = DiscrTree::default();

    let expr = mk_app2("f", "a", "b");
    assert!(tree.insert_if_specific(&state, &goal, &expr, IndexMode::Normal, 5usize));

    let matches = tree.get_match_with_extra(&state, &goal, &expr);
    assert!(
        matches.iter().any(|m| m.value == 5 && m.extra_args == 0),
        "exact match should report extra_args == 0"
    );
}

// ============================================================================
// DiscrTree query tests — liberal matching
// ============================================================================

#[test]
fn test_get_match_liberal_collects_root_bucket() {
    let (state, goal) = discr_tree_state();
    let mut tree = DiscrTree::default();

    let first = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("f"), vec![]),
            Expr::const_(Name::from_string("a"), vec![]),
        ),
        Expr::app(
            Expr::const_(Name::from_string("g"), vec![]),
            Expr::const_(Name::from_string("a"), vec![]),
        ),
    );
    let second = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("f"), vec![]),
            Expr::const_(Name::from_string("b"), vec![]),
        ),
        Expr::const_(Name::from_string("a"), vec![]),
    );

    assert!(tree.insert_if_specific(&state, &goal, &first, IndexMode::Normal, 1usize));
    assert!(tree.insert_if_specific(&state, &goal, &second, IndexMode::Normal, 2usize));

    let matches = tree.get_match_liberal(
        &state,
        &goal,
        &Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("f"), vec![]),
                Expr::const_(Name::from_string("a"), vec![]),
            ),
            Expr::const_(Name::from_string("b"), vec![]),
        ),
    );

    assert!(
        matches.contains(&1) && matches.contains(&2),
        "liberal lookup should return every value under the query root symbol"
    );
}

#[test]
fn test_get_match_liberal_does_not_return_different_root() {
    let (state, goal) = discr_tree_state();
    let mut tree = DiscrTree::default();

    let g_entry = mk_app1("g", "a");
    assert!(tree.insert_if_specific(&state, &goal, &g_entry, IndexMode::Normal, 1usize));

    // Liberal lookup for f-headed expression should not return g's entry
    let matches = tree.get_match_liberal(&state, &goal, &mk_app2("f", "a", "b"));
    assert!(
        !matches.contains(&1),
        "liberal lookup should not cross root symbol boundaries"
    );
}

// ============================================================================
// DiscrTree — empty tree queries
// ============================================================================

#[test]
fn test_get_match_empty_tree_returns_empty() {
    let (state, goal) = discr_tree_state();
    let tree: DiscrTree<usize> = DiscrTree::default();

    let matches = tree.get_match_with_extra(&state, &goal, &mk_app2("f", "a", "b"));
    assert!(
        matches.is_empty(),
        "querying an empty tree should return no matches"
    );
}

#[test]
fn test_get_match_liberal_empty_tree_returns_empty() {
    let (state, goal) = discr_tree_state();
    let tree: DiscrTree<usize> = DiscrTree::default();

    let matches = tree.get_match_liberal(&state, &goal, &mk_app2("f", "a", "b"));
    assert!(
        matches.is_empty(),
        "liberal lookup on empty tree should return no matches"
    );
}

// ============================================================================
// DiscrTree — multiple entries for the same pattern
// ============================================================================

#[test]
fn test_multiple_values_at_same_expression() {
    let (state, goal) = discr_tree_state();
    let mut tree = DiscrTree::default();

    let expr = mk_app1("g", "a");
    assert!(tree.insert_if_specific(&state, &goal, &expr, IndexMode::Normal, 10usize));
    assert!(tree.insert_if_specific(&state, &goal, &expr, IndexMode::Normal, 20usize));
    assert!(tree.insert_if_specific(&state, &goal, &expr, IndexMode::Normal, 30usize));

    let matches = tree.get_match_with_extra(&state, &goal, &expr);
    assert_eq!(
        sorted_values(&matches),
        vec![10, 20, 30],
        "all values inserted at the same expression should be returned"
    );
}

// ============================================================================
// DiscrTree — NoIndexAtArgs mode interacts with matching
// ============================================================================

#[test]
fn test_no_index_at_args_entry_matches_any_arguments() {
    let (state, goal) = discr_tree_state();
    let mut tree = DiscrTree::default();

    // Insert f a b with NoIndexAtArgs — stored as f(*, *)
    let f_a_b = mk_app2("f", "a", "b");
    assert!(tree.insert_if_specific(&state, &goal, &f_a_b, IndexMode::NoIndexAtArgs, 1usize,));

    // Query f b a — should still match because the index has Stars for args
    let f_b_a = mk_app2("f", "b", "a");
    let matches = tree.get_match_with_extra(&state, &goal, &f_b_a);
    assert_eq!(
        sorted_values(&matches),
        vec![1],
        "NoIndexAtArgs entries should match any arguments with the same head"
    );
}

// ============================================================================
// DiscrTree — deeply nested expressions
// ============================================================================

#[test]
fn test_deeply_nested_application_discriminates() {
    let (state, goal) = discr_tree_state();
    let mut tree = DiscrTree::default();

    // f (g a) (g b) = 1
    let e1 = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("f"), vec![]),
            mk_app1("g", "a"),
        ),
        mk_app1("g", "b"),
    );
    // f (g b) (g a) = 2
    let e2 = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("f"), vec![]),
            mk_app1("g", "b"),
        ),
        mk_app1("g", "a"),
    );

    assert!(tree.insert_if_specific(&state, &goal, &e1, IndexMode::Normal, 1usize));
    assert!(tree.insert_if_specific(&state, &goal, &e2, IndexMode::Normal, 2usize));

    let matches1 = tree.get_match_with_extra(&state, &goal, &e1);
    assert_eq!(
        sorted_values(&matches1),
        vec![1],
        "nested f (g a) (g b) should match only entry 1"
    );

    let matches2 = tree.get_match_with_extra(&state, &goal, &e2);
    assert_eq!(
        sorted_values(&matches2),
        vec![2],
        "nested f (g b) (g a) should match only entry 2"
    );
}

// ============================================================================
// Key ordering tests
// ============================================================================

#[test]
fn test_discr_key_ordering_star_before_const() {
    use super::key::cmp_keys;
    use std::cmp::Ordering;

    assert_eq!(
        cmp_keys(&DiscrKey::Star, &DiscrKey::Const(Name::from_string("x"), 0)),
        Ordering::Less,
        "Star (rank 0) should sort before Const (rank 4)"
    );
}

#[test]
fn test_discr_key_ordering_const_by_name_then_arity() {
    use super::key::cmp_keys;
    use std::cmp::Ordering;

    assert_eq!(
        cmp_keys(
            &DiscrKey::Const(Name::from_string("a"), 0),
            &DiscrKey::Const(Name::from_string("b"), 0),
        ),
        Ordering::Less,
        "constants with same arity should sort by name"
    );

    assert_eq!(
        cmp_keys(
            &DiscrKey::Const(Name::from_string("f"), 1),
            &DiscrKey::Const(Name::from_string("f"), 2),
        ),
        Ordering::Less,
        "constants with same name should sort by arity"
    );
}

#[test]
fn test_discr_key_ordering_lit_nat_values() {
    use super::key::cmp_keys;
    use std::cmp::Ordering;

    assert_eq!(
        cmp_keys(
            &DiscrKey::Lit(clean_kernel::Literal::nat(3)),
            &DiscrKey::Lit(clean_kernel::Literal::nat(7)),
        ),
        Ordering::Less,
        "nat literals should sort by value"
    );
}
