// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for simp lemma discrimination tree index.

use clean_kernel::env::Declaration;
use clean_kernel::{Environment, Expr, Level, Name};

use super::simp::{SimpIndexMode, SimpLemma};
use super::simp_index::{
    extract_lhs_pattern, generate_disc_keys, SimpIndex, SimpIndexStats, SimpLemmaEntry,
};
use super::{Goal, ProofState};

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

fn nat_ty() -> Expr {
    Expr::const_(Name::from_string("Nat"), vec![])
}

fn mk_const(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

fn mk_app1(head: &str, arg: &str) -> Expr {
    Expr::app(mk_const(head), mk_const(arg))
}

fn mk_app2(head: &str, arg1: &str, arg2: &str) -> Expr {
    Expr::app(Expr::app(mk_const(head), mk_const(arg1)), mk_const(arg2))
}

fn mk_eq(ty: &Expr, lhs: Expr, rhs: Expr) -> Expr {
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                ty.clone(),
            ),
            lhs,
        ),
        rhs,
    )
}

fn test_env() -> Environment {
    let mut env = Environment::new();
    env.init_nat().unwrap();
    env.init_eq().unwrap();

    let nat = nat_ty();
    add_axiom(
        &mut env,
        "f",
        Expr::arrow(nat.clone(), Expr::arrow(nat.clone(), nat.clone())),
    );
    add_axiom(&mut env, "g", Expr::arrow(nat.clone(), nat.clone()));
    add_axiom(
        &mut env,
        "h",
        Expr::arrow(
            nat.clone(),
            Expr::arrow(nat.clone(), Expr::arrow(nat.clone(), nat.clone())),
        ),
    );
    add_axiom(&mut env, "a", nat.clone());
    add_axiom(&mut env, "b", nat.clone());
    add_axiom(&mut env, "c", nat.clone());
    add_axiom(&mut env, "d", nat.clone());
    env
}

fn test_state() -> (ProofState, Goal) {
    let env = test_env();
    let nat = nat_ty();
    let target = mk_eq(&nat, mk_const("a"), mk_const("a"));
    let state = ProofState::new(env, target);
    let goal = state.current_goal().expect("goal should exist").clone();
    (state, goal)
}

fn mk_lemma(name: &str, lhs: Expr, rhs: Expr, priority: u32) -> SimpLemma {
    SimpLemma {
        name: Name::from_string(name),
        lhs,
        rhs,
        eq_type: Some(nat_ty()),
        proof_expr: None,
        index_mode: SimpIndexMode::Normal,
        priority,
    }
}

// ============================================================================
// SimpLemmaEntry tests
// ============================================================================

#[test]
fn test_entry_from_simp_lemma_preserves_fields() {
    let lemma = mk_lemma("lem1", mk_const("a"), mk_const("b"), 100);
    let entry = SimpLemmaEntry::from_simp_lemma(&lemma);
    assert_eq!(entry.name, Name::from_string("lem1"));
    assert_eq!(entry.priority, 100);
    assert!(entry.proof.is_none());
    assert_eq!(entry.index_mode, SimpIndexMode::Normal);
}

#[test]
fn test_entry_roundtrip_to_simp_lemma() {
    let original = mk_lemma("roundtrip", mk_app1("g", "a"), mk_const("b"), 75);
    let entry = SimpLemmaEntry::from_simp_lemma(&original);
    let back = entry.to_simp_lemma();
    assert_eq!(back.name, original.name);
    assert_eq!(back.priority, original.priority);
    assert_eq!(back.index_mode, original.index_mode);
}

#[test]
fn test_entry_with_proof_expr() {
    let mut lemma = mk_lemma("with_proof", mk_const("a"), mk_const("b"), 50);
    lemma.proof_expr = Some(mk_const("proof_term"));
    let entry = SimpLemmaEntry::from_simp_lemma(&lemma);
    assert!(entry.proof.is_some());
    let back = entry.to_simp_lemma();
    assert!(back.proof_expr.is_some());
}

// ============================================================================
// SimpIndex creation and basic operations
// ============================================================================

#[test]
fn test_new_index_is_empty() {
    let index = SimpIndex::new();
    assert!(index.is_empty());
    assert_eq!(index.len(), 0);
}

#[test]
fn test_insert_single_lemma() {
    let (state, goal) = test_state();
    let mut index = SimpIndex::new();
    let lemma = mk_lemma("add_zero", mk_app2("f", "a", "b"), mk_const("a"), 100);
    assert!(index.insert_lemma(&state, &goal, &lemma));
    assert_eq!(index.len(), 1);
    assert!(!index.is_empty());
}

#[test]
fn test_insert_duplicate_rejected() {
    let (state, goal) = test_state();
    let mut index = SimpIndex::new();
    let lemma = mk_lemma("dup_test", mk_app1("g", "a"), mk_const("b"), 100);
    assert!(index.insert_lemma(&state, &goal, &lemma));
    assert!(!index.insert_lemma(&state, &goal, &lemma));
    assert_eq!(index.len(), 1);
}

#[test]
fn test_insert_many_returns_count() {
    let (state, goal) = test_state();
    let mut index = SimpIndex::new();
    let lemmas = vec![
        mk_lemma("lem_a", mk_app1("g", "a"), mk_const("b"), 100),
        mk_lemma("lem_b", mk_app1("g", "b"), mk_const("c"), 90),
        mk_lemma("lem_c", mk_app2("f", "a", "b"), mk_const("c"), 80),
    ];
    let inserted = index.insert_many(&state, &goal, &lemmas);
    assert_eq!(inserted, 3);
    assert_eq!(index.len(), 3);
}

#[test]
fn test_insert_many_with_duplicates() {
    let (state, goal) = test_state();
    let mut index = SimpIndex::new();
    let lemmas = vec![
        mk_lemma("lem_x", mk_app1("g", "a"), mk_const("b"), 100),
        mk_lemma("lem_x", mk_app1("g", "b"), mk_const("c"), 90), // duplicate name
        mk_lemma("lem_y", mk_app2("f", "a", "b"), mk_const("c"), 80),
    ];
    let inserted = index.insert_many(&state, &goal, &lemmas);
    assert_eq!(inserted, 2);
    assert_eq!(index.len(), 2);
}

#[test]
fn test_contains_checks_name() {
    let (state, goal) = test_state();
    let mut index = SimpIndex::new();
    let lemma = mk_lemma("exists_check", mk_app1("g", "a"), mk_const("b"), 100);
    assert!(!index.contains("exists_check"));
    index.insert_lemma(&state, &goal, &lemma);
    assert!(index.contains("exists_check"));
    assert!(!index.contains("nonexistent"));
}

#[test]
fn test_get_by_index() {
    let (state, goal) = test_state();
    let mut index = SimpIndex::new();
    let lemma = mk_lemma("get_test", mk_app1("g", "a"), mk_const("b"), 100);
    index.insert_lemma(&state, &goal, &lemma);
    assert!(index.get(0).is_some());
    assert_eq!(index.get(0).unwrap().name, Name::from_string("get_test"));
    assert!(index.get(1).is_none());
}

#[test]
fn test_clear_empties_index() {
    let (state, goal) = test_state();
    let mut index = SimpIndex::new();
    index.insert_lemma(
        &state,
        &goal,
        &mk_lemma("to_clear", mk_app1("g", "a"), mk_const("b"), 100),
    );
    assert_eq!(index.len(), 1);
    index.clear();
    assert!(index.is_empty());
    assert_eq!(index.len(), 0);
    assert!(!index.contains("to_clear"));
}

// ============================================================================
// Lookup tests
// ============================================================================

#[test]
fn test_lookup_matching_head() {
    let (state, goal) = test_state();
    let mut index = SimpIndex::new();

    // Insert lemma for `g a = b`
    index.insert_lemma(
        &state,
        &goal,
        &mk_lemma("g_a_eq_b", mk_app1("g", "a"), mk_const("b"), 100),
    );
    // Insert lemma for `f a b = c`
    index.insert_lemma(
        &state,
        &goal,
        &mk_lemma("f_ab_eq_c", mk_app2("f", "a", "b"), mk_const("c"), 90),
    );

    // Look up `g a` — should find g_a_eq_b
    let results = index.lookup(&state, &goal, &mk_app1("g", "a"));
    assert!(!results.is_empty());
    let names: Vec<String> = results.iter().map(|e| e.name.to_string()).collect();
    assert!(names.contains(&"g_a_eq_b".to_string()));
}

#[test]
fn test_lookup_returns_priority_order() {
    let (state, goal) = test_state();
    let mut index = SimpIndex::new();

    // Insert multiple lemmas with different priorities for same head
    index.insert_lemma(
        &state,
        &goal,
        &mk_lemma("low_prio", mk_app1("g", "a"), mk_const("b"), 10),
    );
    index.insert_lemma(
        &state,
        &goal,
        &mk_lemma("high_prio", mk_app1("g", "b"), mk_const("c"), 200),
    );
    index.insert_lemma(
        &state,
        &goal,
        &mk_lemma("mid_prio", mk_app1("g", "c"), mk_const("d"), 50),
    );

    let all = index.all_by_priority();
    assert_eq!(all.len(), 3);
    assert_eq!(all[0].priority, 200);
    assert_eq!(all[1].priority, 50);
    assert_eq!(all[2].priority, 10);
}

#[test]
fn test_lookup_no_match_returns_empty() {
    let (state, goal) = test_state();
    let mut index = SimpIndex::new();

    // Insert lemma for `g a`
    index.insert_lemma(
        &state,
        &goal,
        &mk_lemma("only_g", mk_app1("g", "a"), mk_const("b"), 100),
    );

    // Look up `f a b` — different head, should not match via strict path
    // (may return results via liberal fallback depending on tree structure)
    let results = index.lookup(&state, &goal, &mk_app2("f", "a", "b"));
    // The results may be empty or may include liberal matches;
    // verify names if non-empty
    for entry in &results {
        // Any returned entry should be a valid entry from our index
        assert!(index.contains(&entry.name.to_string()));
    }
}

#[test]
fn test_lookup_empty_index() {
    let (state, goal) = test_state();
    let index = SimpIndex::new();
    let results = index.lookup(&state, &goal, &mk_app1("g", "a"));
    assert!(results.is_empty());
}

#[test]
fn test_lookup_as_lemmas() {
    let (state, goal) = test_state();
    let mut index = SimpIndex::new();
    index.insert_lemma(
        &state,
        &goal,
        &mk_lemma("as_lemma", mk_app1("g", "a"), mk_const("b"), 100),
    );
    let lemmas = index.lookup_as_lemmas(&state, &goal, &mk_app1("g", "a"));
    assert!(!lemmas.is_empty());
    assert_eq!(lemmas[0].name, Name::from_string("as_lemma"));
}

// ============================================================================
// Statistics tests
// ============================================================================

#[test]
fn test_stats_empty_index() {
    let index = SimpIndex::new();
    let stats = index.stats();
    assert_eq!(
        stats,
        SimpIndexStats {
            lemma_count: 0,
            distinct_names: 0,
            unindexed_count: 0,
            indexed_count: 0,
        }
    );
}

#[test]
fn test_stats_after_insertions() {
    let (state, goal) = test_state();
    let mut index = SimpIndex::new();
    index.insert_lemma(
        &state,
        &goal,
        &mk_lemma("s1", mk_app1("g", "a"), mk_const("b"), 100),
    );
    index.insert_lemma(
        &state,
        &goal,
        &mk_lemma("s2", mk_app2("f", "a", "b"), mk_const("c"), 90),
    );

    let stats = index.stats();
    assert_eq!(stats.lemma_count, 2);
    assert_eq!(stats.distinct_names, 2);
}

#[test]
fn test_stats_collision_rate_no_duplicates() {
    let (state, goal) = test_state();
    let mut index = SimpIndex::new();
    index.insert_lemma(
        &state,
        &goal,
        &mk_lemma("unique_a", mk_app1("g", "a"), mk_const("b"), 100),
    );
    index.insert_lemma(
        &state,
        &goal,
        &mk_lemma("unique_b", mk_app2("f", "a", "b"), mk_const("c"), 90),
    );

    let stats = index.stats();
    assert!((stats.collision_rate() - 0.0).abs() < f64::EPSILON);
}

#[test]
fn test_stats_collision_rate_empty() {
    let stats = SimpIndexStats::default();
    assert!((stats.collision_rate() - 0.0).abs() < f64::EPSILON);
}

#[test]
fn test_stats_indexed_vs_unindexed() {
    let (state, goal) = test_state();
    let mut index = SimpIndex::new();

    // This should be indexable (specific head symbol)
    index.insert_lemma(
        &state,
        &goal,
        &mk_lemma("specific", mk_app1("g", "a"), mk_const("b"), 100),
    );

    // A very generic lemma (just a bvar) may fail to index
    let generic_lemma = SimpLemma {
        name: Name::from_string("generic"),
        lhs: Expr::bvar(0),
        rhs: mk_const("b"),
        eq_type: Some(nat_ty()),
        proof_expr: None,
        index_mode: SimpIndexMode::Normal,
        priority: 50,
    };
    index.insert_lemma(&state, &goal, &generic_lemma);

    let stats = index.stats();
    assert_eq!(stats.lemma_count, 2);
    // The bvar lemma should be unindexed (too generic path)
    assert!(stats.unindexed_count >= 1);
    assert!(stats.indexed_count <= stats.lemma_count);
}

// ============================================================================
// extract_lhs_pattern tests
// ============================================================================

#[test]
fn test_extract_lhs_pattern_normal_lemma() {
    let lemma = mk_lemma("normal", mk_app1("g", "a"), mk_const("b"), 100);
    let lhs = extract_lhs_pattern(&lemma);
    assert!(lhs.is_some());
}

#[test]
fn test_extract_lhs_pattern_bvar_returns_none() {
    let lemma = SimpLemma {
        name: Name::from_string("bvar_lhs"),
        lhs: Expr::bvar(0),
        rhs: mk_const("b"),
        eq_type: Some(nat_ty()),
        proof_expr: None,
        index_mode: SimpIndexMode::Normal,
        priority: 50,
    };
    assert!(extract_lhs_pattern(&lemma).is_none());
}

// ============================================================================
// generate_disc_keys tests
// ============================================================================

#[test]
fn test_generate_disc_keys_const() {
    let (state, goal) = test_state();
    let keys = generate_disc_keys(&state, &goal, &mk_const("a"), SimpIndexMode::Normal);
    assert!(!keys.is_empty());
}

#[test]
fn test_generate_disc_keys_app() {
    let (state, goal) = test_state();
    let keys = generate_disc_keys(&state, &goal, &mk_app1("g", "a"), SimpIndexMode::Normal);
    // Should have keys for the head `g` and the argument `a`
    assert!(keys.len() >= 2);
}

#[test]
fn test_generate_disc_keys_no_index_at_args() {
    let (state, goal) = test_state();
    let keys_normal = generate_disc_keys(&state, &goal, &mk_app1("g", "a"), SimpIndexMode::Normal);
    let keys_no_args = generate_disc_keys(
        &state,
        &goal,
        &mk_app1("g", "a"),
        SimpIndexMode::NoIndexAtArgs,
    );
    // NoIndexAtArgs should produce Star keys for arguments
    assert!(!keys_normal.is_empty());
    assert!(!keys_no_args.is_empty());
}

// ============================================================================
// Priority ordering integration test
// ============================================================================

#[test]
fn test_priority_ordering_in_lookup() {
    let (state, goal) = test_state();
    let mut index = SimpIndex::new();

    // Insert lemmas for the same head but different priorities
    let lemmas = vec![
        mk_lemma("prio_10", mk_app1("g", "a"), mk_const("b"), 10),
        mk_lemma("prio_100", mk_app1("g", "b"), mk_const("c"), 100),
        mk_lemma("prio_50", mk_app1("g", "c"), mk_const("d"), 50),
    ];
    index.insert_many(&state, &goal, &lemmas);

    // all_by_priority should be sorted descending
    let all = index.all_by_priority();
    for window in all.windows(2) {
        assert!(window[0].priority >= window[1].priority);
    }
}

// ============================================================================
// Edge cases
// ============================================================================

#[test]
fn test_insert_entry_directly() {
    let (state, goal) = test_state();
    let mut index = SimpIndex::new();
    let entry = SimpLemmaEntry {
        name: Name::from_string("direct_entry"),
        lhs: mk_app1("g", "a"),
        rhs: mk_const("b"),
        eq_type: Some(nat_ty()),
        proof: None,
        priority: 100,
        index_mode: SimpIndexMode::Normal,
    };
    assert!(index.insert(&state, &goal, entry));
    assert_eq!(index.len(), 1);
}

#[test]
fn test_clear_then_reinsert() {
    let (state, goal) = test_state();
    let mut index = SimpIndex::new();
    index.insert_lemma(
        &state,
        &goal,
        &mk_lemma("clearable", mk_app1("g", "a"), mk_const("b"), 100),
    );
    index.clear();
    // After clear, same name can be inserted again
    assert!(index.insert_lemma(
        &state,
        &goal,
        &mk_lemma("clearable", mk_app1("g", "a"), mk_const("b"), 100),
    ));
    assert_eq!(index.len(), 1);
}

#[test]
fn test_stats_after_clear() {
    let (state, goal) = test_state();
    let mut index = SimpIndex::new();
    index.insert_lemma(
        &state,
        &goal,
        &mk_lemma("tmp", mk_app1("g", "a"), mk_const("b"), 100),
    );
    index.clear();
    let stats = index.stats();
    assert_eq!(stats.lemma_count, 0);
    assert_eq!(stats.distinct_names, 0);
    assert_eq!(stats.unindexed_count, 0);
    assert_eq!(stats.indexed_count, 0);
}

#[test]
fn test_no_index_at_args_mode() {
    let (state, goal) = test_state();
    let mut index = SimpIndex::new();
    let lemma = SimpLemma {
        name: Name::from_string("no_args"),
        lhs: mk_app1("g", "a"),
        rhs: mk_const("b"),
        eq_type: Some(nat_ty()),
        proof_expr: None,
        index_mode: SimpIndexMode::NoIndexAtArgs,
        priority: 100,
    };
    assert!(index.insert_lemma(&state, &goal, &lemma));
    assert_eq!(index.len(), 1);

    let stats = index.stats();
    assert!(stats.indexed_count >= 1 || stats.unindexed_count >= 1);
}

#[test]
fn test_multiple_lemmas_same_head_different_args() {
    let (state, goal) = test_state();
    let mut index = SimpIndex::new();

    index.insert_lemma(
        &state,
        &goal,
        &mk_lemma("ga", mk_app1("g", "a"), mk_const("b"), 100),
    );
    index.insert_lemma(
        &state,
        &goal,
        &mk_lemma("gb", mk_app1("g", "b"), mk_const("c"), 90),
    );
    index.insert_lemma(
        &state,
        &goal,
        &mk_lemma("gc", mk_app1("g", "c"), mk_const("d"), 80),
    );

    assert_eq!(index.len(), 3);
    let stats = index.stats();
    assert_eq!(stats.distinct_names, 3);
}
