// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the WHNF reduce cache (Lean 4's `m_whnf`).
//!
//! The reduce cache (`whnf_cache`) stores full WHNF results from the outer
//! delta loop (`whnf_outer_loop`). This is the most impactful cache because
//! it memoizes the entire WHNF computation, not just the first step.
//!
//! Tests verify:
//! 1. Cache hit avoids recomputation (basic correctness)
//! 2. Cache is consulted for intermediate expressions after delta unfolding
//! 3. Cache is cleared on mode/transparency changes
//! 4. Heartbeat savings from cache hits
//!
//! Part of #3210.

use super::*;
use crate::env::{Declaration, Reducibility};

/// Helper: create an environment with a chain of definitions for delta testing.
///
/// Creates definitions: chain_0 = zero, chain_1 = chain_0, ..., chain_n = chain_{n-1}.
/// WHNF of `chain_n` requires n delta steps to reach `Nat.zero`.
fn env_with_delta_chain(depth: usize) -> Environment {
    let mut env = Environment::new();
    env.init_nat()
        .expect("invariant: Nat init required for delta chain");

    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);

    // chain_0 := Nat.zero
    let name0 = Name::from_string("chain_0");
    env.add_decl(Declaration::Definition {
        name: name0.clone(),
        level_params: vec![],
        type_: nat.clone(),
        value: zero,
        is_reducible: true,
    })
    .expect("chain_0 definition should be valid");
    env.set_reducibility(&name0, Reducibility::Reducible);

    // chain_i := chain_{i-1}
    for i in 1..depth {
        let prev_name = Name::from_string(&format!("chain_{}", i - 1));
        let cur_name = Name::from_string(&format!("chain_{i}"));
        let prev_const = Expr::const_(prev_name, vec![]);
        env.add_decl(Declaration::Definition {
            name: cur_name.clone(),
            level_params: vec![],
            type_: nat.clone(),
            value: prev_const,
            is_reducible: true,
        })
        .expect("chain definition should be valid");
        env.set_reducibility(&cur_name, Reducibility::Reducible);
    }

    env
}

/// The reduce cache stores and retrieves WHNF results for the same expression.
///
/// After whnf(chain_5), calling whnf(chain_5) again should return the cached
/// result without re-traversing the 5-step delta chain.
#[test]
fn test_reduce_cache_basic_hit() {
    let env = env_with_delta_chain(6);
    let tc = TypeChecker::new(&env);

    let chain_5 = Expr::const_(Name::from_string("chain_5"), vec![]);
    let result1 = tc.whnf(&chain_5);
    let entries_after_first = tc.whnf_cache_entries();

    // Second call should hit the cache
    let result2 = tc.whnf(&chain_5);
    let entries_after_second = tc.whnf_cache_entries();

    assert_eq!(
        result1, result2,
        "reduce cache must return consistent results"
    );
    assert_eq!(
        entries_after_first, entries_after_second,
        "reduce cache should not grow on hit"
    );
}

/// The reduce cache avoids recomputation: cache entries grow on first call only.
///
/// WHNF of chain_N requires N delta steps. After the first call, subsequent
/// calls should hit the cache and NOT add new entries.
#[test]
fn test_reduce_cache_no_growth_on_hit() {
    let env = env_with_delta_chain(10);
    let tc = TypeChecker::new(&env);

    let chain_9 = Expr::const_(Name::from_string("chain_9"), vec![]);

    // First call: compute WHNF, populates cache
    let result1 = tc.whnf(&chain_9);
    let entries_first = tc.whnf_cache_entries();

    // Second call: cache hit, no new entries
    let result2 = tc.whnf(&chain_9);
    let entries_second = tc.whnf_cache_entries();

    assert_eq!(
        result1, result2,
        "reduce cache must return consistent results"
    );
    assert_eq!(
        entries_first, entries_second,
        "reduce cache should not grow on cache hit"
    );

    // The cache should have at least 1 entry (the chain_9 -> zero mapping)
    assert!(
        entries_first >= 1,
        "cache should have stored at least one entry"
    );
}

/// Intermediate expressions after delta unfolding benefit from the reduce cache.
///
/// When whnf(chain_5) is computed, the outer loop unfolds:
///   chain_5 -> chain_4 -> chain_3 -> ... -> chain_0 -> Nat.zero
///
/// If we separately whnf(chain_3), the result is already in the cache because
/// chain_3 was encountered as an intermediate during whnf(chain_5).
///
/// This test verifies the optimization: after delta unfolding produces an
/// intermediate expression, the reduce cache is consulted before re-entering
/// the loop.
#[test]
fn test_reduce_cache_intermediate_hit() {
    let env = env_with_delta_chain(6);
    let tc = TypeChecker::new(&env);

    // First: compute whnf(chain_5) — traverses chain_5 -> chain_4 -> ... -> zero
    let chain_5 = Expr::const_(Name::from_string("chain_5"), vec![]);
    let result_5 = tc.whnf(&chain_5);

    // The reduce cache should now contain entries for intermediate forms.
    // When we compute whnf(chain_3), the cache should already have the result
    // (chain_3 was an intermediate during chain_5's computation, and the
    // optimization checks the cache after each delta step).
    let chain_3 = Expr::const_(Name::from_string("chain_3"), vec![]);

    tc.reset_whnf_impl_call_count_for_tests();
    let result_3 = tc.whnf(&chain_3);
    let calls_3 = tc.whnf_impl_call_count_for_tests();

    // Both should reduce to the same Nat.zero constructor
    assert_eq!(
        result_5, result_3,
        "chain_5 and chain_3 should both reduce to Nat.zero"
    );

    // On cache hit, whnf_impl should fire once (the top-level call) and
    // immediately return from the cache. Without the intermediate cache
    // check, it would need 3 delta steps.
    assert!(
        calls_3 <= 1,
        "intermediate cache hit should need at most 1 whnf_impl call, got {calls_3}"
    );
}

/// The reduce cache is cleared when mode changes.
///
/// WHNF results may differ across modes (e.g., Classical vs Constructive),
/// so the cache must be invalidated on mode change.
#[test]
fn test_reduce_cache_cleared_on_mode_change() {
    let env = env_with_delta_chain(3);
    let mut tc = TypeChecker::new(&env);

    let chain_2 = Expr::const_(Name::from_string("chain_2"), vec![]);
    let _ = tc.whnf(&chain_2);
    assert!(
        tc.whnf_cache_entries() > 0,
        "cache should have entries after whnf"
    );

    // Change mode — should clear cache
    tc.set_mode(CleanMode::SetTheoretic);
    assert_eq!(
        tc.whnf_cache_entries(),
        0,
        "cache should be cleared on mode change"
    );
}

/// The reduce cache is cleared when transparency changes.
///
/// Different transparency modes unfold different definitions, so cached
/// WHNF results are invalid after a transparency change.
#[test]
fn test_reduce_cache_cleared_on_transparency_change() {
    let env = env_with_delta_chain(3);
    let mut tc = TypeChecker::new(&env);

    let chain_2 = Expr::const_(Name::from_string("chain_2"), vec![]);
    let _ = tc.whnf(&chain_2);
    assert!(
        tc.whnf_cache_entries() > 0,
        "cache should have entries after whnf"
    );

    // Change transparency — should clear cache
    tc.set_transparency(TransparencyMode::All);
    assert_eq!(
        tc.whnf_cache_entries(),
        0,
        "cache should be cleared on transparency change"
    );
}

/// The reduce cache correctly handles expressions that are already in WHNF.
///
/// Sort, Pi, Lambda, Literal, and BVar expressions are already in WHNF.
/// These should NOT be cached (they return immediately from whnf_impl's
/// fast-path before reaching whnf_inner).
#[test]
fn test_reduce_cache_skips_already_whnf() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    let sort = Expr::sort(Level::zero());
    let pi = Expr::pi(
        BinderInfo::Default,
        Expr::sort(Level::zero()),
        Expr::sort(Level::zero()),
    );
    let lam = Expr::lam(
        BinderInfo::Default,
        Expr::sort(Level::zero()),
        Expr::bvar(0),
    );
    let lit = Expr::nat_lit(42);
    let bvar = Expr::bvar(0);

    for expr in [&sort, &pi, &lam, &lit, &bvar] {
        let _ = tc.whnf(expr);
    }

    assert_eq!(
        tc.whnf_cache_entries(),
        0,
        "already-WHNF expressions should not be cached (fast-path in whnf_impl)"
    );
}

/// The reduce cache benefits def_eq checking on repeated subexpressions.
///
/// is_def_eq internally calls whnf on both sides. When checking def_eq on
/// expressions that share subexpressions with prior checks, the reduce cache
/// prevents redundant WHNF computation.
///
/// Note: for Nat-typed chains, the proof irrelevance quick non-Prop filter
/// (type_is_quickly_not_in_prop) avoids whnf_impl calls in the proof irrel
/// path, so cache entries may be zero for simple Nat-typed def_eq checks.
/// The second comparison still benefits from the def_eq cache and equiv_manager.
#[test]
fn test_reduce_cache_benefits_def_eq() {
    let env = env_with_delta_chain(6);
    let tc = TypeChecker::new(&env);

    let chain_5 = Expr::const_(Name::from_string("chain_5"), vec![]);
    let chain_4 = Expr::const_(Name::from_string("chain_4"), vec![]);
    let chain_3 = Expr::const_(Name::from_string("chain_3"), vec![]);

    // First def_eq: chain_5 vs chain_4 — both reduce through lazy delta.
    assert!(tc.is_def_eq(&chain_5, &chain_4));

    // Second def_eq: chain_3 vs chain_5 — benefits from cached knowledge.
    // The def_eq cache and equiv_manager amortize repeated comparisons.
    // With the proof irrel quick non-Prop filter, Nat-typed terms skip
    // the expensive whnf_impl calls in type_is_proof_irrelevant entirely.
    tc.reset_whnf_impl_call_count_for_tests();
    assert!(tc.is_def_eq(&chain_3, &chain_5));
    let calls = tc.whnf_impl_call_count_for_tests();

    // is_def_eq has internal whnf calls from delta reduction and proof irrel.
    // With the quick non-Prop filter, Nat-typed chains need fewer whnf_impl calls.
    assert!(
        calls <= 10,
        "def_eq with cached subexpressions should need few whnf_impl calls, got {calls}"
    );
}
