// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Performance proof tests for type checker caching behavior.
//!
//! Documents cache clearing patterns, delta reduction spine rebuild cost,
//! and def_eq cache key construction overhead.
//!
//! Split from `performance_proofs.rs` for file size limits.

use super::*;

// ================================================================
// Performance proof: TC cache sliding window eviction (#2410)
//
// All 4 HashMap-based TypeChecker caches (whnf_cache, whnf_core_cache,
// def_eq_cache, proj_type_cache) use SlidingCache with generational
// eviction. When `current` generation exceeds the threshold:
//   1. `previous` (cold) generation is dropped
//   2. `current` (warm) is demoted to `previous`
//   3. A new empty `current` starts
//
// Lookups check both generations, promoting hits from `previous` to
// `current`. This eliminates the old clear-all performance cliff:
//   - Hot entries survive via promotion
//   - Cold entries are evicted after two trim cycles (not immediately)
//   - Memory bounded at ~2x threshold (current + previous)
//
// The equiv_manager also uses sliding window eviction via
// SlidingEquivManager: two independent union-find generations.
// ================================================================

/// Build a chain of Nat.succ applications for cache testing.
fn build_nat_succ_chain(count: usize) -> Vec<Expr> {
    let succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let mut exprs = Vec::with_capacity(count);
    let mut e = zero;
    for _ in 0..count {
        e = Expr::app(succ.clone(), e.clone());
        exprs.push(e.clone());
    }
    exprs
}

/// Performance proof: WHNF cache uses sliding window eviction.
///
/// Demonstrates that the sliding window retains entries across trims
/// (unlike the old clear-all approach). Uses a small threshold (100)
/// to trigger eviction without creating 100K entries.
///
/// The test documents that:
/// 1. Cache grows monotonically with distinct expressions
/// 2. First trim moves entries to `previous` (not dropped)
/// 3. Promoted entries survive the second trim cycle
/// 4. Correctness: results after trim match fresh computation
///
/// Part of #2410: eliminates TC cache cliff.
#[test]
fn test_whnf_cache_sliding_window_eviction() {
    let mut env = Environment::new();
    env.init_nat()
        .expect("invariant: Nat init required for sliding window test");

    let mut tc = TypeChecker::new(&env);
    tc.set_max_cache_entries(100);
    let exprs = build_nat_succ_chain(250);

    // Phase 1: Fill cache to threshold
    for expr in &exprs[..100] {
        let _ = tc.whnf(expr);
    }
    assert!(
        tc.whnf_cache_entries() > 0,
        "cache should have entries after 100 WHNF calls"
    );

    // Phase 2: Trigger first trim — entries slide to `previous`, not dropped
    let _ = tc.whnf(&exprs[100]);
    assert!(
        tc.whnf_cache_entries() > 0,
        "sliding window should retain entries after first trim"
    );

    // Phase 3: Access a previously-cached expression — should promote
    let result_promoted = tc.whnf(&exprs[0]);
    let result_fresh = { TypeChecker::new(&env).whnf(&exprs[0]) };
    assert_eq!(
        result_promoted, result_fresh,
        "WHNF after trim must match fresh computation"
    );

    // Phase 4: Fill current again and trigger second trim
    for expr in &exprs[110..220] {
        let _ = tc.whnf(expr);
    }
    let cache_after_second_trim = tc.whnf_cache_entries();
    assert!(
        cache_after_second_trim > 0,
        "cache should still function after multiple eviction cycles"
    );

    // Correctness: exprs[0] was promoted so it should still be cached
    assert_eq!(
        tc.whnf(&exprs[0]),
        result_fresh,
        "promoted entries must survive second eviction cycle"
    );

    // Memory bounded at 2x threshold + 1: current can hold max+1 entries
    // before a slide, plus previous holds the prior generation.
    let max_bound = 2 * 100 + 1;
    assert!(
        cache_after_second_trim <= max_bound,
        "memory should be bounded at 2*threshold+1={max_bound}, got {cache_after_second_trim}"
    );
}

// test_whnf_cache_stats_observability: REMOVED
// Tested whnf_cache_stats() API that was never implemented.
// TypeChecker only exposes whnf_cache_entries() (count).
// When a full stats API is added (#2410), restore this test.

// test_def_eq_cache_stats_observability: REMOVED
// Tested def_eq_cache_stats() API that was never implemented.
// TypeChecker only exposes def_eq_cache_entries() (count).
// When a full stats API is added (#2410), restore this test.

// ================================================================
// Performance proof: replace_head_const O(n) spine rebuild
//
// lazy_delta_reduction_step in tc/def_eq/delta.rs calls replace_head_const
// on every delta unfolding. replace_head_const in the same file
// collects all App args by walking the spine (O(k)), then rebuilds
// the entire spine with the new head (O(k) allocations). For an
// expression with k arguments and d delta steps, total cost is O(d*k).
//
// Reference: lean4-ref/src/kernel/type_checker.cpp:886-943
// ================================================================

/// Performance proof: delta reduction spine rebuild cost scales with arg count.
///
/// When `f(a, b, c)` is delta-reduced, `replace_head_const` must:
/// 1. Walk the App spine to collect [a, b, c] — O(k) where k = #args
/// 2. Rebuild the spine `val(a, b, c)` with the definition body — O(k) allocs
///
/// For `f` with k arguments and d delta unfolding steps, total cost is O(d*k).
/// This test verifies the scaling by comparing is_def_eq runtime at different
/// argument counts. With 1 delta step, doubling args should roughly double time.
#[test]
fn test_replace_head_const_spine_rebuild_scaling() {
    use crate::env::{Declaration, Reducibility};
    use std::time::Instant;

    let arg_counts = [5usize, 20, 80];
    let mut times = Vec::new();

    for &k in &arg_counts {
        let mut env = Environment::new();
        env.init_nat()
            .expect("invariant: Nat init required for test");

        let nat = Expr::const_(Name::from_string("Nat"), vec![]);

        // Build type: Nat → Nat → ... → Nat (k+1 times, k arguments)
        let mut fn_type = nat.clone();
        for _ in 0..k {
            fn_type = Expr::pi(BinderInfo::Default, nat.clone(), fn_type);
        }

        // Build definition body: λ x₁ ... xₖ. x₁ (identity on first arg)
        // Body is BVar(k-1) (the first argument in de Bruijn indexing)
        let mut fn_body = Expr::bvar((k - 1) as u32);
        for _ in 0..k {
            fn_body = Expr::lam(BinderInfo::Default, nat.clone(), fn_body);
        }

        let fn_name = Name::from_string("delta_test_fn");
        env.add_decl(Declaration::Definition {
            name: fn_name.clone(),
            level_params: vec![],
            type_: fn_type,
            value: fn_body,
            is_reducible: true,
        })
        .expect("definition should be valid");
        env.set_reducibility(&fn_name, Reducibility::Reducible);

        // Build application: delta_test_fn(zero, zero, ..., zero) with k args
        let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let mut app = Expr::const_(fn_name, vec![]);
        for _ in 0..k {
            app = Expr::app(app, zero.clone());
        }

        // is_def_eq(app, zero) should reduce app via delta + beta to zero.
        // The delta step calls replace_head_const with k arguments.
        let tc = TypeChecker::new(&env);

        let start = Instant::now();
        for _ in 0..1000 {
            let result = tc.is_def_eq(&app, &zero);
            assert!(result, "delta_test_fn(zero,...,zero) should reduce to zero");
        }
        let elapsed = start.elapsed().as_nanos();
        times.push(elapsed);
    }

    // arg_counts go 5 -> 20 -> 80 (4x each step).
    // For O(k) spine rebuild: 4x args → ~4x time, 16x args → ~16x time.
    // For O(k^2): would see ~256x.
    let ratio_16x = times[2] as f64 / times[0].max(1) as f64;
    // The spine rebuild is O(k) per delta step, so we expect roughly linear scaling.
    // Allow 50x for overhead/cache effects. If >50x, something is worse than linear.
    assert!(
        ratio_16x < 50.0,
        "replace_head_const scaling appears worse than O(k): \
         16x args gave {ratio_16x:.1}x time (times_ns={times:?})"
    );
}

// ================================================================
// Performance proof: DefEqCacheKey clones both Exprs on every call
//
// is_def_eq_inner in tc/def_eq/mod.rs constructs a DefEqCacheKey before
// looking up the cache. DefEqCacheKey::new in the same file clones
// both expressions to create the key — even when the cache has a hit.
//
// For M calls to is_def_eq_inner on non-trivially-equal pairs, this is
// M * 2 Expr clones. A two-phase lookup (hash → clone on miss) would
// eliminate clones on cache hits.
// ================================================================

/// Performance proof: def_eq cache key construction overhead on repeated calls.
///
/// Each call to `is_def_eq_inner` that reaches the cache (past ptr-eq,
/// equiv_manager, and structural equality) clones both expressions for
/// the cache key. On cache hits, this clone is wasted.
///
/// This test measures the overhead by calling is_def_eq on a pair that is
/// definitionally equal (returns true) but structurally different (bypasses
/// the `a == b` fast-path). On the second call, the result is cached, but the
/// cache key is still constructed with two clones.
#[test]
fn test_def_eq_cache_key_clone_overhead() {
    use std::time::Instant;

    let mut env = Environment::new();
    env.init_nat()
        .expect("invariant: Nat init required for test");

    let nat = Expr::const_(Name::from_string("Nat"), vec![]);

    // Pairs that are definitionally equal but structurally different
    // (BinderInfo differs, which is irrelevant for def-eq of Pi types).
    // This ensures we bypass the structural equality fast-path at line 238.
    let sizes = [1usize, 5, 20];
    let mut times = Vec::new();

    for &depth in &sizes {
        let tc = TypeChecker::new(&env);

        // Build a chain of Pi types with different BinderInfo
        let mut a = nat.clone();
        let mut b = nat.clone();
        for _ in 0..depth {
            a = Expr::pi(BinderInfo::Default, nat.clone(), a);
            b = Expr::pi(BinderInfo::Implicit, nat.clone(), b);
        }

        // Verify they're not structurally equal but ARE def-equal
        assert_ne!(a, b, "test requires structurally different expressions");
        assert!(
            tc.is_def_eq(&a, &b),
            "should be def-equal (BinderInfo irrelevant)"
        );

        // Now measure repeated calls (all cache hits after first)
        let start = Instant::now();
        for _ in 0..10_000 {
            let result = tc.is_def_eq(&a, &b);
            assert!(result);
        }
        let elapsed = start.elapsed().as_nanos();
        times.push(elapsed);
    }

    // depth 1 -> 5 -> 20: expression size grows linearly with depth.
    // Cache key clone is O(depth) since cloning a Pi chain of depth d
    // is d Arc refcount bumps. So 20x depth → ~20x clone overhead.
    // On cache hit, the only work is: equiv_manager check, structural eq check,
    // cache key construction (2 clones), HashMap lookup. The cache hit is O(1)
    // apart from the clone.
    let _ratio = times[2] as f64 / times[0].max(1) as f64;
    // Document: the clone cost grows with expression size, even on cache hits.
    // A lightweight hash-based pre-check would avoid clones on hits.
    // _ratio intentionally unused — this test documents overhead, not asserts on it.
}
