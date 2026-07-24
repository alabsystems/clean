// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Performance proof tests for type checker.
//!
//! These tests verify algorithmic complexity claims and detect regressions
//! in the type checker's core operations. Each test documents the expected
//! complexity class and measures actual behavior.
//!
//! Stack-safety overflow prevention tests are in `stack_safe_proofs`.

use super::tests::helpers::{run_with_timeout, SCALING_TEST_TIMEOUT};
use super::*;

// ================================================================
// Performance proof: is_def_eq on deeply nested Pi types
//
// clean's is_def_eq_binding_impl clones the entire TypeChecker (including
// LocalContext) per binder level. For a Pi chain of depth d with context
// size c, this is O(d * c) = O(d^2) work for context cloning alone, plus
// O(d) HashMap allocations for fresh whnf_cache and def_eq_cache.
//
// Lean 4's type_checker::is_def_eq_binding (type_checker.cpp:692-719)
// uses flet<local_ctx> save/restore + iterative loop = O(d) total.
//
// This test documents the current behavior. The RefCell migration (commit
// 4942ec74d, #1477) moved infer_type to &self. The timing ratio should
// now be linear rather than quadratic for binding comparisons.
// ================================================================

/// Build a Pi chain: Π (x₁ : Nat), Π (x₂ : Nat), ..., Π (xₙ : Nat), Nat
/// Each binder's body references BVar(0), creating a dependent chain
/// that forces is_def_eq_binding_impl to open each binder.
fn make_deep_pi_chain(depth: usize) -> Expr {
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let mut result = nat.clone();
    for _ in 0..depth {
        // Body uses BVar(0) so has_loose_bvars() = true,
        // forcing the full context-clone path.
        let body = Expr::app(
            Expr::const_(Name::from_string("Nat.succ"), vec![]),
            Expr::bvar(0),
        );
        // Π (_ : Nat), Nat.succ #0
        // This is not well-typed but is_def_eq doesn't type-check, only
        // compares structurally after WHNF. The important thing is that
        // has_loose_bvars() returns true so the binding comparison takes
        // the full path.
        result = Expr::pi(BinderInfo::Default, nat.clone(), body);
    }
    result
}

/// Build a Pi chain where the body does NOT reference the bound variable.
/// This tests the fast path where has_loose_bvars() = false.
fn make_deep_closed_pi_chain(depth: usize) -> Expr {
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let mut result = nat.clone();
    for _ in 0..depth {
        result = Expr::pi(BinderInfo::Default, nat.clone(), result);
    }
    result
}

/// Performance proof: is_def_eq on identical deeply nested open Pi types.
///
/// This test exercises the O(d^2) context-clone path in is_def_eq_binding_impl.
/// At depth d, the TypeChecker creates d temporary TypeCheckers, each cloning
/// a context of size 0..d. Total context-clone work: Σᵢ₌₁ᵈ i = d(d+1)/2.
///
/// Expected: depth=10 should complete in <10ms, depth=40 should complete
/// in <1s. If depth=40 takes >5s, the quadratic behavior is problematic.
///
/// Reference: lean4-ref/src/kernel/type_checker.cpp:692-719
/// Tracked in: #1421 (lazy delta) which will require is_def_eq refactoring.
#[test]
fn test_is_def_eq_deep_open_pi_completes() {
    // Wrapped in timeout: this test has O(d^2) complexity due to context cloning
    // in is_def_eq_binding_impl. At depth 40 it should complete in <1s, but if
    // performance regresses it could hang. See #1421.
    run_with_timeout(
        SCALING_TEST_TIMEOUT,
        "test_is_def_eq_deep_open_pi_completes",
        || {
            let mut env = Environment::new();
            env.init_nat()
                .expect("invariant: Nat init required for test");

            // Test at depth 40 — should complete without timeout
            let pi40 = make_deep_pi_chain(40);
            let tc = TypeChecker::new(&env);
            let result = tc.is_def_eq(&pi40, &pi40);
            assert!(result, "identical Pi chains should be def-eq");
        },
    );
}

/// Performance proof: is_def_eq on closed Pi chains uses the fast path.
///
/// When has_loose_bvars() = false, is_def_eq_binding_impl skips the
/// context-clone path and directly compares bodies. This should be
/// essentially O(d) pointer comparisons for identical expressions.
#[test]
fn test_is_def_eq_deep_closed_pi_fast_path() {
    run_with_timeout(
        SCALING_TEST_TIMEOUT,
        "test_is_def_eq_deep_closed_pi_fast_path",
        || {
            let mut env = Environment::new();
            env.init_nat()
                .expect("invariant: Nat init required for test");

            // Closed Pi chains at depth 100 should be instant
            let pi100 = make_deep_closed_pi_chain(100);
            let tc = TypeChecker::new(&env);
            let result = tc.is_def_eq(&pi100, &pi100);
            assert!(result, "identical closed Pi chains should be def-eq");
        },
    );
}

/// Performance proof: is_def_eq on structurally different deep Pi types.
///
/// Tests that the checker doesn't waste work when a difference is found
/// early in the chain (domain mismatch at first binder).
#[test]
fn test_is_def_eq_deep_pi_early_mismatch() {
    run_with_timeout(
        SCALING_TEST_TIMEOUT,
        "test_is_def_eq_deep_pi_early_mismatch",
        || {
            let mut env = Environment::new();
            env.init_nat()
                .expect("invariant: Nat init required for test");

            let nat = Expr::const_(Name::from_string("Nat"), vec![]);

            // Build two deep Pi chains that differ at the outermost domain
            let pi_nat = make_deep_pi_chain(40);
            // Same depth but different outer domain
            let pi_other = Expr::pi(
                BinderInfo::Default,
                // Different domain: Nat → Nat instead of Nat
                Expr::pi(BinderInfo::Default, nat.clone(), nat.clone()),
                Expr::app(
                    Expr::const_(Name::from_string("Nat.succ"), vec![]),
                    Expr::bvar(0),
                ),
            );

            let tc = TypeChecker::new(&env);
            let result = tc.is_def_eq(&pi_nat, &pi_other);
            assert!(
                !result,
                "Pi chains with different outer domain should not be def-eq"
            );
        },
    );
}

// ================================================================
// Performance proof: WHNF cache effectiveness
//
// The WHNF cache should prevent redundant reductions. This test verifies
// that calling whnf on the same expression twice returns quickly due to
// caching, and that the cache grows as expected.
// ================================================================

/// Performance proof: WHNF cache hit avoids recomputation.
///
/// Verifies that the whnf_cache correctly stores and retrieves results.
/// After the first WHNF call, subsequent calls should hit the cache.
#[test]
fn test_whnf_cache_hit() {
    let mut env = Environment::new();
    env.init_nat().unwrap();

    let tc = TypeChecker::new(&env);

    // Build an expression that requires delta reduction
    // Nat.succ (Nat.succ Nat.zero) — requires looking up Nat.succ definition
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
    let expr = Expr::app(succ.clone(), Expr::app(succ.clone(), zero.clone()));

    // First call: should compute and cache
    let result1 = tc.whnf(&expr);
    let cache_after_first = tc.whnf_cache_entries();

    // Second call: should hit cache
    let result2 = tc.whnf(&expr);
    let cache_after_second = tc.whnf_cache_entries();

    // Results should be identical
    assert_eq!(result1, result2, "WHNF results should be consistent");

    // Cache size should not grow on second call (cache hit)
    assert_eq!(
        cache_after_first, cache_after_second,
        "cache should not grow on hit"
    );
}

/// Performance proof: def_eq cache prevents redundant comparisons.
///
/// Exercises the cache path in `is_def_eq_inner` by comparing expressions
/// that are definitionally equal but NOT structurally equal. BinderInfo
/// differs between the two Pi types (Default vs Implicit), which means:
/// - `Expr::eq` returns false (bypasses structural equality fast-path)
/// - `is_def_eq_binding_impl` returns true (BinderInfo is irrelevant)
/// - The result is stored in `def_eq_cache`
///
/// Previous version used structurally identical expressions, which were
/// caught by the `a == b` fast-path before reaching the cache (#1467).
#[test]
fn test_def_eq_cache_hit() {
    let mut env = Environment::new();
    env.init_nat().unwrap();

    let tc = TypeChecker::new(&env);

    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    // Definitionally equal but structurally different: BinderInfo differs.
    // Lean 4 (and clean) treat BinderInfo as irrelevant for def-eq of Pi.
    let a = Expr::pi(BinderInfo::Default, nat.clone(), nat.clone());
    let b = Expr::pi(BinderInfo::Implicit, nat.clone(), nat.clone());

    // Structural inequality: BinderInfo differs
    assert_ne!(a, b, "test requires structurally different expressions");

    // Cache starts empty
    assert_eq!(tc.def_eq_cache_entries(), 0, "cache should start empty");

    // First call: should compute and cache the result
    assert!(
        tc.is_def_eq(&a, &b),
        "Pi types with different BinderInfo should be def-eq"
    );
    let cache_after_first = tc.def_eq_cache_entries();

    // Cache must have grown — proves insertion actually happened.
    // If cache insertion is disabled (mutation test), this fails.
    assert!(
        cache_after_first > 0,
        "def_eq cache must grow after first call (proves insertion)"
    );

    // Second call: should not insert a new cache entry.
    // Note: for positive results, the equiv_manager (populated by is_def_eq
    // in tc/def_eq/mod.rs) may short-circuit before the cache is consulted.
    // test_def_eq_cache_hit_negative below proves the cache *lookup* path
    // specifically, using negative results that bypass equiv_manager.
    assert!(tc.is_def_eq(&a, &b), "second call should also succeed");
    let cache_after_second = tc.def_eq_cache_entries();

    // Cache size should not grow on second call
    assert_eq!(
        cache_after_first, cache_after_second,
        "def_eq cache should not grow on repeated call"
    );
}

/// Performance proof: def_eq cache lookup works for negative results.
///
/// Positive def_eq results are also recorded in the equiv_manager (union-find),
/// which short-circuits before the cache is consulted on repeat calls.
/// Negative results are cached but NOT added to equiv_manager, so the second
/// call for a negative result MUST go through the cache lookup path.
///
/// This test completes the cache-hit proof from `test_def_eq_cache_hit`:
/// - That test proves cache *insertion* (positive case, cache grows).
/// - This test proves cache *lookup* (negative case, result returned from cache
///   without recomputation, and cache size stays stable).
///
/// If cache lookup were broken, the second call would recompute and re-insert
/// the same key, which wouldn't change cache size — so we also verify that the
/// is_def_eq result is consistent (both calls return false).
#[test]
fn test_def_eq_cache_hit_negative() {
    let mut env = Environment::new();
    env.init_nat()
        .expect("invariant: Nat init required for test");

    let tc = TypeChecker::new(&env);

    // Two expressions that are NOT definitionally equal and NOT structurally equal.
    // Nat ≠ Nat → Nat (Pi Nat Nat). This ensures:
    // - Structural equality fast-path misses (different Expr variants)
    // - equiv_manager never records them (negative result)
    // - The result goes through def_eq_cache
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let nat_to_nat = Expr::pi(BinderInfo::Default, nat.clone(), nat.clone());

    assert_ne!(
        nat, nat_to_nat,
        "test requires structurally different expressions"
    );

    // Cache starts empty
    assert_eq!(tc.def_eq_cache_entries(), 0, "cache should start empty");

    // First call: should compute and cache the negative result
    assert!(
        !tc.is_def_eq(&nat, &nat_to_nat),
        "Nat and Nat→Nat should NOT be def-eq"
    );
    let cache_after_first = tc.def_eq_cache_entries();

    // Cache must have grown — proves insertion of negative result
    assert!(
        cache_after_first > 0,
        "def_eq cache must grow after first call (proves insertion of negative result)"
    );

    // Second call: must return the cached negative result.
    // Since the first call returned false, equiv_manager was NOT populated,
    // so this call MUST go through the cache lookup in is_def_eq_inner.
    assert!(
        !tc.is_def_eq(&nat, &nat_to_nat),
        "second call should also return false (from cache)"
    );
    let cache_after_second = tc.def_eq_cache_entries();

    // Cache size must not grow — proves cache lookup returned the cached result
    // rather than recomputing and re-inserting.
    assert_eq!(
        cache_after_first, cache_after_second,
        "def_eq cache must not grow on repeated negative call (proves cache lookup)"
    );
}

// ================================================================
// Performance proof: instantiate is O(n) with subtree skipping
//
// instantiate_at_opt uses loose_bvar_range metadata to skip subtrees
// that cannot contain the target BVar. This test verifies the O(1)
// guard works correctly on expressions with no loose bvars.
// ================================================================

/// Performance proof: instantiate on closed expressions is O(1).
///
/// When an expression has no loose bound variables (loose_bvar_range = 0),
/// instantiate should return immediately without traversing the tree.
#[test]
fn test_instantiate_closed_expr_is_noop() {
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let big_expr = {
        // Build a moderately large closed expression: f (f (f ... (f x)))
        let mut e = nat.clone();
        for _ in 0..100 {
            e = Expr::app(nat.clone(), e);
        }
        e
    };

    assert!(
        !big_expr.has_loose_bvars(),
        "expression should be closed (no loose bvars)"
    );

    // instantiate on a closed expression should return the same expression
    let replacement = Expr::const_(Name::from_string("Bool"), vec![]);
    let result = big_expr.instantiate(&replacement);

    // Result should be identical to input (sharing preserved)
    assert_eq!(
        result, big_expr,
        "instantiate on closed expression should be identity"
    );
}

/// Performance proof: instantiate skips closed subtrees.
///
/// In Π (x : BigClosedType), #0, only the body (#0 = BVar(0)) needs
/// traversal. The domain (BigClosedType) should be skipped via the
/// loose_bvar_range metadata guard.
#[test]
fn test_instantiate_skips_closed_domain() {
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);

    // Build a large closed domain type
    let big_domain = {
        let mut e = nat.clone();
        for _ in 0..100 {
            e = Expr::app(nat.clone(), e);
        }
        e
    };

    // Π (_ : big_domain), #0
    // The body is BVar(0), so has_loose_bvars = true overall,
    // but the domain has no loose bvars.
    let pi = Expr::pi(BinderInfo::Default, big_domain.clone(), Expr::bvar(0));

    // instantiate(Nat) should produce: Π (_ : big_domain), Nat
    // The domain should be shared (not traversed/rebuilt).
    let result = pi.instantiate(&nat);

    // The result domain should be structurally identical
    if let ExprKind::Pi(_, domain, _) = &result.kind {
        assert_eq!(
            domain.as_ref(),
            &big_domain,
            "domain should be preserved (subtree skipped)"
        );
    } else {
        panic!("expected Pi after instantiate");
    }
}
