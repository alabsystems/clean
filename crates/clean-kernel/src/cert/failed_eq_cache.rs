// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Failed equality cache for `CertBuilder` batch mode performance.
//!
//! When the cert builder checks definitional equality (`def_eq`) between
//! expression pairs, failures are often repeated across certificate nodes
//! in the same batch. This cache records failed `def_eq` comparisons
//! using expression hash pairs, enabling O(1) short-circuit on known
//! failures.
//!
//! ## Design
//!
//! - Hash pairs are normalized to `(min, max)` order for symmetry:
//!   `has_failed(a, b)` and `has_failed(b, a)` return the same result.
//! - Uses `Expr::hash_cached()` (32-bit) widened to `u64` via the
//!   crate's `hash_to_u64` helper for the `ExprHasher` utility.
//! - The cache is conservative: a hit means the pair *previously* failed,
//!   but hash collisions mean false positives are possible. Callers must
//!   tolerate this (returning early `false` from `def_eq` is safe since
//!   the caller already treats failure as a type error).

use std::collections::HashSet;

use crate::expr::Expr;

/// Normalized hash pair for an unordered expression comparison.
///
/// Stored as `(min, max)` so that `(a, b)` and `(b, a)` produce
/// the same key.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct NormalizedPair(u64, u64);

impl NormalizedPair {
    /// Create a normalized pair from two hashes.
    ///
    /// Invariant: `self.0 <= self.1`.
    #[inline]
    fn new(a: u64, b: u64) -> Self {
        if a <= b {
            Self(a, b)
        } else {
            Self(b, a)
        }
    }
}

/// Cache of failed definitional equality comparisons.
///
/// Records `(hash_a, hash_b)` pairs that previously failed `def_eq`.
/// Lookups are symmetric: `has_failed(a, b) == has_failed(b, a)`.
///
/// ## Usage
///
/// ```text
/// let mut cache = FailedEqCache::new();
/// cache.record_failure(hash_a, hash_b);
/// assert!(cache.has_failed(hash_a, hash_b));
/// assert!(cache.has_failed(hash_b, hash_a)); // symmetric
/// ```
#[derive(Clone, Debug)]
pub(crate) struct FailedEqCache {
    failures: HashSet<NormalizedPair>,
}

impl FailedEqCache {
    /// Create an empty failed equality cache.
    #[must_use]
    pub(crate) fn new() -> Self {
        Self {
            failures: HashSet::new(),
        }
    }

    /// Create an empty cache with pre-allocated capacity.
    #[must_use]
    pub(crate) fn new_with_capacity(cap: usize) -> Self {
        Self {
            failures: HashSet::with_capacity(cap),
        }
    }

    /// Record a failed `def_eq` comparison between expressions with
    /// the given hashes.
    ///
    /// Order does not matter: `record_failure(a, b)` is equivalent to
    /// `record_failure(b, a)`.
    #[inline]
    pub(crate) fn record_failure(&mut self, a_hash: u64, b_hash: u64) {
        self.failures.insert(NormalizedPair::new(a_hash, b_hash));
    }

    /// Check whether a comparison between expressions with these hashes
    /// previously failed.
    ///
    /// Symmetric: `has_failed(a, b) == has_failed(b, a)`.
    ///
    /// Note: false positives are possible due to hash collisions.
    /// This is safe because the caller treats `true` as "likely to fail"
    /// and skips a redundant computation.
    #[inline]
    #[must_use]
    pub(crate) fn has_failed(&self, a_hash: u64, b_hash: u64) -> bool {
        self.failures.contains(&NormalizedPair::new(a_hash, b_hash))
    }

    /// Reset the cache, removing all recorded failures.
    pub(crate) fn clear(&mut self) {
        self.failures.clear();
    }

    /// Number of recorded failure pairs.
    #[must_use]
    pub(crate) fn len(&self) -> usize {
        self.failures.len()
    }

    /// Returns `true` if no failures have been recorded.
    #[must_use]
    pub(crate) fn is_empty(&self) -> bool {
        self.failures.is_empty()
    }
}

/// Utility to compute stable 64-bit hashes for expressions.
///
/// Uses the expression's cached metadata hash (O(1), no tree traversal)
/// widened to `u64` via `DefaultHasher` (SipHash) for better distribution.
pub(crate) struct ExprHasher;

impl ExprHasher {
    /// Compute a stable 64-bit hash for an expression.
    ///
    /// Delegates to the crate-internal `hash_to_u64` which applies
    /// `DefaultHasher` to `Expr`'s O(1) cached hash.
    #[inline]
    #[must_use]
    pub(crate) fn hash_expr(expr: &Expr) -> u64 {
        crate::expr::hash_to_u64(expr)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::expr::Expr;
    use crate::level::Level;

    // --- FailedEqCache tests ---

    #[test]
    fn test_failed_eq_cache_new_is_empty() {
        let cache = FailedEqCache::new();
        assert!(cache.is_empty());
        assert_eq!(cache.len(), 0);
    }

    #[test]
    fn test_failed_eq_cache_new_with_capacity_is_empty() {
        let cache = FailedEqCache::new_with_capacity(64);
        assert!(cache.is_empty());
        assert_eq!(cache.len(), 0);
    }

    #[test]
    fn test_failed_eq_cache_miss_returns_false() {
        let cache = FailedEqCache::new();
        assert!(!cache.has_failed(42, 99));
        assert!(!cache.has_failed(0, 0));
        assert!(!cache.has_failed(u64::MAX, 1));
    }

    #[test]
    fn test_failed_eq_cache_hit_after_record() {
        let mut cache = FailedEqCache::new();
        cache.record_failure(100, 200);
        assert!(cache.has_failed(100, 200));
        assert_eq!(cache.len(), 1);
    }

    #[test]
    fn test_failed_eq_cache_symmetry() {
        let mut cache = FailedEqCache::new();
        cache.record_failure(10, 20);
        // (a, b) same as (b, a)
        assert!(cache.has_failed(10, 20));
        assert!(cache.has_failed(20, 10));
        // Only one entry stored
        assert_eq!(cache.len(), 1);
    }

    #[test]
    fn test_failed_eq_cache_symmetry_reverse_record() {
        let mut cache = FailedEqCache::new();
        // Record in reverse order
        cache.record_failure(20, 10);
        assert!(cache.has_failed(10, 20));
        assert!(cache.has_failed(20, 10));
        assert_eq!(cache.len(), 1);
    }

    #[test]
    fn test_failed_eq_cache_reflexive_pair() {
        let mut cache = FailedEqCache::new();
        cache.record_failure(42, 42);
        assert!(cache.has_failed(42, 42));
        assert_eq!(cache.len(), 1);
    }

    #[test]
    fn test_failed_eq_cache_multiple_entries() {
        let mut cache = FailedEqCache::new();
        cache.record_failure(1, 2);
        cache.record_failure(3, 4);
        cache.record_failure(5, 6);

        assert!(cache.has_failed(1, 2));
        assert!(cache.has_failed(3, 4));
        assert!(cache.has_failed(5, 6));
        assert!(!cache.has_failed(1, 3));
        assert!(!cache.has_failed(2, 4));
        assert_eq!(cache.len(), 3);
    }

    #[test]
    fn test_failed_eq_cache_duplicate_record_is_idempotent() {
        let mut cache = FailedEqCache::new();
        cache.record_failure(10, 20);
        cache.record_failure(10, 20);
        cache.record_failure(20, 10); // symmetric duplicate
        assert_eq!(cache.len(), 1);
    }

    #[test]
    fn test_failed_eq_cache_clear() {
        let mut cache = FailedEqCache::new();
        cache.record_failure(1, 2);
        cache.record_failure(3, 4);
        assert_eq!(cache.len(), 2);

        cache.clear();
        assert!(cache.is_empty());
        assert_eq!(cache.len(), 0);
        assert!(!cache.has_failed(1, 2));
        assert!(!cache.has_failed(3, 4));
    }

    #[test]
    fn test_failed_eq_cache_clear_then_reuse() {
        let mut cache = FailedEqCache::new();
        cache.record_failure(1, 2);
        cache.clear();
        cache.record_failure(3, 4);
        assert!(!cache.has_failed(1, 2));
        assert!(cache.has_failed(3, 4));
        assert_eq!(cache.len(), 1);
    }

    #[test]
    fn test_failed_eq_cache_boundary_hashes() {
        let mut cache = FailedEqCache::new();
        cache.record_failure(0, u64::MAX);
        assert!(cache.has_failed(0, u64::MAX));
        assert!(cache.has_failed(u64::MAX, 0));

        cache.record_failure(u64::MAX, u64::MAX);
        assert!(cache.has_failed(u64::MAX, u64::MAX));
        assert_eq!(cache.len(), 2);
    }

    // --- ExprHasher tests ---

    #[test]
    fn test_expr_hasher_deterministic() {
        let e = Expr::sort(Level::zero());
        let h1 = ExprHasher::hash_expr(&e);
        let h2 = ExprHasher::hash_expr(&e);
        assert_eq!(h1, h2, "same expression must produce same hash");
    }

    #[test]
    fn test_expr_hasher_distinct_exprs_likely_differ() {
        let e1 = Expr::sort(Level::zero());
        let e2 = Expr::sort(Level::succ(Level::zero()));
        let h1 = ExprHasher::hash_expr(&e1);
        let h2 = ExprHasher::hash_expr(&e2);
        // Not guaranteed to differ (hash collisions exist), but these
        // structurally different expressions should produce different
        // hashes in practice.
        assert_ne!(h1, h2, "distinct exprs should hash differently");
    }

    #[test]
    fn test_expr_hasher_structurally_equal_same_hash() {
        // Two independently constructed but structurally equal expressions
        let e1 = Expr::sort(Level::zero());
        let e2 = Expr::sort(Level::zero());
        let h1 = ExprHasher::hash_expr(&e1);
        let h2 = ExprHasher::hash_expr(&e2);
        assert_eq!(h1, h2, "structurally equal exprs must hash the same");
    }

    // --- Integration: ExprHasher + FailedEqCache ---

    #[test]
    fn test_cache_with_expr_hashes() {
        let mut cache = FailedEqCache::new();
        let e1 = Expr::sort(Level::zero());
        let e2 = Expr::sort(Level::succ(Level::zero()));

        let h1 = ExprHasher::hash_expr(&e1);
        let h2 = ExprHasher::hash_expr(&e2);

        assert!(!cache.has_failed(h1, h2));
        cache.record_failure(h1, h2);
        assert!(cache.has_failed(h1, h2));
        assert!(cache.has_failed(h2, h1)); // symmetric
    }

    #[test]
    fn test_cache_with_expr_hashes_no_false_positive_on_different_pair() {
        let mut cache = FailedEqCache::new();
        let e1 = Expr::sort(Level::zero());
        let e2 = Expr::sort(Level::succ(Level::zero()));
        let e3 = Expr::bvar(0);

        let h1 = ExprHasher::hash_expr(&e1);
        let h2 = ExprHasher::hash_expr(&e2);
        let h3 = ExprHasher::hash_expr(&e3);

        cache.record_failure(h1, h2);
        // Different pair should not be cached
        assert!(!cache.has_failed(h1, h3));
        assert!(!cache.has_failed(h2, h3));
    }

    // --- NormalizedPair internal tests ---

    #[test]
    fn test_normalized_pair_order_invariant() {
        let p1 = NormalizedPair::new(5, 10);
        let p2 = NormalizedPair::new(10, 5);
        assert_eq!(p1, p2);
        assert_eq!(p1.0, 5);
        assert_eq!(p1.1, 10);
    }

    #[test]
    fn test_normalized_pair_equal_values() {
        let p = NormalizedPair::new(7, 7);
        assert_eq!(p.0, 7);
        assert_eq!(p.1, 7);
    }
}
