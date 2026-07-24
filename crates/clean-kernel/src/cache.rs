// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Content-addressed caching for type checking
//!
//! This module provides caching infrastructure for type inference results,
//! keyed by expression fingerprints. The cache improves performance when
//! re-checking files by reusing results for unchanged expressions.
//!
//! # Design
//!
//! Following the ty `ObligationId` pattern from `tla-prove/src/obligation.rs`,
//! we use content-addressed fingerprints to identify type checking queries.
//!
//! The cache key includes:
//! - The expression being type-checked
//! - A hash of the environment state (to invalidate on definition changes)
//!
//! # Phase 1 Scope
//!
//! This is an in-memory cache with no persistence. Future phases will add:
//! - Phase 2: DefEqCache for definitional equality
//! - Phase 3: ElabCache for elaboration (with disk persistence)
//! - Phase 4: Server ResponseCache
//!
//! See `designs/2026-01-31-content-addressed-caching.md` for full design.

use crate::expr::{iterative_drop, Expr};
use std::collections::HashMap;
use std::hash::{Hash, Hasher};
use std::sync::Arc;

/// Drain cache values using iterative expression teardown.
///
/// This avoids recursive `Drop` stack growth when a cache happens to contain a
/// very deep `Expr` tree.
fn drop_expr_values_iteratively<K>(results: &mut HashMap<K, Expr>)
where
    K: Eq + Hash,
{
    for (_, expr) in results.drain() {
        iterative_drop(expr);
    }
}

/// Fingerprint for type inference cache lookups.
///
/// Combines the expression hash with environment and mode state to ensure
/// cache validity across definition and mode changes.
///
/// Stores the original expression as `Arc<Expr>` to guarantee structural
/// equality verification on hash collisions. The hash fields provide O(1)
/// fast-reject for HashMap bucket placement, while `PartialEq` falls through
/// to structural comparison when hashes match — preventing soundness bugs
/// from hash-only key comparisons (#1771).
#[derive(Clone, Debug)]
pub struct TypeCheckId {
    /// Hash of the expression being type-checked (for fast HashMap bucketing)
    expr_hash: u64,
    /// Hash of environment state (definitions in scope)
    env_hash: u64,
    /// Hash of the current CleanMode (e.g. Constructive vs Classical)
    mode_hash: u64,
    /// Original expression for structural equality verification on collision
    expr: Arc<Expr>,
}

impl PartialEq for TypeCheckId {
    fn eq(&self, other: &Self) -> bool {
        // Fast-reject on hash fields (O(1))
        self.expr_hash == other.expr_hash
            && self.env_hash == other.env_hash
            && self.mode_hash == other.mode_hash
            // Structural equality verification — prevents soundness bugs from
            // hash collisions. Expr::PartialEq has its own O(1) meta pre-filter
            // before falling through to recursive structural comparison.
            && *self.expr == *other.expr
    }
}

impl Eq for TypeCheckId {}

impl Hash for TypeCheckId {
    fn hash<H: Hasher>(&self, state: &mut H) {
        // Only hash the numeric fields for HashMap bucket placement.
        // Structural equality is enforced by PartialEq, not Hash.
        self.expr_hash.hash(state);
        self.env_hash.hash(state);
        self.mode_hash.hash(state);
    }
}

impl TypeCheckId {
    /// Create a new TypeCheckId from an expression, environment hash, and mode hash.
    ///
    /// The env_hash should capture the state of definitions that could
    /// affect type inference for this expression. The mode_hash captures
    /// the current CleanMode to prevent stale results after mode changes.
    ///
    /// # Contract
    ///
    /// ENSURES: Equal expressions with equal env_hash and mode_hash produce equal TypeCheckIds
    /// ENSURES: Different expressions with same hash are distinguished by structural equality
    #[cfg(not(kani))]
    pub fn new(expr: &Expr, env_hash: u64, mode_hash: u64) -> Self {
        let mut hasher = std::collections::hash_map::DefaultHasher::new();
        expr.hash(&mut hasher);
        TypeCheckId {
            expr_hash: hasher.finish(),
            env_hash,
            mode_hash,
            expr: Arc::new(expr.clone()),
        }
    }

    #[cfg(kani)]
    pub fn new(expr: &Expr, env_hash: u64, mode_hash: u64) -> Self {
        use crate::expr::KaniHasher;
        let mut hasher = KaniHasher::new();
        expr.hash(&mut hasher);
        TypeCheckId {
            expr_hash: hasher.finish(),
            env_hash,
            mode_hash,
            expr: Arc::new(expr.clone()),
        }
    }
}

/// Statistics for TypeCheckCache usage.
#[derive(Clone, Debug, Default)]
pub struct TypeCheckCacheStats {
    /// Number of cache hits
    pub hits: u64,
    /// Number of cache misses
    pub misses: u64,
    /// Number of entries in cache
    pub entries: usize,
}

impl TypeCheckCacheStats {
    /// Calculate hit rate as a percentage (0.0 to 100.0)
    ///
    /// # Contract
    ///
    /// ENSURES: `result >= 0.0 && result <= 100.0`
    /// ENSURES: `result == 0.0` if `hits + misses == 0`
    /// ENSURES: `result == (hits * 100) / (hits + misses)` otherwise
    pub fn hit_rate(&self) -> f64 {
        let total = self.hits + self.misses;
        if total == 0 {
            0.0
        } else {
            (self.hits as f64 / total as f64) * 100.0
        }
    }
}

/// Maximum number of entries before eviction kicks in.
///
/// Chosen to bound memory at roughly O(100K * sizeof(Expr)) while still
/// providing good hit rates for Mathlib-scale imports.
const MAX_CACHE_ENTRIES: usize = 100_000;

/// When eviction triggers, remove this fraction of entries (1/4).
/// Amortizes the eviction cost over many inserts.
const EVICTION_FRACTION: usize = 4;

/// Cache for type inference results.
///
/// Maps expression fingerprints to their inferred types.
/// The cache is invalidated when the environment version or mode changes.
/// Bounded to [`MAX_CACHE_ENTRIES`]; excess entries are evicted randomly.
#[derive(Clone, Debug, Default)]
pub struct TypeCheckCache {
    /// Cached type inference results: TypeCheckId -> inferred type
    results: HashMap<TypeCheckId, Expr>,
    /// Current environment hash (used to detect environment changes)
    current_env_hash: u64,
    /// Current mode hash (used to detect CleanMode changes)
    current_mode_hash: u64,
    /// Usage statistics
    stats: TypeCheckCacheStats,
}

impl TypeCheckCache {
    /// Create a new empty cache.
    ///
    /// # Contract
    ///
    /// ENSURES: `result.is_empty() == true`
    /// ENSURES: `result.len() == 0`
    pub fn new() -> Self {
        Self::default()
    }

    /// Create a cache with specific environment and mode hashes.
    ///
    /// # Contract
    ///
    /// ENSURES: `result.is_empty() == true`
    /// ENSURES: `result.env_hash() == env_hash`
    /// ENSURES: `result.mode_hash() == mode_hash`
    pub fn with_hashes(env_hash: u64, mode_hash: u64) -> Self {
        Self {
            results: HashMap::new(),
            current_env_hash: env_hash,
            current_mode_hash: mode_hash,
            stats: TypeCheckCacheStats::default(),
        }
    }

    /// Get the current environment hash.
    ///
    /// # Contract
    ///
    /// ENSURES: Returns the current environment hash
    pub fn env_hash(&self) -> u64 {
        self.current_env_hash
    }

    /// Get the current mode hash.
    ///
    /// # Contract
    ///
    /// ENSURES: Returns the current mode hash
    pub fn mode_hash(&self) -> u64 {
        self.current_mode_hash
    }

    /// Update the environment hash.
    ///
    /// If the hash changes, the cache is cleared since cached results
    /// may no longer be valid. Statistics are preserved (hits/misses)
    /// but entries count is updated to reflect the cleared cache.
    ///
    /// # Contract
    ///
    /// ENSURES: `self.env_hash() == env_hash` after call
    /// ENSURES: If `old(env_hash()) != env_hash`, then `self.is_empty() == true`
    /// ENSURES: If `old(env_hash()) == env_hash`, cache contents unchanged
    pub fn set_env_hash(&mut self, env_hash: u64) {
        if self.current_env_hash != env_hash {
            drop_expr_values_iteratively(&mut self.results);
            self.current_env_hash = env_hash;
            self.stats.entries = 0;
        }
    }

    /// Update the mode hash.
    ///
    /// If the hash changes, the cache is cleared since cached results
    /// may no longer be valid under a different mode (e.g. Classical vs
    /// Constructive). Statistics are preserved (hits/misses) but entries
    /// count is updated to reflect the cleared cache.
    ///
    /// # Contract
    ///
    /// ENSURES: `self.mode_hash() == mode_hash` after call
    /// ENSURES: If `old(mode_hash()) != mode_hash`, then `self.is_empty() == true`
    /// ENSURES: If `old(mode_hash()) == mode_hash`, cache contents unchanged
    pub fn set_mode_hash(&mut self, mode_hash: u64) {
        if self.current_mode_hash != mode_hash {
            drop_expr_values_iteratively(&mut self.results);
            self.current_mode_hash = mode_hash;
            self.stats.entries = 0;
        }
    }

    /// Look up a cached type inference result.
    ///
    /// Returns `Some(type)` if the result is cached, `None` otherwise.
    /// Updates hit/miss statistics.
    ///
    /// # Contract
    ///
    /// ENSURES: `Some(&type_)` iff expression was previously inserted
    /// ENSURES: `self.stats().hits == old(stats().hits) + 1` if cache hit
    /// ENSURES: `self.stats().misses == old(stats().misses) + 1` if cache miss
    pub fn get(&mut self, expr: &Expr) -> Option<&Expr> {
        let id = TypeCheckId::new(expr, self.current_env_hash, self.current_mode_hash);
        if self.results.contains_key(&id) {
            self.stats.hits += 1;
            self.results.get(&id)
        } else {
            self.stats.misses += 1;
            None
        }
    }

    /// Insert a type inference result into the cache.
    ///
    /// If the cache exceeds [`MAX_CACHE_ENTRIES`], 1/[`EVICTION_FRACTION`] of
    /// entries are evicted (random selection via HashMap iteration order) to
    /// bound memory growth.
    ///
    /// # Contract
    ///
    /// ENSURES: Subsequent `get(expr)` returns `Some(&type_)`
    /// ENSURES: `self.stats().entries == self.len()`
    /// ENSURES: `self.len() <= MAX_CACHE_ENTRIES + 1`
    pub fn insert(&mut self, expr: &Expr, type_: Expr) {
        if self.results.len() >= MAX_CACHE_ENTRIES {
            self.evict();
        }
        let id = TypeCheckId::new(expr, self.current_env_hash, self.current_mode_hash);
        self.results.insert(id, type_);
        self.stats.entries = self.results.len();
    }

    /// Evict a fraction of cache entries to make room.
    fn evict(&mut self) {
        let to_remove = self.results.len() / EVICTION_FRACTION;
        let keys_to_remove: Vec<TypeCheckId> =
            self.results.keys().take(to_remove).cloned().collect();
        for key in keys_to_remove {
            if let Some(expr) = self.results.remove(&key) {
                iterative_drop(expr);
            }
        }
        self.stats.entries = self.results.len();
    }

    /// Get cache statistics.
    ///
    /// # Contract
    ///
    /// ENSURES: Returns reference to current statistics
    pub fn stats(&self) -> &TypeCheckCacheStats {
        &self.stats
    }

    /// Clear the cache and reset statistics.
    ///
    /// # Contract
    ///
    /// ENSURES: `self.is_empty() == true`
    /// ENSURES: `self.stats().hits == 0`
    /// ENSURES: `self.stats().misses == 0`
    /// ENSURES: `self.env_hash()` unchanged
    /// ENSURES: `self.mode_hash()` unchanged
    pub fn clear(&mut self) {
        drop_expr_values_iteratively(&mut self.results);
        self.stats = TypeCheckCacheStats::default();
    }

    /// Number of cached entries.
    ///
    /// # Contract
    ///
    /// ENSURES: `result == 0` iff `is_empty() == true`
    pub fn len(&self) -> usize {
        self.results.len()
    }

    /// Check if cache is empty.
    ///
    /// # Contract
    ///
    /// ENSURES: `result == true` iff `len() == 0`
    pub fn is_empty(&self) -> bool {
        self.results.is_empty()
    }
}

impl Drop for TypeCheckCache {
    fn drop(&mut self) {
        drop_expr_values_iteratively(&mut self.results);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::expr::{BinderInfo, Expr, ExprKind, ExprMeta, FVarId};
    use crate::level::Level;
    use crate::name::Name;

    #[test]
    fn test_type_check_id_equality() {
        let expr1 = Expr::from_kind(ExprKind::Sort(Level::zero()));
        let expr2 = Expr::from_kind(ExprKind::Sort(Level::zero()));
        let expr3 = Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero())));

        let id1 = TypeCheckId::new(&expr1, 0, 0);
        let id2 = TypeCheckId::new(&expr2, 0, 0);
        let id3 = TypeCheckId::new(&expr3, 0, 0);
        let id4 = TypeCheckId::new(&expr1, 1, 0); // Different env hash
        let id5 = TypeCheckId::new(&expr1, 0, 1); // Different mode hash

        assert_eq!(id1, id2, "Same expression should produce same ID");
        assert_ne!(
            id1, id3,
            "Different expressions should produce different IDs"
        );
        assert_ne!(id1, id4, "Different env hash should produce different ID");
        assert_ne!(id1, id5, "Different mode hash should produce different ID");
    }

    #[test]
    fn test_cache_basic_operations() {
        let mut cache = TypeCheckCache::new();

        let expr = Expr::const_(Name::from_string("Nat"), vec![]);
        let type_ = Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero())));

        // Initially not cached
        assert_eq!(cache.get(&expr), None, "uncached expr should return None");
        assert_eq!(cache.stats().misses, 1);

        // Insert and retrieve
        cache.insert(&expr, type_.clone());
        assert_eq!(cache.get(&expr), Some(&type_));
        assert_eq!(cache.stats().hits, 1);
        assert_eq!(cache.stats().misses, 1);
    }

    #[test]
    fn test_cache_env_invalidation() {
        let mut cache = TypeCheckCache::with_hashes(100, 0);

        let expr = Expr::const_(Name::from_string("Bool"), vec![]);
        let type_ = Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero())));

        cache.insert(&expr, type_.clone());
        assert_eq!(cache.len(), 1);
        assert_eq!(cache.stats().entries, 1);

        // Same env hash - cache preserved
        cache.set_env_hash(100);
        assert_eq!(cache.len(), 1);
        assert_eq!(cache.stats().entries, 1);

        // Different env hash - cache cleared
        cache.set_env_hash(200);
        assert_eq!(cache.len(), 0);
        assert_eq!(
            cache.stats().entries,
            0,
            "stats.entries should be updated on cache clear"
        );
    }

    #[test]
    fn test_cache_hit_rate() {
        let mut cache = TypeCheckCache::new();
        let expr = Expr::from_kind(ExprKind::Sort(Level::zero()));
        let type_ = Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero())));

        // 0 hits, 0 misses -> 0% hit rate
        assert_eq!(cache.stats().hit_rate(), 0.0);

        // 1 miss
        cache.get(&expr);
        assert_eq!(cache.stats().hit_rate(), 0.0);

        // Insert and get twice (2 hits, 1 miss -> 66.67% hit rate)
        cache.insert(&expr, type_);
        cache.get(&expr);
        cache.get(&expr);

        let hit_rate = cache.stats().hit_rate();
        assert!((hit_rate - 66.67).abs() < 0.1, "Hit rate should be ~66.67%");
    }

    #[test]
    fn test_cache_clear() {
        let mut cache = TypeCheckCache::with_hashes(42, 0);

        // Add some entries
        let expr1 = Expr::from_kind(ExprKind::Sort(Level::zero()));
        let expr2 = Expr::const_(Name::from_string("Nat"), vec![]);
        let type1 = Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero())));
        let type2 = Expr::from_kind(ExprKind::Sort(Level::succ(Level::succ(Level::zero()))));

        cache.insert(&expr1, type1);
        cache.insert(&expr2, type2);
        assert_eq!(cache.len(), 2);
        assert_eq!(cache.stats().entries, 2);

        // Generate some hits/misses for stats
        cache.get(&expr1); // hit
        cache.get(&Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero())))); // miss (different expr)

        // Clear the cache
        cache.clear();

        // Cache should be empty
        assert!(cache.is_empty());
        assert_eq!(cache.len(), 0);

        // Stats should be reset
        assert_eq!(cache.stats().hits, 0);
        assert_eq!(cache.stats().misses, 0);
        assert_eq!(cache.stats().entries, 0);
        assert_eq!(cache.stats().hit_rate(), 0.0);

        // Env and mode hashes should be preserved
        assert_eq!(cache.env_hash(), 42);
        assert_eq!(cache.mode_hash(), 0);
    }

    #[test]
    fn test_cache_clear_handles_deep_expression_drop() {
        let mut cache = TypeCheckCache::new();

        let key = Expr::const_(Name::from_string("DeepExpr"), vec![]);
        let func = Expr::const_(Name::from_string("f"), vec![]);
        let mut deep_type = Expr::fvar(FVarId::new(0));
        for _ in 0..20_000 {
            deep_type = Expr::app(func.clone(), deep_type);
        }

        cache.insert(&key, deep_type);
        cache.clear();

        assert!(cache.is_empty(), "cache clear should remove all entries");
    }

    #[test]
    fn test_cache_drop_handles_deep_expression_drop() {
        let key = Expr::const_(Name::from_string("DropDeepExpr"), vec![]);
        let func = Expr::const_(Name::from_string("f"), vec![]);
        let mut deep_type = Expr::fvar(FVarId::new(0));
        for _ in 0..20_000 {
            deep_type = Expr::app(func.clone(), deep_type);
        }

        let mut cache = TypeCheckCache::new();
        cache.insert(&key, deep_type);
        // cache dropped at end of scope; should not stack overflow.
    }

    #[test]
    fn test_cache_env_invalidation_handles_deep_expression_drop() {
        let mut cache = TypeCheckCache::with_hashes(1, 0);

        let key = Expr::const_(Name::from_string("EnvDeepExpr"), vec![]);
        let func = Expr::const_(Name::from_string("f"), vec![]);
        let mut deep_type = Expr::fvar(FVarId::new(0));
        for _ in 0..20_000 {
            deep_type = Expr::app(func.clone(), deep_type);
        }

        cache.insert(&key, deep_type);
        cache.set_env_hash(2);

        assert!(cache.is_empty(), "cache invalidation should clear entries");
    }

    #[test]
    fn test_cache_multiple_entries() {
        let mut cache = TypeCheckCache::new();

        // Create several distinct expressions
        let exprs: Vec<Expr> = (0..5)
            .map(|i| Expr::const_(Name::from_string(&format!("Const{i}")), vec![]))
            .collect();

        let types: Vec<Expr> = (0..5)
            .map(|_| Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero()))))
            .collect();

        // Insert all
        for (expr, type_) in exprs.iter().zip(types.iter()) {
            cache.insert(expr, type_.clone());
        }

        assert_eq!(cache.len(), 5);
        assert_eq!(cache.stats().entries, 5);

        // Verify all can be retrieved
        for (i, (expr, type_)) in exprs.iter().zip(types.iter()).enumerate() {
            let cached = cache.get(expr);
            assert_eq!(cached, Some(type_), "Entry {i} should be cached");
        }

        // All should be hits
        assert_eq!(cache.stats().hits, 5);
        assert_eq!(cache.stats().misses, 0);
    }

    #[test]
    fn test_cache_overwrite() {
        let mut cache = TypeCheckCache::new();

        let expr = Expr::const_(Name::from_string("X"), vec![]);
        let type1 = Expr::from_kind(ExprKind::Sort(Level::zero()));
        let type2 = Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero())));

        // Insert first type
        cache.insert(&expr, type1.clone());
        assert_eq!(cache.get(&expr), Some(&type1));

        // Overwrite with second type
        cache.insert(&expr, type2.clone());

        // Should return new type, entry count should be same
        assert_eq!(cache.get(&expr), Some(&type2));
        assert_eq!(cache.len(), 1);
        assert_eq!(cache.stats().entries, 1);
    }

    #[test]
    fn test_type_check_id_hash_stability() {
        // Verify that the same expression always produces the same ID
        // (important for cache correctness)
        let expr = Expr::const_(Name::from_string("Test"), vec![Level::zero()]);

        let id1 = TypeCheckId::new(&expr, 100, 0);
        let id2 = TypeCheckId::new(&expr, 100, 0);
        let id3 = TypeCheckId::new(&expr, 100, 0);

        assert_eq!(id1, id2);
        assert_eq!(id2, id3);

        // And different env hashes produce different IDs
        let id4 = TypeCheckId::new(&expr, 101, 0);
        assert_ne!(id1, id4);
    }

    #[test]
    fn test_stats_preserved_on_env_change() {
        let mut cache = TypeCheckCache::with_hashes(1, 0);

        let expr = Expr::from_kind(ExprKind::Sort(Level::zero()));
        let type_ = Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero())));

        // Generate stats
        cache.get(&expr); // miss
        cache.insert(&expr, type_.clone());
        cache.get(&expr); // hit

        assert_eq!(cache.stats().hits, 1);
        assert_eq!(cache.stats().misses, 1);

        // Change env hash - should clear cache but preserve hit/miss stats
        cache.set_env_hash(2);

        assert_eq!(cache.len(), 0);
        assert_eq!(cache.stats().entries, 0);
        // Note: hit/miss stats are preserved per current implementation
        assert_eq!(cache.stats().hits, 1);
        assert_eq!(cache.stats().misses, 1);
    }

    #[test]
    fn test_lambda_and_pi_expressions() {
        let mut cache = TypeCheckCache::new();

        // Create lambda and pi expressions
        let nat_type = Expr::const_(Name::from_string("Nat"), vec![]);
        let lambda = Expr::lam(
            BinderInfo::Default,
            nat_type.clone(),
            Expr::from_kind(ExprKind::BVar(0)),
        );
        let pi = Expr::pi(
            BinderInfo::Default,
            nat_type.clone(),
            Expr::from_kind(ExprKind::Sort(Level::zero())),
        );

        let lambda_type = Expr::pi(BinderInfo::Default, nat_type.clone(), nat_type.clone());
        let pi_type = Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero())));

        // Insert both
        cache.insert(&lambda, lambda_type.clone());
        cache.insert(&pi, pi_type.clone());

        assert_eq!(cache.len(), 2);
        assert_eq!(cache.get(&lambda), Some(&lambda_type));
        assert_eq!(cache.get(&pi), Some(&pi_type));
    }

    #[test]
    fn test_app_expression() {
        let mut cache = TypeCheckCache::new();

        // Create application expression: f(x)
        let f = Expr::const_(Name::from_string("f"), vec![]);
        let x = Expr::const_(Name::from_string("x"), vec![]);
        let app = Expr::app(f, x);

        let result_type = Expr::const_(Name::from_string("Result"), vec![]);
        cache.insert(&app, result_type.clone());

        assert_eq!(cache.get(&app), Some(&result_type));
    }

    #[test]
    fn test_bvar_expressions() {
        let mut cache = TypeCheckCache::new();

        // BVars with different indices
        let bvar0 = Expr::from_kind(ExprKind::BVar(0));
        let bvar1 = Expr::from_kind(ExprKind::BVar(1));
        let type_ = Expr::from_kind(ExprKind::Sort(Level::zero()));

        cache.insert(&bvar0, type_.clone());

        // Same BVar should hit
        assert_eq!(cache.get(&bvar0), Some(&type_));

        // Different BVar should miss
        assert_eq!(
            cache.get(&bvar1),
            None,
            "different BVar should not be cached"
        );
        assert_eq!(cache.stats().misses, 1);
    }

    #[test]
    fn test_nested_expression() {
        let mut cache = TypeCheckCache::new();

        // Deeply nested expression: λx. λy. (x y)
        let inner_app = Expr::app(
            Expr::from_kind(ExprKind::BVar(1)),
            Expr::from_kind(ExprKind::BVar(0)),
        );
        let inner_lam = Expr::lam(
            BinderInfo::Default,
            Expr::from_kind(ExprKind::Sort(Level::zero())),
            inner_app,
        );
        let outer_lam = Expr::lam(
            BinderInfo::Default,
            Expr::pi(
                BinderInfo::Default,
                Expr::from_kind(ExprKind::Sort(Level::zero())),
                Expr::from_kind(ExprKind::Sort(Level::zero())),
            ),
            inner_lam,
        );

        let type_ = Expr::pi(
            BinderInfo::Default,
            Expr::pi(
                BinderInfo::Default,
                Expr::from_kind(ExprKind::Sort(Level::zero())),
                Expr::from_kind(ExprKind::Sort(Level::zero())),
            ),
            Expr::pi(
                BinderInfo::Default,
                Expr::from_kind(ExprKind::Sort(Level::zero())),
                Expr::from_kind(ExprKind::Sort(Level::zero())),
            ),
        );

        cache.insert(&outer_lam, type_.clone());
        assert_eq!(cache.get(&outer_lam), Some(&type_));
    }

    #[test]
    fn test_const_with_universe_levels() {
        let mut cache = TypeCheckCache::new();

        // Constants with different universe levels
        let const_l0 = Expr::const_(Name::from_string("List"), vec![Level::zero()]);
        let const_l1 = Expr::const_(Name::from_string("List"), vec![Level::succ(Level::zero())]);

        let type_ = Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero())));

        cache.insert(&const_l0, type_.clone());

        // Same const should hit
        assert_eq!(cache.get(&const_l0), Some(&type_));

        // Different universe level should miss
        assert_eq!(
            cache.get(&const_l1),
            None,
            "different universe level should not be cached"
        );
    }

    #[test]
    fn test_default_trait() {
        // Verify Default trait implementation matches new()
        let default_cache: TypeCheckCache = Default::default();
        let new_cache = TypeCheckCache::new();

        assert_eq!(default_cache.len(), new_cache.len());
        assert_eq!(default_cache.env_hash(), new_cache.env_hash());
        assert_eq!(default_cache.mode_hash(), new_cache.mode_hash());
        assert_eq!(default_cache.is_empty(), new_cache.is_empty());
        assert_eq!(default_cache.stats().hits, new_cache.stats().hits);
        assert_eq!(default_cache.stats().misses, new_cache.stats().misses);
    }

    /// Test cache behavior under sustained load (below eviction threshold).
    ///
    /// Verifies:
    /// 1. Cache can handle many unique entries below MAX_CACHE_ENTRIES
    /// 2. Clear functionality correctly releases entries
    /// 3. Operations remain functional after heavy load
    #[test]
    fn test_cache_memory_pressure() {
        let mut cache = TypeCheckCache::new();

        // Phase 1: Insert many unique expressions
        // Using 10K instead of 100K for test speed; pattern still validates behavior
        const NUM_ENTRIES: usize = 10_000;

        for i in 0..NUM_ENTRIES {
            // Create unique expressions by varying the constant name
            let expr = Expr::const_(Name::from_string(&format!("Const_{i}")), vec![]);
            let type_ = Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero())));
            cache.insert(&expr, type_);
        }

        // 10K is below MAX_CACHE_ENTRIES (100K), so no eviction should occur
        assert_eq!(
            cache.len(),
            NUM_ENTRIES,
            "Cache should store all entries when below eviction threshold"
        );
        assert_eq!(cache.stats().entries, NUM_ENTRIES);

        // Phase 2: Verify retrieval still works for early entries
        let first_expr = Expr::const_(Name::from_string("Const_0"), vec![]);
        let first_result = cache.get(&first_expr);
        assert!(
            first_result.is_some(),
            "First entry should still be accessible"
        );
        assert_eq!(cache.stats().hits, 1);

        // Phase 3: Verify retrieval works for late entries
        let last_expr = Expr::const_(
            Name::from_string(&format!("Const_{}", NUM_ENTRIES - 1)),
            vec![],
        );
        let last_result = cache.get(&last_expr);
        assert!(
            last_result.is_some(),
            "Last entry should still be accessible"
        );
        assert_eq!(cache.stats().hits, 2);

        // Phase 4: Test clear functionality releases all entries
        cache.clear();
        assert!(
            cache.is_empty(),
            "Cache should be empty after clear under memory pressure"
        );
        assert_eq!(cache.len(), 0);
        assert_eq!(cache.stats().entries, 0);

        // Phase 5: Verify cache is still functional after clear
        let new_expr = Expr::const_(Name::from_string("NewConst"), vec![]);
        let new_type = Expr::from_kind(ExprKind::Sort(Level::zero()));
        cache.insert(&new_expr, new_type.clone());
        assert_eq!(cache.len(), 1);
        assert_eq!(cache.get(&new_expr), Some(&new_type));
    }

    /// Test cache scaling behavior with increasing load.
    ///
    /// Verifies that cache operations remain O(1) amortized as cache grows.
    /// A 16x size increase (100→1600) should not cause >20x increase in per-operation time.
    #[test]
    fn test_cache_scaling() {
        let _serial = crate::test_utils::serial_test_guard();
        use std::time::Instant;

        // Test sizes: 100, 400, 1600 (4x increases)
        let sizes = [100, 400, 1600];
        let mut insert_times = Vec::new();
        let mut lookup_times = Vec::new();

        for &n in &sizes {
            let mut cache = TypeCheckCache::new();

            // Measure insert time
            let start = Instant::now();
            for i in 0..n {
                let expr = Expr::const_(Name::from_string(&format!("C{i}")), vec![]);
                let type_ = Expr::from_kind(ExprKind::Sort(Level::zero()));
                cache.insert(&expr, type_);
            }
            insert_times.push(start.elapsed().as_nanos() / n as u128);

            // Measure lookup time (hit rate)
            let start = Instant::now();
            for i in 0..n {
                let expr = Expr::const_(Name::from_string(&format!("C{i}")), vec![]);
                let _ = cache.get(&expr);
            }
            lookup_times.push(start.elapsed().as_nanos() / n as u128);
        }

        // Check that 16x size increase (1600/100) doesn't cause >20x per-op time
        // (allowing overhead variance; HashMap should be ~O(1) amortized).
        // Use max(1) to avoid division by zero on fast hardware (#1785).
        let insert_ratio = insert_times[2] as f64 / insert_times[0].max(1) as f64;
        assert!(
            insert_ratio < 20.0,
            "Insert scaling appears non-O(1): 16x size gave {insert_ratio:.1}x time per op"
        );

        let lookup_ratio = lookup_times[2] as f64 / lookup_times[0].max(1) as f64;
        assert!(
            lookup_ratio < 20.0,
            "Lookup scaling appears non-O(1): 16x size gave {lookup_ratio:.1}x time per op"
        );
    }

    /// Test cache hit rate behavior under mixed workload.
    ///
    /// Simulates realistic usage patterns with repeated expressions.
    #[test]
    fn test_cache_hit_rate_under_load() {
        let mut cache = TypeCheckCache::new();

        // Create a small set of "hot" expressions that repeat frequently
        let hot_exprs: Vec<Expr> = (0..10)
            .map(|i| Expr::const_(Name::from_string(&format!("Hot{i}")), vec![]))
            .collect();
        let type_ = Expr::from_kind(ExprKind::Sort(Level::zero()));

        // Insert hot expressions
        for expr in &hot_exprs {
            cache.insert(expr, type_.clone());
        }

        // Simulate workload: 90% hot (hits), 10% cold (misses)
        for i in 0..1000 {
            if i % 10 == 0 {
                // Cold: new unique expression
                let cold_expr = Expr::const_(Name::from_string(&format!("Cold{i}")), vec![]);
                cache.insert(&cold_expr, type_.clone());
            } else {
                // Hot: repeated lookup
                let hot_expr = &hot_exprs[i % hot_exprs.len()];
                let _ = cache.get(hot_expr);
            }
        }

        // Verify hit rate is reasonable (should be ~90% for hot lookups)
        // Note: first 10 inserts don't count as hits/misses
        let hit_rate = cache.stats().hit_rate();
        assert!(
            hit_rate > 50.0,
            "Hit rate should be >50% with hot expression reuse, got {hit_rate:.1}%"
        );
    }

    /// Regression test for #1364: mode change must invalidate cache.
    ///
    /// Before the fix, TypeCheckId did not include mode_hash, so switching
    /// from Constructive to Classical would return stale cached types.
    #[test]
    fn test_cache_mode_invalidation() {
        let mut cache = TypeCheckCache::with_hashes(100, 10); // env=100, mode=10

        let expr = Expr::const_(Name::from_string("LEM"), vec![]);
        let type_ = Expr::from_kind(ExprKind::Sort(Level::zero()));

        cache.insert(&expr, type_.clone());
        assert_eq!(cache.len(), 1);
        assert_eq!(cache.get(&expr), Some(&type_));

        // Same mode hash — cache preserved
        cache.set_mode_hash(10);
        assert_eq!(cache.len(), 1);

        // Different mode hash — cache cleared
        cache.set_mode_hash(20);
        assert_eq!(cache.len(), 0);
        assert_eq!(
            cache.stats().entries,
            0,
            "stats.entries should be updated on mode change"
        );
        assert_eq!(cache.mode_hash(), 20);

        // Re-inserting under the new mode works
        cache.insert(&expr, type_.clone());
        assert_eq!(cache.len(), 1);
        assert_eq!(cache.get(&expr), Some(&type_));
    }

    /// Verify that mode_hash is part of the cache key so that the same
    /// expression under different modes produces different TypeCheckIds.
    #[test]
    fn test_mode_hash_in_cache_key() {
        let mut cache = TypeCheckCache::with_hashes(0, 10);
        let expr = Expr::const_(Name::from_string("P"), vec![]);
        let type_a = Expr::from_kind(ExprKind::Sort(Level::zero()));
        let type_b = Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero())));

        // Insert under mode 10
        cache.insert(&expr, type_a.clone());

        // Manually switch mode in the cache (simulating what set_mode does)
        // Without clearing — the old entry stays but is unreachable under the
        // new mode because the key includes mode_hash.
        cache.current_mode_hash = 20;

        // Same expr should miss under the new mode
        assert_eq!(
            cache.get(&expr),
            None,
            "same expr under different mode should miss"
        );

        // Insert under mode 20
        cache.insert(&expr, type_b.clone());

        // Now the cache has 2 entries (one per mode)
        assert_eq!(cache.len(), 2);

        // Switch back to mode 10 — original entry should still be there
        cache.current_mode_hash = 10;
        assert_eq!(
            cache.get(&expr),
            Some(&type_a),
            "original entry should survive under original mode"
        );
    }

    /// Regression test for #1771: hash collision must not return wrong type.
    ///
    /// Constructs two structurally different expressions with identical 32-bit
    /// hashes (forced via ExprMeta). Before the fix, both would map to the same
    /// TypeCheckId and the second insert would silently overwrite the first.
    /// After the fix, structural equality in TypeCheckId distinguishes them.
    #[test]
    fn test_cache_hash_collision_returns_correct_type() {
        // Pick a common hash value to force collision
        let collision_hash: u32 = 0xDEAD_BEEF;

        // Two structurally different expressions sharing the same 32-bit hash
        let expr_a = Expr::with_meta(
            ExprKind::BVar(0),
            ExprMeta::pack(collision_hash, 0, 0, false, false, false, false),
        );
        let expr_b = Expr::with_meta(
            ExprKind::BVar(1),
            ExprMeta::pack(collision_hash, 0, 0, false, false, false, false),
        );

        // Verify they are structurally different but hash-identical
        assert_ne!(expr_a, expr_b, "expressions must be structurally different");
        assert_eq!(
            expr_a.hash_cached(),
            expr_b.hash_cached(),
            "expressions must share the same 32-bit hash for this test"
        );

        // Two distinct result types
        let type_a = Expr::from_kind(ExprKind::Sort(Level::zero()));
        let type_b = Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero())));

        let mut cache = TypeCheckCache::new();
        cache.insert(&expr_a, type_a.clone());
        cache.insert(&expr_b, type_b.clone());

        // Both entries must coexist — collision must NOT cause overwrite
        assert_eq!(
            cache.len(),
            2,
            "hash-colliding expressions must be stored as separate entries"
        );

        // Each expression must retrieve its own type
        assert_eq!(
            cache.get(&expr_a),
            Some(&type_a),
            "expr_a must return type_a, not type_b"
        );
        assert_eq!(
            cache.get(&expr_b),
            Some(&type_b),
            "expr_b must return type_b, not type_a"
        );
    }

    /// Verify that TypeCheckId structural equality rejects colliding hashes.
    #[test]
    fn test_type_check_id_rejects_hash_collision() {
        let collision_hash: u32 = 0xCAFE_BABE;

        let expr_a = Expr::with_meta(
            ExprKind::BVar(0),
            ExprMeta::pack(collision_hash, 0, 0, false, false, false, false),
        );
        let expr_b = Expr::with_meta(
            ExprKind::BVar(1),
            ExprMeta::pack(collision_hash, 0, 0, false, false, false, false),
        );

        let id_a = TypeCheckId::new(&expr_a, 0, 0);
        let id_b = TypeCheckId::new(&expr_b, 0, 0);

        // Hash fields are identical (would collide in HashMap bucket)
        assert_eq!(id_a.expr_hash, id_b.expr_hash, "hash fields must match");
        assert_eq!(id_a.env_hash, id_b.env_hash);
        assert_eq!(id_a.mode_hash, id_b.mode_hash);

        // But PartialEq must reject due to structural difference
        assert_ne!(
            id_a, id_b,
            "TypeCheckId must distinguish structurally different expressions \
             even when all hash fields match (soundness requirement)"
        );
    }

    #[test]
    fn test_cache_eviction_bounds_size() {
        let mut cache = TypeCheckCache::new();
        let type_ = Expr::from_kind(ExprKind::Sort(Level::zero()));

        // Insert more than MAX_CACHE_ENTRIES
        let total = MAX_CACHE_ENTRIES + 500;
        for i in 0..total {
            let expr = Expr::const_(Name::from_string(&format!("E{i}")), vec![]);
            cache.insert(&expr, type_.clone());
        }

        // Cache should be bounded: after eviction it holds at most
        // MAX_CACHE_ENTRIES - (MAX_CACHE_ENTRIES / EVICTION_FRACTION) + 500 + 1
        assert!(
            cache.len() <= MAX_CACHE_ENTRIES + 1,
            "cache should be bounded by eviction; got {} entries",
            cache.len()
        );
        assert_eq!(cache.stats().entries, cache.len());

        // Cache should still be functional after eviction
        let probe = Expr::const_(Name::from_string("PostEvict"), vec![]);
        cache.insert(&probe, type_.clone());
        assert_eq!(cache.get(&probe), Some(&type_));
    }
}
