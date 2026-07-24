// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Double-buffer ("sliding window") wrapper for `EquivManager`.
//!
//! Applies the same generational eviction strategy as `SlidingCache` (#2410)
//! to the equivalence manager. When `current` exceeds the size threshold:
//!
//! 1. `previous` (cold) EquivManager is dropped
//! 2. `current` (warm) is demoted to `previous`
//! 3. A new empty `current` starts
//!
//! Lookups check both generations independently. Each generation maintains
//! its own complete union-find, so intra-generation transitivity is preserved.
//! Cross-generation transitivity is lost, but this is acceptable because:
//! - The equiv_manager is a pure optimization (memoization of is_def_eq results)
//! - Missing a transitive link just falls through to the def_eq_cache or recomputation
//! - Hot equivalences are naturally re-added to `current` via `is_def_eq`'s
//!   post-result `add_equiv` call, providing implicit promotion
//!
//! Part of #2410: eliminates equiv_manager cache cliff at 100K entries.

use crate::expr::Expr;

use super::equiv_manager::EquivManager;

/// Equivalence manager operation counters for observability.
///
/// Tracks hits (current vs previous generation), misses, and eviction slides.
/// Unlike `SlidingCacheStats`, there is no explicit promotion — hot equivalences
/// are implicitly promoted via `add_equiv` after a positive `is_def_eq` result.
///
/// Part of #2410: cache observability for sliding window tuning.
#[derive(Debug, Clone, Default)]
pub(crate) struct SlidingEquivStats {
    /// Lookups resolved by the current generation.
    pub(crate) hits_current: u64,
    /// Lookups resolved by the previous generation (not found in current).
    pub(crate) hits_previous: u64,
    /// Lookups that found no match in either generation.
    pub(crate) misses: u64,
    /// Number of sliding window evictions.
    pub(crate) slides: u64,
}

/// Double-buffer equivalence manager with sliding window eviction.
///
/// Each generation holds an independent union-find. When `current` exceeds
/// the size threshold, it becomes `previous` and a fresh `current` starts.
/// Lookups check both generations. Memory bounded at ~2x threshold.
pub(crate) struct SlidingEquivManager {
    current: EquivManager,
    previous: EquivManager,
    stats: SlidingEquivStats,
}

impl Default for SlidingEquivManager {
    fn default() -> Self {
        Self::new()
    }
}

impl SlidingEquivManager {
    pub(crate) fn new() -> Self {
        SlidingEquivManager {
            current: EquivManager::new(),
            previous: EquivManager::new(),
            stats: SlidingEquivStats::default(),
        }
    }

    /// Check if two expressions are known-equivalent in either generation.
    pub(crate) fn is_equiv(&mut self, a: &Expr, b: &Expr, use_hash: bool) -> bool {
        if self.current.is_equiv(a, b, use_hash) {
            self.stats.hits_current += 1;
            return true;
        }
        if self.previous.is_equiv(a, b, use_hash) {
            self.stats.hits_previous += 1;
            return true;
        }
        self.stats.misses += 1;
        false
    }

    /// Record that two expressions are definitionally equal (current generation only).
    pub(crate) fn add_equiv(&mut self, a: &Expr, b: &Expr) {
        self.current.add_equiv(a, b);
    }

    /// Slide the window if `current` exceeds the threshold.
    ///
    /// Returns `true` if eviction occurred. Unlike clear-all, this retains
    /// the previous generation's equivalence knowledge for lookups.
    pub(crate) fn trim_if_needed(&mut self, max: usize) -> bool {
        if self.current.len() > max {
            self.stats.slides += 1;
            self.previous = std::mem::take(&mut self.current);
            true
        } else {
            false
        }
    }

    /// Clear both generations. Called on context mutation, mode change,
    /// or transparency change.
    pub(crate) fn clear(&mut self) {
        self.current.clear();
        self.previous.clear();
    }

    /// Total entries across both generations.
    #[cfg(test)]
    pub(crate) fn len(&self) -> usize {
        self.current.len() + self.previous.len()
    }

    /// Whether both generations are empty.
    #[cfg(test)]
    pub(crate) fn is_empty(&self) -> bool {
        self.current.is_empty() && self.previous.is_empty()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::expr::ExprKind;
    use crate::Level;
    use std::sync::Arc;

    fn mk_sort(n: u32) -> Expr {
        Expr::from_kind(ExprKind::Sort(Level::zero().add_offset(n)))
    }

    fn mk_app(f: &Expr, a: &Expr) -> Expr {
        Expr::from_kind(ExprKind::App(Arc::new(f.clone()), Arc::new(a.clone())))
    }

    fn mk_bvar(idx: u32) -> Expr {
        Expr::from_kind(ExprKind::BVar(idx))
    }

    #[test]
    fn test_basic_equiv() {
        let mut sem = SlidingEquivManager::new();
        let (a, b) = (mk_sort(0), mk_sort(1));
        assert!(!sem.is_equiv(&a, &b, true));
        sem.add_equiv(&a, &b);
        assert!(sem.is_equiv(&a, &b, true));
    }

    #[test]
    fn test_trim_preserves_previous() {
        let mut sem = SlidingEquivManager::new();

        // Add equivalences to current generation
        let (a, b) = (mk_sort(0), mk_sort(1));
        let (c, d) = (mk_sort(2), mk_sort(3));
        sem.add_equiv(&a, &b);
        sem.add_equiv(&c, &d);

        // Trim with threshold below current size (4 entries: a,b,c,d)
        assert!(sem.trim_if_needed(3));

        // Equivalences survive in the previous generation
        assert!(
            sem.is_equiv(&a, &b, true),
            "equivalences in previous generation should still be found"
        );
        assert!(
            sem.is_equiv(&c, &d, true),
            "equivalences in previous generation should still be found"
        );
    }

    #[test]
    fn test_second_trim_drops_cold() {
        let mut sem = SlidingEquivManager::new();

        // Phase 1: add to current, trim (→ previous)
        let (a, b) = (mk_sort(0), mk_sort(1));
        sem.add_equiv(&a, &b);
        sem.trim_if_needed(0); // force slide

        // Phase 2: add new equivalences to current, trim again
        let (c, d) = (mk_sort(2), mk_sort(3));
        sem.add_equiv(&c, &d);
        sem.trim_if_needed(0); // force slide: old previous (a≡b) dropped

        // Phase 1 equivalences are gone (were in previous, now dropped)
        assert!(
            !sem.is_equiv(&a, &b, true),
            "cold generation should be dropped on second trim"
        );
        // Phase 2 equivalences survive (now in previous)
        assert!(
            sem.is_equiv(&c, &d, true),
            "demoted generation should survive one trim"
        );
    }

    #[test]
    fn test_no_trim_below_threshold() {
        let mut sem = SlidingEquivManager::new();
        let (a, b) = (mk_sort(0), mk_sort(1));
        sem.add_equiv(&a, &b);
        assert!(!sem.trim_if_needed(100));
        assert_eq!(sem.len(), 2);
    }

    #[test]
    fn test_clear() {
        let mut sem = SlidingEquivManager::new();
        let (a, b) = (mk_sort(0), mk_sort(1));
        sem.add_equiv(&a, &b);
        sem.trim_if_needed(0); // slide to previous
        let (c, d) = (mk_sort(2), mk_sort(3));
        sem.add_equiv(&c, &d);

        assert!(!sem.is_empty());
        sem.clear();
        assert!(sem.is_empty());
        assert_eq!(sem.len(), 0);
    }

    #[test]
    fn test_len_counts_both_generations() {
        let mut sem = SlidingEquivManager::new();
        let (a, b) = (mk_sort(0), mk_sort(1));
        sem.add_equiv(&a, &b);
        assert_eq!(sem.len(), 2);

        sem.trim_if_needed(0); // slide: 2 entries in previous
        let (c, d) = (mk_sort(2), mk_sort(3));
        sem.add_equiv(&c, &d);
        // 2 in previous + 2 in current = 4
        assert_eq!(sem.len(), 4);
    }

    /// Verify that natural re-addition after trim provides implicit promotion.
    /// When is_def_eq finds a result via the previous generation, it calls
    /// add_equiv on the positive result, which adds to current. This means
    /// hot equivalences migrate to current generation without explicit promotion.
    #[test]
    fn test_implicit_promotion_via_readd() {
        let mut sem = SlidingEquivManager::new();

        // Add and slide to previous
        let (a, b) = (mk_sort(0), mk_sort(1));
        sem.add_equiv(&a, &b);
        sem.trim_if_needed(0);

        // Simulate what is_def_eq does: find in previous, then re-add
        assert!(sem.is_equiv(&a, &b, true)); // found in previous
        sem.add_equiv(&a, &b); // re-added to current (implicit promotion)

        // Second trim: old previous dropped, but a≡b is in new current
        sem.trim_if_needed(0);

        // Still found because it was re-added to current before the second trim
        assert!(
            sem.is_equiv(&a, &b, true),
            "re-added equivalences should survive second trim"
        );
    }

    /// Verify independence between generations: adding to current doesn't
    /// affect queries that only hit previous, and vice versa.
    #[test]
    fn test_generation_independence() {
        let mut sem = SlidingEquivManager::new();

        // Add A≡B and slide to previous
        let (a, b) = (mk_sort(0), mk_sort(1));
        sem.add_equiv(&a, &b);
        sem.trim_if_needed(0);

        // Add C≡D to current (different from previous)
        let (c, d) = (mk_sort(2), mk_sort(3));
        sem.add_equiv(&c, &d);

        // A≡B only in previous, C≡D only in current
        assert!(sem.is_equiv(&a, &b, true)); // previous
        assert!(sem.is_equiv(&c, &d, true)); // current

        // No cross-generation transitivity: A≢C even though both exist
        assert!(!sem.is_equiv(&a, &c, true));
        assert!(!sem.is_equiv(&b, &d, true));
    }

    /// Verify grows-without-bound behavior matches inner EquivManager.
    #[test]
    fn test_grows_without_explicit_trim() {
        let mut sem = SlidingEquivManager::new();

        for i in 0..1_000u32 {
            let a = mk_app(&mk_sort(i), &mk_bvar(0));
            let b = mk_app(&mk_sort(i), &mk_bvar(1));
            sem.add_equiv(&a, &b);
        }

        // 2K entries in current, none in previous
        assert!(
            sem.len() >= 2_000,
            "should accumulate >=2K entries without trim, got {}",
            sem.len()
        );
    }
}
