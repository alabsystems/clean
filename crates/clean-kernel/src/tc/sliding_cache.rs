// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Double-buffer ("sliding window") cache with generational eviction.
//!
//! Replaces the clear-all eviction strategy that creates performance cliffs
//! when caches hit their size threshold. Instead of wiping all entries:
//!
//! 1. `previous` (cold) generation is dropped
//! 2. `current` (warm) generation is demoted to `previous`
//! 3. A new empty `current` generation starts
//!
//! Lookups check both generations. Hits in `previous` promote the entry to
//! `current`, ensuring frequently-accessed entries survive eviction cycles.
//!
//! Part of #2410: eliminates TC cache cliff at 100K entries.

use std::hash::Hash;

use super::TcHashMap;

/// Cache operation counters for observability.
///
/// Tracks hits (current vs promoted), misses, inserts, and eviction slides
/// to enable profiling and threshold tuning for Mathlib-scale workloads.
///
/// Part of #2410: cache observability for sliding window tuning.
#[derive(Debug, Clone, Default)]
pub(crate) struct SlidingCacheStats {
    /// Lookups that found the key in the current generation.
    pub(crate) hits_current: u64,
    /// Lookups that found the key in the previous generation (promoted to current).
    pub(crate) hits_promoted: u64,
    /// Lookups that found no matching key.
    pub(crate) misses: u64,
    /// Number of sliding window evictions (trim_if_needed triggered).
    pub(crate) slides: u64,
}

#[cfg(test)]
impl SlidingCacheStats {
    /// Total cache lookups (hits + misses).
    pub(crate) fn total_lookups(&self) -> u64 {
        self.hits_current + self.hits_promoted + self.misses
    }

    /// Hit rate as a fraction in [0.0, 1.0]. Returns 0.0 if no lookups.
    pub(crate) fn hit_rate(&self) -> f64 {
        let total = self.total_lookups();
        if total == 0 {
            return 0.0;
        }
        (self.hits_current + self.hits_promoted) as f64 / total as f64
    }

    /// Promotion rate: fraction of hits that came from the previous generation.
    /// Returns 0.0 if no hits.
    pub(crate) fn promotion_rate(&self) -> f64 {
        let total_hits = self.hits_current + self.hits_promoted;
        if total_hits == 0 {
            return 0.0;
        }
        self.hits_promoted as f64 / total_hits as f64
    }
}

/// Double-buffer cache with sliding window eviction.
///
/// Each cache holds two hash maps: `current` (hot) and `previous` (cold).
/// When `current` exceeds the size threshold, it becomes `previous` and a
/// fresh `current` is created. Lookups that hit `previous` promote entries
/// to `current`, preserving the hot working set across eviction boundaries.
///
/// Memory usage is bounded at ~2x the threshold (one full `current` + one
/// full `previous`), compared to 1x with clear-all. The tradeoff is
/// eliminating latency spikes from full cache rebuilds.
pub(crate) struct SlidingCache<K, V> {
    current: TcHashMap<K, V>,
    previous: TcHashMap<K, V>,
    stats: SlidingCacheStats,
}

impl<K, V> Default for SlidingCache<K, V> {
    fn default() -> Self {
        Self {
            current: Default::default(),
            previous: Default::default(),
            stats: SlidingCacheStats::default(),
        }
    }
}

impl<K: Eq + Hash + Clone, V: Clone> SlidingCache<K, V> {
    /// Look up a key, promoting from `previous` to `current` on hit.
    ///
    /// Returns a clone of the cached value if found in either generation.
    /// Entries found in `previous` are moved to `current` so they survive
    /// the next eviction cycle.
    pub(crate) fn get(&mut self, key: &K) -> Option<V> {
        if let Some(v) = self.current.get(key) {
            self.stats.hits_current += 1;
            return Some(v.clone());
        }
        // Promote from previous → current to preserve hot entries
        if let Some((k, v)) = self.previous.remove_entry(key) {
            self.stats.hits_promoted += 1;
            let result = v.clone();
            self.current.insert(k, v);
            Some(result)
        } else {
            self.stats.misses += 1;
            None
        }
    }

    /// Insert a key-value pair into the current generation.
    pub(crate) fn insert(&mut self, key: K, value: V) {
        self.current.insert(key, value);
    }

    /// Slide the window if `current` exceeds the threshold.
    ///
    /// Returns `true` if eviction occurred. Unlike clear-all, this retains
    /// entries in `previous` for promotion on subsequent lookups.
    pub(crate) fn trim_if_needed(&mut self, max: usize) -> bool {
        if self.current.len() > max {
            self.stats.slides += 1;
            // Drop cold generation, demote current → previous
            self.previous = std::mem::take(&mut self.current);
            true
        } else {
            false
        }
    }

    /// Clear both generations. Used on context/mode/transparency changes.
    pub(crate) fn clear(&mut self) {
        self.current.clear();
        self.previous.clear();
    }

    /// Total entries across both generations.
    pub(crate) fn len(&self) -> usize {
        self.current.len() + self.previous.len()
    }

    /// Snapshot of cache operation counters.
    #[cfg(test)]
    pub(crate) fn stats(&self) -> &SlidingCacheStats {
        &self.stats
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

    /// Helper: create a SlidingCache<i32, String> for testing.
    fn make_cache() -> SlidingCache<i32, String> {
        SlidingCache::default()
    }

    #[test]
    fn test_basic_insert_and_get() {
        let mut cache = make_cache();
        cache.insert(1, "one".to_string());
        cache.insert(2, "two".to_string());

        assert_eq!(cache.get(&1), Some("one".to_string()));
        assert_eq!(cache.get(&2), Some("two".to_string()));
        assert_eq!(cache.get(&3), None);
        assert_eq!(cache.len(), 2);
    }

    #[test]
    fn test_trim_slides_window() {
        let mut cache = make_cache();
        // Insert 5 entries with max=3
        for i in 0..5 {
            cache.insert(i, format!("val{i}"));
        }
        assert_eq!(cache.len(), 5);

        // Trim should slide: current→previous, new empty current
        assert!(cache.trim_if_needed(3));
        // All 5 entries now in previous, current is empty
        assert_eq!(cache.current.len(), 0);
        assert_eq!(cache.previous.len(), 5);
        assert_eq!(cache.len(), 5);
    }

    #[test]
    fn test_promotion_on_get() {
        let mut cache = make_cache();
        for i in 0..5 {
            cache.insert(i, format!("val{i}"));
        }

        // Trigger trim
        cache.trim_if_needed(3);
        assert_eq!(cache.current.len(), 0);
        assert_eq!(cache.previous.len(), 5);

        // Access key 2 — should promote from previous to current
        assert_eq!(cache.get(&2), Some("val2".to_string()));
        assert_eq!(cache.current.len(), 1);
        assert_eq!(cache.previous.len(), 4);

        // Access key 2 again — now from current
        assert_eq!(cache.get(&2), Some("val2".to_string()));
        assert_eq!(cache.current.len(), 1);
        assert_eq!(cache.previous.len(), 4);
    }

    #[test]
    fn test_second_trim_drops_cold_entries() {
        let mut cache = make_cache();
        // Phase 1: fill and trim
        for i in 0..5 {
            cache.insert(i, format!("v1_{i}"));
        }
        cache.trim_if_needed(3);

        // Promote keys 0 and 1 (hot)
        cache.get(&0);
        cache.get(&1);

        // Phase 2: add new entries and trim again
        for i in 10..14 {
            cache.insert(i, format!("v2_{i}"));
        }
        // current has 2 promoted + 4 new = 6, previous has 3 unpromoted
        assert_eq!(cache.current.len(), 6);
        assert_eq!(cache.previous.len(), 3);

        cache.trim_if_needed(3);
        // After trim: old previous (keys 2,3,4) dropped permanently
        // Current (keys 0,1,10,11,12,13) moved to previous
        assert_eq!(cache.current.len(), 0);
        assert_eq!(cache.previous.len(), 6);

        // Keys 0 and 1 survived (were promoted before second trim)
        assert_eq!(cache.get(&0), Some("v1_0".to_string()));
        assert_eq!(cache.get(&1), Some("v1_1".to_string()));
        // Keys 2,3,4 are gone (were cold in previous, dropped on second trim)
        assert_eq!(cache.get(&2), None);
        assert_eq!(cache.get(&3), None);
    }

    #[test]
    fn test_clear_empties_both() {
        let mut cache = make_cache();
        for i in 0..5 {
            cache.insert(i, format!("val{i}"));
        }
        cache.trim_if_needed(3);
        cache.insert(99, "new".to_string());

        assert!(!cache.is_empty());
        cache.clear();
        assert!(cache.is_empty());
        assert_eq!(cache.len(), 0);
    }

    #[test]
    fn test_no_trim_below_threshold() {
        let mut cache = make_cache();
        cache.insert(1, "one".to_string());
        cache.insert(2, "two".to_string());

        assert!(!cache.trim_if_needed(5));
        assert_eq!(cache.current.len(), 2);
        assert_eq!(cache.previous.len(), 0);
    }

    #[test]
    fn test_stats_tracking() {
        let mut cache = make_cache();
        cache.insert(1, "one".to_string());
        cache.insert(2, "two".to_string());

        // Hit in current
        assert_eq!(cache.get(&1), Some("one".to_string()));
        assert_eq!(cache.stats().hits_current, 1);
        assert_eq!(cache.stats().hits_promoted, 0);
        assert_eq!(cache.stats().misses, 0);

        // Miss
        assert_eq!(cache.get(&99), None);
        assert_eq!(cache.stats().misses, 1);

        // Slide and then access — promotes from previous
        cache.trim_if_needed(0);
        assert_eq!(cache.stats().slides, 1);

        assert_eq!(cache.get(&1), Some("one".to_string()));
        assert_eq!(cache.stats().hits_promoted, 1);

        // Same key again — now in current
        assert_eq!(cache.get(&1), Some("one".to_string()));
        assert_eq!(cache.stats().hits_current, 2);

        // Verify derived stats
        assert_eq!(cache.stats().total_lookups(), 4);
        assert!(cache.stats().hit_rate() > 0.7);
        assert!(cache.stats().promotion_rate() > 0.0);
    }
}
