// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Name lookup index using sorted Vec + binary search.
//!
//! O(log n) exact lookup and O(log n + k) prefix search where k is the
//! number of matching entries. No bloom filter needed at this layer — the
//! shard-level bloom filter in `shard.rs` handles that.

use serde::{Deserialize, Serialize};

/// A reference to a constant within a specific shard.
///
/// Encapsulates the shard index and the constant's position within that shard,
/// enabling cross-shard name resolution without loading full shard contents.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct ConstantRef {
    /// Index of the shard containing this constant.
    pub shard_idx: u32,
    /// Index of the constant within the shard.
    pub constant_idx: u32,
}

/// A name-indexed entry: the name string and the constant index it maps to.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NameEntry {
    pub name: String,
    pub constant_idx: u32,
}

/// A name-indexed entry with shard location for cross-shard lookup.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShardNameEntry {
    pub name: String,
    pub constant_ref: ConstantRef,
}

/// Sorted name index for O(log n) lookup by qualified name.
///
/// Built once from a collection of entries, then immutable for queries.
/// Uses `Vec` + binary search rather than a HashMap for cache-friendly
/// access patterns on sorted data.
pub struct NameIndex {
    /// Sorted by name (lexicographic).
    entries: Vec<NameEntry>,
}

impl NameIndex {
    /// Build a name index from unsorted entries.
    #[must_use]
    pub fn build(mut entries: Vec<NameEntry>) -> Self {
        entries.sort_unstable_by(|a, b| a.name.cmp(&b.name));
        Self { entries }
    }

    /// Exact name lookup. Returns all constant indices with the given name.
    #[must_use]
    pub fn search_exact(&self, name: &str) -> Vec<u32> {
        let pos = self.entries.partition_point(|e| e.name.as_str() < name);
        let mut results = Vec::new();
        for entry in &self.entries[pos..] {
            if entry.name == name {
                results.push(entry.constant_idx);
            } else {
                break;
            }
        }
        results
    }

    /// Prefix search. Returns all entries whose name starts with `prefix`.
    #[must_use]
    pub fn search_prefix(&self, prefix: &str) -> Vec<&NameEntry> {
        let pos = self.entries.partition_point(|e| e.name.as_str() < prefix);
        let mut results = Vec::new();
        for entry in &self.entries[pos..] {
            if entry.name.starts_with(prefix) {
                results.push(entry);
            } else {
                break;
            }
        }
        results
    }

    /// Number of entries in the index.
    #[must_use]
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    /// Whether the index is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }
}

// ---------------------------------------------------------------------------
// ShardNameIndex — shard-aware O(log n) name lookup
// ---------------------------------------------------------------------------

/// Shard-aware name index for O(1) name lookup returning [`ConstantRef`]s.
///
/// Built from shard metadata, maps qualified names to their shard locations.
/// Uses a HashMap for O(1) exact lookup and a sorted Vec for prefix search.
pub struct ShardNameIndex {
    /// Exact lookup: name -> constant references (may be multiple if
    /// the same name appears in different shards/systems).
    exact: std::collections::HashMap<String, Vec<ConstantRef>>,
    /// Sorted entries for prefix search.
    sorted: Vec<ShardNameEntry>,
}

impl ShardNameIndex {
    /// Build a shard name index from entries.
    #[must_use]
    pub fn build(entries: Vec<ShardNameEntry>) -> Self {
        let mut exact: std::collections::HashMap<String, Vec<ConstantRef>> =
            std::collections::HashMap::new();
        for entry in &entries {
            exact
                .entry(entry.name.clone())
                .or_default()
                .push(entry.constant_ref.clone());
        }

        let mut sorted = entries;
        sorted.sort_unstable_by(|a, b| a.name.cmp(&b.name));

        Self { exact, sorted }
    }

    /// O(1) exact name lookup. Returns the first matching [`ConstantRef`],
    /// or `None` if the name is not in the index.
    #[must_use]
    pub fn lookup(&self, name: &str) -> Option<ConstantRef> {
        self.exact.get(name).and_then(|refs| refs.first()).cloned()
    }

    /// O(1) exact name lookup returning all matching constant references.
    /// A name may resolve to multiple constants if it exists in multiple shards.
    #[must_use]
    pub fn lookup_all(&self, name: &str) -> Vec<ConstantRef> {
        self.exact.get(name).cloned().unwrap_or_default()
    }

    /// Prefix search returning all [`ConstantRef`]s whose name starts with `prefix`.
    /// Uses binary search on the sorted entry list: O(log n + k).
    #[must_use]
    pub fn prefix_search(&self, prefix: &str) -> Vec<ConstantRef> {
        let pos = self.sorted.partition_point(|e| e.name.as_str() < prefix);
        let mut results = Vec::new();
        for entry in &self.sorted[pos..] {
            if entry.name.starts_with(prefix) {
                results.push(entry.constant_ref.clone());
            } else {
                break;
            }
        }
        results
    }

    /// Number of entries in the index.
    #[must_use]
    pub fn len(&self) -> usize {
        self.sorted.len()
    }

    /// Whether the index is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.sorted.is_empty()
    }

    /// Number of distinct names.
    #[must_use]
    pub fn name_count(&self) -> usize {
        self.exact.len()
    }
}
