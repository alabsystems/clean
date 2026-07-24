// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Retrieval index for the Mathverse Library.
//!
//! Provides fast lookup of theorems by:
//! - **Discrimination tree** — structural matching on expression shape
//! - **Bloom filter** — fast negative lookups by name
//! - **Name index** — exact and prefix search by qualified name (sorted Vec + binary search)
//! - **Type index** — type-directed search by head symbol
//! - **Dependency graph** — adjacency list for dependency walking
//! - **Source index** — filter by source system
//!
//! The [`MathverseSearch`] trait provides a unified interface for all search modes.

pub mod dependency_graph;
pub mod name_index;
pub mod type_index;

#[cfg(test)]
mod tests;

use std::collections::HashMap;

use crate::retrieval::dependency_graph::DependencyGraph;
use crate::retrieval::name_index::{NameEntry, NameIndex};
use crate::retrieval::type_index::{HeadSymbol, TypeIndex, TypeIndexEntry};
use crate::trust::trust_enforcement::{TrustEnforcer, TrustPolicy};
use crate::types::{AxiomProfile, SourceSystem, TrustLevel};

// Re-export key types for consumer convenience.
pub use name_index::{ConstantRef, ShardNameEntry, ShardNameIndex};
pub use type_index::{FingerprintEntry, FingerprintTypeIndex, TypeFingerprint};

// ─── MathverseSearch trait ──────────────────────────────────────────────────

/// Unified search interface for the Mathverse Library.
///
/// Provides name lookup, type-directed search, and dependency walking
/// across all indexed constants regardless of source system.
pub trait MathverseSearch {
    /// Search for constants by exact name.
    fn search_by_name(&self, name: &str) -> Vec<u32>;

    /// Search for constants by name prefix.
    fn search_by_name_prefix(&self, prefix: &str) -> Vec<u32>;

    /// Search for constants whose type has the given head symbol.
    fn search_by_type(&self, head: &HeadSymbol) -> Vec<u32>;

    /// Get direct dependencies of a constant.
    fn search_dependencies(&self, constant_idx: u32) -> Vec<u32>;

    /// Get transitive dependencies of a constant.
    fn search_transitive_dependencies(&self, constant_idx: u32) -> Vec<u32>;

    /// Get constants that depend on the given constant.
    fn search_reverse_dependencies(&self, constant_idx: u32) -> Vec<u32>;
}

/// Builder for a composite search index.
///
/// Accumulate constants and dependencies via `add_constant` / `add_dependency`,
/// then call [`build`](CompositeSearchBuilder::build) to produce a frozen
/// [`CompositeSearch`] that implements [`MathverseSearch`].
pub struct CompositeSearchBuilder {
    name_entries: Vec<NameEntry>,
    type_entries: Vec<TypeIndexEntry>,
    dep_edges: Vec<(u32, u32)>,
    max_idx: u32,
}

impl CompositeSearchBuilder {
    /// Create a new empty builder.
    #[must_use]
    pub fn new() -> Self {
        Self {
            name_entries: Vec::new(),
            type_entries: Vec::new(),
            dep_edges: Vec::new(),
            max_idx: 0,
        }
    }

    /// Register a constant for indexing.
    pub fn add_constant(&mut self, constant_idx: u32, name: &str, head: HeadSymbol) {
        self.name_entries.push(NameEntry {
            name: name.to_owned(),
            constant_idx,
        });
        self.type_entries
            .push(TypeIndexEntry { constant_idx, head });
        if constant_idx >= self.max_idx {
            self.max_idx = constant_idx + 1;
        }
    }

    /// Register a dependency: `from` depends on `to`.
    pub fn add_dependency(&mut self, from: u32, to: u32) {
        self.dep_edges.push((from, to));
        let m = from.max(to) + 1;
        if m > self.max_idx {
            self.max_idx = m;
        }
    }

    /// Build the frozen search index.
    #[must_use]
    pub fn build(self) -> CompositeSearch {
        let name_index = NameIndex::build(self.name_entries);
        let type_index = TypeIndex::build(self.type_entries);
        let mut dep_graph = DependencyGraph::new(self.max_idx as usize);
        for (from, to) in self.dep_edges {
            dep_graph.add_dependency(from, to);
        }
        CompositeSearch {
            name_index,
            type_index,
            dep_graph,
        }
    }
}

impl Default for CompositeSearchBuilder {
    fn default() -> Self {
        Self::new()
    }
}

/// Frozen composite search index combining name, type, and dependency search.
///
/// Implements [`MathverseSearch`]. Built via [`CompositeSearchBuilder`] or the
/// convenience methods [`CompositeSearch::new`] (empty) and
/// [`CompositeSearch::add_constant`] / [`CompositeSearch::add_dependency`]
/// followed by [`CompositeSearch::rebuild`].
pub struct CompositeSearch {
    name_index: NameIndex,
    type_index: TypeIndex,
    dep_graph: DependencyGraph,
}

impl CompositeSearch {
    /// Create a new mutable builder.
    ///
    /// This is a convenience wrapper that returns a builder. For the
    /// common pattern of building inline in tests, use the builder directly.
    #[must_use]
    pub fn builder() -> CompositeSearchBuilder {
        CompositeSearchBuilder::new()
    }
}

impl MathverseSearch for CompositeSearch {
    fn search_by_name(&self, name: &str) -> Vec<u32> {
        self.name_index.search_exact(name)
    }

    fn search_by_name_prefix(&self, prefix: &str) -> Vec<u32> {
        self.name_index
            .search_prefix(prefix)
            .iter()
            .map(|e| e.constant_idx)
            .collect()
    }

    fn search_by_type(&self, head: &HeadSymbol) -> Vec<u32> {
        self.type_index.search_by_head(head)
    }

    fn search_dependencies(&self, constant_idx: u32) -> Vec<u32> {
        self.dep_graph.direct_deps(constant_idx).to_vec()
    }

    fn search_transitive_dependencies(&self, constant_idx: u32) -> Vec<u32> {
        self.dep_graph.transitive_deps(constant_idx)
    }

    fn search_reverse_dependencies(&self, constant_idx: u32) -> Vec<u32> {
        self.dep_graph.direct_rdeps(constant_idx).to_vec()
    }
}

// ─── Index entry ─────────────────────────────────────────────────────────

/// A searchable entry in the retrieval index.
#[derive(Clone, Debug)]
pub struct IndexEntry {
    /// Constant index in the Mathverse shard.
    pub constant_idx: u32,
    /// Fully-qualified name.
    pub name: String,
    /// Source system.
    pub source: SourceSystem,
    /// Trust level.
    pub trust_level: TrustLevel,
    /// Axiom profile.
    pub axiom_profile: AxiomProfile,
    /// Structural fingerprint for discrimination tree matching.
    pub fingerprint: Vec<u8>,
}

// ─── Bloom filter ────────────────────────────────────────────────────────

/// Simple Bloom filter for fast negative lookups.
pub struct BloomFilter {
    bits: Vec<u64>,
    num_bits: usize,
    num_hashes: u32,
}

impl BloomFilter {
    /// Create a new Bloom filter with the given capacity and false-positive rate.
    #[must_use]
    pub fn new(expected_items: usize, fp_rate: f64) -> Self {
        let num_bits = optimal_bits(expected_items, fp_rate);
        let num_hashes = optimal_hashes(num_bits, expected_items);
        let words = num_bits.div_ceil(64);
        Self {
            bits: vec![0; words],
            num_bits,
            num_hashes,
        }
    }

    /// Insert a key into the filter.
    pub fn insert(&mut self, key: &[u8]) {
        for i in 0..self.num_hashes {
            let h = hash_with_seed(key, i) % self.num_bits;
            self.bits[h / 64] |= 1 << (h % 64);
        }
    }

    /// Check if a key might be in the filter.
    #[must_use]
    pub fn might_contain(&self, key: &[u8]) -> bool {
        for i in 0..self.num_hashes {
            let h = hash_with_seed(key, i) % self.num_bits;
            if self.bits[h / 64] & (1 << (h % 64)) == 0 {
                return false;
            }
        }
        true
    }

    /// Number of bits set.
    #[must_use]
    pub fn popcount(&self) -> u64 {
        self.bits.iter().map(|w| w.count_ones() as u64).sum()
    }
}

fn optimal_bits(n: usize, fp: f64) -> usize {
    let m = -(n as f64 * fp.ln()) / (2.0_f64.ln().powi(2));
    (m.ceil() as usize).max(64)
}

fn optimal_hashes(m: usize, n: usize) -> u32 {
    let k = (m as f64 / n as f64) * 2.0_f64.ln();
    (k.ceil() as u32).clamp(1, 16)
}

fn hash_with_seed(key: &[u8], seed: u32) -> usize {
    // FNV-1a with seed mixing.
    let mut h: u64 = 0xcbf29ce484222325 ^ (seed as u64);
    for &b in key {
        h ^= b as u64;
        h = h.wrapping_mul(0x100000001b3);
    }
    h as usize
}

// ─── Discrimination tree ─────────────────────────────────────────────────

/// Node in a discrimination tree for structural expression matching.
#[derive(Clone, Debug, Default)]
pub struct DiscTreeNode {
    /// Children keyed by expression head symbol.
    children: HashMap<DiscTreeKey, DiscTreeNode>,
    /// Entries that match this path.
    entries: Vec<u32>,
}

/// Key for discrimination tree branching.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum DiscTreeKey {
    /// Constant with name index.
    Const(u32),
    /// Bound variable.
    BVar(u32),
    /// Application head.
    App,
    /// Lambda abstraction.
    Lambda,
    /// Pi/forall.
    Pi,
    /// Sort/Type.
    Sort,
    /// Wildcard (matches anything).
    Star,
}

impl DiscTreeNode {
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Insert an entry at the path given by `keys`.
    pub fn insert(&mut self, keys: &[DiscTreeKey], entry: u32) {
        if keys.is_empty() {
            self.entries.push(entry);
            return;
        }
        self.children
            .entry(keys[0].clone())
            .or_default()
            .insert(&keys[1..], entry);
    }

    /// Look up entries matching a path.
    #[must_use]
    pub fn lookup(&self, keys: &[DiscTreeKey]) -> Vec<u32> {
        if keys.is_empty() {
            return self.entries.clone();
        }

        let mut results = Vec::new();

        // Exact match.
        if let Some(child) = self.children.get(&keys[0]) {
            results.extend(child.lookup(&keys[1..]));
        }

        // Wildcard match: `Star` children match anything.
        if let Some(star_child) = self.children.get(&DiscTreeKey::Star) {
            results.extend(star_child.lookup(&keys[1..]));
        }

        // If query is Star, match all children.
        if keys[0] == DiscTreeKey::Star {
            for child in self.children.values() {
                results.extend(child.lookup(&keys[1..]));
            }
        }

        results
    }

    /// Number of entries stored (recursively).
    #[must_use]
    pub fn entry_count(&self) -> usize {
        let mut count = self.entries.len();
        for child in self.children.values() {
            count += child.entry_count();
        }
        count
    }
}

// ─── Retrieval index ─────────────────────────────────────────────────────

/// Main retrieval index combining name lookup, Bloom filter, and disc tree.
pub struct RetrievalIndex {
    /// Name → constant index.
    name_index: HashMap<String, Vec<u32>>,
    /// Source system → constant indices.
    source_index: HashMap<SourceSystem, Vec<u32>>,
    /// Bloom filter on names.
    bloom: BloomFilter,
    /// Discrimination tree for structural matching.
    disc_tree: DiscTreeNode,
    /// All entries.
    entries: Vec<IndexEntry>,
}

impl RetrievalIndex {
    /// Create a new empty index.
    #[must_use]
    pub fn new(expected_size: usize) -> Self {
        Self {
            name_index: HashMap::new(),
            source_index: HashMap::new(),
            bloom: BloomFilter::new(expected_size.max(1), 0.01),
            disc_tree: DiscTreeNode::new(),
            entries: Vec::new(),
        }
    }

    /// Add an entry to the index.
    pub fn add(&mut self, entry: IndexEntry) {
        let idx = self.entries.len() as u32;

        // Name index.
        self.name_index
            .entry(entry.name.clone())
            .or_default()
            .push(idx);

        // Bloom filter.
        self.bloom.insert(entry.name.as_bytes());

        // Source index.
        self.source_index.entry(entry.source).or_default().push(idx);

        self.entries.push(entry);
    }

    /// Exact name lookup.
    #[must_use]
    pub fn lookup_by_name(&self, name: &str) -> Vec<&IndexEntry> {
        if !self.bloom.might_contain(name.as_bytes()) {
            return Vec::new();
        }
        self.name_index
            .get(name)
            .map(|indices| indices.iter().map(|&i| &self.entries[i as usize]).collect())
            .unwrap_or_default()
    }

    /// Exact name lookup filtered through Mathverse trust enforcement.
    #[must_use]
    pub fn lookup_by_name_with_policy(&self, name: &str, policy: &TrustPolicy) -> Vec<&IndexEntry> {
        let enforcer = TrustEnforcer::new(policy.clone());
        self.lookup_by_name(name)
            .into_iter()
            .filter(|entry| entry_visible_under_enforcer(entry, &enforcer))
            .collect()
    }

    /// Prefix name search.
    #[must_use]
    pub fn search_by_prefix(&self, prefix: &str) -> Vec<&IndexEntry> {
        let mut results = Vec::new();
        for (name, indices) in &self.name_index {
            if name.starts_with(prefix) {
                for &i in indices {
                    results.push(&self.entries[i as usize]);
                }
            }
        }
        results
    }

    /// Prefix name search filtered through Mathverse trust enforcement.
    #[must_use]
    pub fn search_by_prefix_with_policy(
        &self,
        prefix: &str,
        policy: &TrustPolicy,
    ) -> Vec<&IndexEntry> {
        let enforcer = TrustEnforcer::new(policy.clone());
        self.search_by_prefix(prefix)
            .into_iter()
            .filter(|entry| entry_visible_under_enforcer(entry, &enforcer))
            .collect()
    }

    /// Return all entries visible under the given trust policy.
    #[must_use]
    pub fn trusted_entries(&self, policy: &TrustPolicy) -> Vec<&IndexEntry> {
        let enforcer = TrustEnforcer::new(policy.clone());
        self.entries
            .iter()
            .filter(|entry| entry_visible_under_enforcer(entry, &enforcer))
            .collect()
    }

    /// Filter by source system.
    #[must_use]
    pub fn filter_by_source(&self, source: &SourceSystem) -> Vec<&IndexEntry> {
        self.source_index
            .get(source)
            .map(|indices| indices.iter().map(|&i| &self.entries[i as usize]).collect())
            .unwrap_or_default()
    }

    /// Filter by trust level.
    #[must_use]
    pub fn filter_by_trust(&self, level: TrustLevel) -> Vec<&IndexEntry> {
        self.entries
            .iter()
            .filter(|e| e.trust_level == level)
            .collect()
    }

    /// Total number of indexed entries.
    #[must_use]
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    /// Whether the index is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// Number of distinct names.
    #[must_use]
    pub fn name_count(&self) -> usize {
        self.name_index.len()
    }

    /// Number of distinct source systems.
    #[must_use]
    pub fn source_count(&self) -> usize {
        self.source_index.len()
    }
}

fn entry_visible_under_enforcer(entry: &IndexEntry, enforcer: &TrustEnforcer) -> bool {
    enforcer
        .check_visible(entry.constant_idx, entry.axiom_profile, entry.trust_level)
        .is_ok()
}

// Existing tests for BloomFilter, DiscTree, RetrievalIndex are in tests.rs.
