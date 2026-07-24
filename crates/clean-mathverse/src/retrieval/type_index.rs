// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Type-directed search by head symbol.
//!
//! Indexes constants by the head symbol of their type expression so that
//! queries like "find all theorems about `Nat`" or "find all functions
//! returning `List`" are fast. This is a simplified discrimination tree
//! that indexes only the outermost head symbol rather than the full
//! expression structure.

use std::collections::HashMap;

use serde::{Deserialize, Serialize};

/// A head symbol extracted from a type expression.
///
/// For a type like `Nat -> Nat -> Nat`, the head symbol is `Nat` (the
/// return type). For `forall (n : Nat), P n`, the head is the head of `P n`.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum HeadSymbol {
    /// Named constant (e.g., `Nat`, `List`, `Eq`).
    Const(String),
    /// Sort/Prop/Type.
    Sort,
    /// Pi/forall (the type is itself a function type).
    Pi,
    /// Unknown or complex head.
    Other,
}

/// Entry in the type index.
#[derive(Clone, Debug)]
pub struct TypeIndexEntry {
    pub constant_idx: u32,
    pub head: HeadSymbol,
}

/// Type-directed index mapping head symbols to constant indices.
///
/// This is a stub for the full discrimination tree. The full version
/// (in `discrim.rs`) indexes the complete expression shape; this module
/// provides fast first-pass filtering by head symbol only.
pub struct TypeIndex {
    /// Head symbol -> list of constant indices.
    index: HashMap<HeadSymbol, Vec<u32>>,
    /// Total entry count.
    count: usize,
}

impl TypeIndex {
    /// Build a type index from entries.
    #[must_use]
    pub fn build(entries: Vec<TypeIndexEntry>) -> Self {
        let count = entries.len();
        let mut index: HashMap<HeadSymbol, Vec<u32>> = HashMap::new();
        for entry in entries {
            index
                .entry(entry.head)
                .or_default()
                .push(entry.constant_idx);
        }
        Self { index, count }
    }

    /// Search by head symbol. Returns all constant indices whose type has
    /// the given head symbol.
    #[must_use]
    pub fn search_by_head(&self, head: &HeadSymbol) -> Vec<u32> {
        self.index.get(head).cloned().unwrap_or_default()
    }

    /// Return all distinct head symbols in the index.
    #[must_use]
    pub fn head_symbols(&self) -> Vec<&HeadSymbol> {
        self.index.keys().collect()
    }

    /// Number of indexed entries.
    #[must_use]
    pub fn len(&self) -> usize {
        self.count
    }

    /// Whether the index is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.count == 0
    }
}

// ---------------------------------------------------------------------------
// Type fingerprinting
// ---------------------------------------------------------------------------

/// A structural fingerprint of a type expression.
///
/// Extracts top-level structural properties for fast approximate matching
/// before full unification. Two types can only unify if their fingerprints
/// are compatible.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct TypeFingerprint {
    /// Arrow/function depth (number of nested Pi types in the head position).
    pub arrow_depth: u16,
    /// Number of universally quantified variables (forall binders).
    pub quantifier_count: u16,
    /// Head symbol of the return type.
    pub return_head: HeadSymbol,
    /// Sorted list of base type names that appear in the type.
    pub base_types: Vec<String>,
}

impl TypeFingerprint {
    /// Create a fingerprint from explicit components.
    #[must_use]
    pub fn new(
        arrow_depth: u16,
        quantifier_count: u16,
        return_head: HeadSymbol,
        base_types: Vec<String>,
    ) -> Self {
        let mut base_types = base_types;
        base_types.sort_unstable();
        base_types.dedup();
        Self {
            arrow_depth,
            quantifier_count,
            return_head,
            base_types,
        }
    }

    /// Compute a similarity score (0.0 to 1.0) between two fingerprints.
    ///
    /// Returns 1.0 for identical fingerprints. Partial scores based on
    /// head match, arrow depth proximity, and base type overlap.
    #[must_use]
    pub fn similarity(&self, other: &Self) -> f64 {
        let mut score = 0.0;
        let total_weight = 4.0;

        // Return head match (highest weight).
        if self.return_head == other.return_head {
            score += 2.0;
        }

        // Arrow depth proximity (max 1.0 contribution).
        let depth_diff = (self.arrow_depth as i32 - other.arrow_depth as i32).unsigned_abs();
        if depth_diff == 0 {
            score += 1.0;
        } else if depth_diff <= 2 {
            score += 0.5;
        }

        // Base type overlap (Jaccard similarity, max 1.0 contribution).
        if !self.base_types.is_empty() || !other.base_types.is_empty() {
            let intersection = self
                .base_types
                .iter()
                .filter(|t| other.base_types.contains(t))
                .count();
            let union = {
                let mut combined = self.base_types.clone();
                for t in &other.base_types {
                    if !combined.contains(t) {
                        combined.push(t.clone());
                    }
                }
                combined.len()
            };
            if union > 0 {
                score += intersection as f64 / union as f64;
            }
        } else {
            // Both empty => compatible.
            score += 1.0;
        }

        score / total_weight
    }
}

// ---------------------------------------------------------------------------
// FingerprintTypeIndex — fingerprint-based type search with relevance
// ---------------------------------------------------------------------------

/// Entry in the fingerprint type index.
#[derive(Clone, Debug)]
pub struct FingerprintEntry {
    pub constant_idx: u32,
    pub name: String,
    pub fingerprint: TypeFingerprint,
}

/// Type-directed search index using fingerprints for relevance-scored results.
///
/// Supports insertion and search with similarity scoring. Results are
/// returned sorted by descending relevance.
pub struct FingerprintTypeIndex {
    entries: Vec<FingerprintEntry>,
    /// Index from return head -> entry indices for fast pre-filtering.
    by_head: HashMap<HeadSymbol, Vec<usize>>,
}

impl FingerprintTypeIndex {
    /// Create a new empty index.
    #[must_use]
    pub fn new() -> Self {
        Self {
            entries: Vec::new(),
            by_head: HashMap::new(),
        }
    }

    /// Insert a constant with its type fingerprint.
    pub fn insert(&mut self, name: &str, constant_idx: u32, fingerprint: TypeFingerprint) {
        let idx = self.entries.len();
        self.by_head
            .entry(fingerprint.return_head.clone())
            .or_default()
            .push(idx);
        self.entries.push(FingerprintEntry {
            constant_idx,
            name: name.to_owned(),
            fingerprint,
        });
    }

    /// Search by type fingerprint, returning matches with relevance scores.
    ///
    /// Returns `(constant_idx, relevance)` pairs sorted by descending relevance.
    /// Only includes results with relevance > `min_relevance`.
    #[must_use]
    pub fn search_by_type(&self, query: &TypeFingerprint, min_relevance: f64) -> Vec<(u32, f64)> {
        let mut results = Vec::new();

        // Fast path: check entries with matching return head first.
        if let Some(indices) = self.by_head.get(&query.return_head) {
            for &idx in indices {
                let entry = &self.entries[idx];
                let score = entry.fingerprint.similarity(query);
                if score >= min_relevance {
                    results.push((entry.constant_idx, score));
                }
            }
        }

        // Also check HeadSymbol::Other (wildcard-like) entries.
        if query.return_head != HeadSymbol::Other {
            if let Some(indices) = self.by_head.get(&HeadSymbol::Other) {
                for &idx in indices {
                    let entry = &self.entries[idx];
                    let score = entry.fingerprint.similarity(query);
                    if score >= min_relevance {
                        results.push((entry.constant_idx, score));
                    }
                }
            }
        }

        results.sort_by(|a, b| b.1.partial_cmp(&a.1).unwrap_or(std::cmp::Ordering::Equal));
        results
    }

    /// Number of indexed entries.
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

impl Default for FingerprintTypeIndex {
    fn default() -> Self {
        Self::new()
    }
}
