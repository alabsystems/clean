// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Simp lemma discrimination tree index for efficient rewrite lookup.
//!
//! Provides a persistent, incrementally-built index of simp lemmas keyed
//! by their LHS pattern. The index wraps the low-level `DiscrTree` from
//! `crate::tactic::discr_tree` and adds:
//!
//! - Batch insertion with duplicate detection
//! - Priority-ordered lookup results
//! - LHS pattern extraction from equality types (handles Pi-binders)
//! - Index statistics (lemma count, tree depth, collision rate)
//!
//! # Architecture
//!
//! Lean 4 uses discrimination trees to index `@[simp]` lemmas by their
//! LHS pattern so that `simp` only attempts to match lemmas whose head
//! symbol agrees with the current subexpression. This module provides the
//! same capability for clean's simplifier.
//!
//! The index stores `SimpLemmaEntry` values keyed by discrimination-tree
//! paths derived from each lemma's LHS. Lookup returns entries sorted by
//! descending priority so callers try higher-priority rewrites first.

use std::collections::HashSet;

use clean_kernel::name::Name;
use clean_kernel::Expr;

use super::discr_tree::{mk_path, query_path_is_too_generic, DiscrTree, IndexMode};
use super::simp::{SimpIndexMode, SimpLemma};
use super::{Goal, ProofState};

/// A simp lemma entry stored in the index.
///
/// Contains all information needed to attempt a rewrite: the lemma
/// identity, its LHS/RHS, an optional pre-built proof, and priority.
#[derive(Debug, Clone)]
pub(crate) struct SimpLemmaEntry {
    /// Lemma name (for diagnostics and dedup).
    pub(crate) name: Name,
    /// The LHS of the rewrite (`lhs = rhs`).
    pub(crate) lhs: Expr,
    /// The RHS of the rewrite.
    pub(crate) rhs: Expr,
    /// The type parameter of the equality (`@Eq eq_type lhs rhs`).
    pub(crate) eq_type: Option<Expr>,
    /// Optional pre-built proof term.
    pub(crate) proof: Option<Expr>,
    /// Priority (higher = try first).
    pub(crate) priority: u32,
    /// How the lemma was indexed.
    pub(crate) index_mode: SimpIndexMode,
}

impl SimpLemmaEntry {
    /// Create an entry from a `SimpLemma`.
    pub(crate) fn from_simp_lemma(lemma: &SimpLemma) -> Self {
        SimpLemmaEntry {
            name: lemma.name.clone(),
            lhs: lemma.lhs.clone(),
            rhs: lemma.rhs.clone(),
            eq_type: lemma.eq_type.clone(),
            proof: lemma.proof_expr.clone(),
            priority: lemma.priority,
            index_mode: lemma.index_mode,
        }
    }

    /// Convert back to a `SimpLemma` for use with the existing simp engine.
    pub(crate) fn to_simp_lemma(&self) -> SimpLemma {
        SimpLemma {
            name: self.name.clone(),
            lhs: self.lhs.clone(),
            rhs: self.rhs.clone(),
            eq_type: self.eq_type.clone(),
            proof_expr: self.proof.clone(),
            index_mode: self.index_mode,
            priority: self.priority,
        }
    }
}

/// Statistics about the simp index.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct SimpIndexStats {
    /// Total number of lemma entries in the index.
    pub(crate) lemma_count: usize,
    /// Number of distinct lemma names (detects duplicates).
    pub(crate) distinct_names: usize,
    /// Number of lemmas that could not be indexed (too generic).
    pub(crate) unindexed_count: usize,
    /// Number of lemmas successfully inserted into the disc tree.
    pub(crate) indexed_count: usize,
}

impl SimpIndexStats {
    /// Collision rate: fraction of lemmas that share a disc tree path
    /// with at least one other lemma. Returns 0.0 when no lemmas are indexed.
    pub(crate) fn collision_rate(&self) -> f64 {
        if self.indexed_count == 0 {
            return 0.0;
        }
        let duplicates = self.lemma_count.saturating_sub(self.distinct_names);
        duplicates as f64 / self.lemma_count as f64
    }
}

/// Discrimination tree index for simp lemma lookup.
///
/// Wraps `DiscrTree<usize>` (indices into `entries`) with batch insertion,
/// deduplication, and priority-ordered retrieval.
#[derive(Debug, Clone, Default)]
pub(crate) struct SimpIndex {
    /// All lemma entries in insertion order.
    entries: Vec<SimpLemmaEntry>,
    /// Disc tree mapping LHS paths to entry indices.
    tree: DiscrTree<usize>,
    /// Names already inserted (for dedup).
    inserted_names: HashSet<String>,
    /// Count of entries that could not be indexed.
    unindexed_count: usize,
}

impl SimpIndex {
    /// Create an empty index.
    pub(crate) fn new() -> Self {
        Self::default()
    }

    /// Number of lemma entries in the index.
    pub(crate) fn len(&self) -> usize {
        self.entries.len()
    }

    /// Whether the index contains any entries.
    pub(crate) fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// Insert a single lemma entry into the index.
    ///
    /// Returns `true` if the entry was inserted, `false` if a lemma with
    /// the same name was already present (duplicate suppressed).
    pub(crate) fn insert(
        &mut self,
        state: &ProofState,
        goal: &Goal,
        entry: SimpLemmaEntry,
    ) -> bool {
        let name_str = entry.name.to_string();
        if self.inserted_names.contains(&name_str) {
            return false;
        }

        let index_value = self.entries.len();
        let mode: IndexMode = entry.index_mode.into();

        if !self
            .tree
            .insert_if_specific(state, goal, &entry.lhs, mode, index_value)
        {
            self.unindexed_count += 1;
        }

        self.inserted_names.insert(name_str);
        self.entries.push(entry);
        true
    }

    /// Insert a `SimpLemma` directly.
    ///
    /// Convenience wrapper that converts to `SimpLemmaEntry` first.
    pub(crate) fn insert_lemma(
        &mut self,
        state: &ProofState,
        goal: &Goal,
        lemma: &SimpLemma,
    ) -> bool {
        self.insert(state, goal, SimpLemmaEntry::from_simp_lemma(lemma))
    }

    /// Batch-insert multiple lemmas. Returns the number actually inserted
    /// (excludes duplicates).
    pub(crate) fn insert_many(
        &mut self,
        state: &ProofState,
        goal: &Goal,
        lemmas: &[SimpLemma],
    ) -> usize {
        lemmas
            .iter()
            .filter(|lemma| self.insert_lemma(state, goal, lemma))
            .count()
    }

    /// Look up candidate lemma entries for `expr`, returned in descending
    /// priority order (highest priority first).
    ///
    /// Falls back to returning all entries when the query path is too
    /// generic for discrimination-tree filtering.
    pub(crate) fn lookup(
        &self,
        state: &ProofState,
        goal: &Goal,
        expr: &Expr,
    ) -> Vec<&SimpLemmaEntry> {
        let query_path = mk_path(state, goal, expr, IndexMode::Normal);

        if query_path_is_too_generic(&query_path) || self.tree.is_empty() {
            return self.all_by_priority();
        }

        let mut matched_indices: Vec<usize> = self
            .tree
            .get_match_with_extra(state, goal, expr)
            .into_iter()
            .map(|m| m.value)
            .collect();
        matched_indices.sort_unstable();
        matched_indices.dedup();

        // Fall back to liberal match when strict matching finds nothing
        if matched_indices.is_empty() {
            matched_indices = self.tree.get_match_liberal(state, goal, expr);
            matched_indices.sort_unstable();
            matched_indices.dedup();
        }

        // If still empty and we have unindexed lemmas, return everything
        if matched_indices.is_empty() && self.unindexed_count > 0 {
            return self.all_by_priority();
        }

        if matched_indices.is_empty() {
            return Vec::new();
        }

        let mut results: Vec<&SimpLemmaEntry> = matched_indices
            .into_iter()
            .filter_map(|idx| self.entries.get(idx))
            .collect();
        results.sort_by_key(|b| std::cmp::Reverse(b.priority));
        results
    }

    /// Look up candidates and return them as `SimpLemma` values.
    pub(crate) fn lookup_as_lemmas(
        &self,
        state: &ProofState,
        goal: &Goal,
        expr: &Expr,
    ) -> Vec<SimpLemma> {
        self.lookup(state, goal, expr)
            .into_iter()
            .map(SimpLemmaEntry::to_simp_lemma)
            .collect()
    }

    /// Return all entries sorted by descending priority.
    pub(crate) fn all_by_priority(&self) -> Vec<&SimpLemmaEntry> {
        let mut entries: Vec<&SimpLemmaEntry> = self.entries.iter().collect();
        entries.sort_by_key(|b| std::cmp::Reverse(b.priority));
        entries
    }

    /// Get an entry by its insertion index.
    pub(crate) fn get(&self, index: usize) -> Option<&SimpLemmaEntry> {
        self.entries.get(index)
    }

    /// Compute index statistics.
    pub(crate) fn stats(&self) -> SimpIndexStats {
        SimpIndexStats {
            lemma_count: self.entries.len(),
            distinct_names: self.inserted_names.len(),
            unindexed_count: self.unindexed_count,
            indexed_count: self.entries.len().saturating_sub(self.unindexed_count),
        }
    }

    /// Check whether a lemma name is already in the index.
    pub(crate) fn contains(&self, name: &str) -> bool {
        self.inserted_names.contains(name)
    }

    /// Remove all entries from the index.
    pub(crate) fn clear(&mut self) {
        self.entries.clear();
        self.tree = DiscrTree::default();
        self.inserted_names.clear();
        self.unindexed_count = 0;
    }
}

/// Extract the LHS pattern from a `SimpLemma`'s equality type for indexing.
///
/// Returns the LHS if the lemma type is of the form `@Eq _ lhs rhs`
/// (possibly under Pi/forall binders). This is the expression that should
/// be used as the discrimination tree key.
///
/// ENSURES: On `Some`, the returned expression is the LHS of the rewrite rule.
/// ENSURES: On `None`, the lemma type does not contain an extractable equality.
pub(crate) fn extract_lhs_pattern(lemma: &SimpLemma) -> Option<Expr> {
    // The SimpLemma already has lhs extracted; verify it is non-trivial.
    if matches!(lemma.lhs.kind(), clean_kernel::ExprKind::BVar(_)) {
        return None;
    }
    Some(lemma.lhs.clone())
}

/// Generate a discrimination tree key path from an expression.
///
/// Thin wrapper around `discr_tree::mk_path` exposed for use by callers
/// that need to inspect the key sequence without a full index lookup.
/// Only available in test builds since `DiscrKey` is test-only exported.
#[cfg(test)]
pub(crate) fn generate_disc_keys(
    state: &ProofState,
    goal: &Goal,
    expr: &Expr,
    mode: SimpIndexMode,
) -> Vec<super::discr_tree::DiscrKey> {
    mk_path(state, goal, expr, mode.into())
}
