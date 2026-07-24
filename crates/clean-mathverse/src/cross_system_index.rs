// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Cross-system name-based matching over imported constants.
//!
//! This module builds an inverted index from normalized names to the original
//! constants that produced them. The normalization comes from
//! [`crate::equivalence::normalize_name`], allowing lightweight detection of
//! likely cross-system equivalents by grouping constants whose names collapse
//! to the same canonical form across different source systems.

use hashbrown::HashMap;

use crate::equivalence::normalize_name;
use crate::types::{ConstantIdx, SourceSystem};

/// A single constant reference stored in the cross-system name index.
#[derive(Debug, Clone, PartialEq)]
pub struct ConstantRef {
    pub source: SourceSystem,
    pub shard_id: u32,
    pub constant_id: ConstantIdx,
    pub original_name: String,
}

/// A canonical-name match spanning one or more source systems.
#[derive(Debug, Clone, PartialEq)]
pub struct EquivalenceMatch {
    pub canonical_name: String,
    pub refs: Vec<ConstantRef>,
    pub system_count: usize,
    pub confidence: f32,
}

/// Shared-name overlap between a pair of source systems.
#[derive(Debug, Clone, PartialEq)]
pub struct SystemOverlap {
    pub system_a: SourceSystem,
    pub system_b: SourceSystem,
    pub shared_names: usize,
}

/// Aggregate report for cross-system name matching coverage.
#[derive(Debug, Clone, PartialEq)]
pub struct CrossSystemReport {
    pub total_constants: usize,
    pub total_systems: usize,
    pub multi_system_count: usize,
    pub top_cross_referenced: Vec<EquivalenceMatch>,
    pub overlap_matrix: Vec<SystemOverlap>,
}

/// In-memory inverted index keyed by cross-system canonical name.
#[derive(Debug, Clone, Default)]
pub struct CrossSystemIndex {
    inverted_index: HashMap<String, Vec<ConstantRef>>,
    system_counts: HashMap<SourceSystem, usize>,
}

impl CrossSystemIndex {
    /// Create an empty cross-system index.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Add a constant to the inverted name index.
    pub fn index_constant(
        &mut self,
        name: &str,
        source: SourceSystem,
        shard_id: u32,
        constant_id: ConstantIdx,
    ) {
        let canonical_name = normalize_name(name, source);
        let constant_ref = ConstantRef {
            source,
            shard_id,
            constant_id,
            original_name: name.to_owned(),
        };

        self.inverted_index
            .entry(canonical_name)
            .or_default()
            .push(constant_ref);
        *self.system_counts.entry(source).or_insert(0) += 1;
    }

    /// Total number of constants indexed across all systems.
    #[must_use]
    pub fn total_indexed(&self) -> usize {
        self.system_counts.values().sum()
    }

    /// Find canonical names that appear in at least `min_systems` systems.
    #[must_use]
    pub fn find_matches(&self, min_systems: usize) -> Vec<EquivalenceMatch> {
        let total_systems = self.system_counts.len();
        let mut matches = Vec::new();

        for (canonical_name, refs) in &self.inverted_index {
            let systems = distinct_systems(refs);
            let system_count = systems.len();
            if system_count < min_systems {
                continue;
            }

            let confidence = if total_systems == 0 {
                0.0
            } else {
                system_count as f32 / total_systems as f32
            };

            matches.push(EquivalenceMatch {
                canonical_name: canonical_name.clone(),
                refs: refs.clone(),
                system_count,
                confidence,
            });
        }

        matches.sort_by(|left, right| {
            right
                .system_count
                .cmp(&left.system_count)
                .then_with(|| left.canonical_name.cmp(&right.canonical_name))
        });
        matches
    }

    /// Build a summary report over the current index contents.
    #[must_use]
    pub fn generate_report(&self, top_n: usize) -> CrossSystemReport {
        let all_matches = self.find_matches(2);
        CrossSystemReport {
            total_constants: self.total_indexed(),
            total_systems: self.system_counts.len(),
            multi_system_count: all_matches.len(),
            top_cross_referenced: all_matches.into_iter().take(top_n).collect(),
            overlap_matrix: self.overlap_matrix(),
        }
    }

    /// Count shared canonical names for every pair of indexed systems.
    #[must_use]
    pub fn overlap_matrix(&self) -> Vec<SystemOverlap> {
        let systems = sorted_systems(self.system_counts.keys().copied().collect());
        let mut pair_counts: HashMap<(SourceSystem, SourceSystem), usize> = HashMap::new();

        for refs in self.inverted_index.values() {
            let present_systems = distinct_systems(refs);
            for (index, system_a) in present_systems.iter().enumerate() {
                for system_b in &present_systems[index + 1..] {
                    *pair_counts.entry((*system_a, *system_b)).or_insert(0) += 1;
                }
            }
        }

        let mut overlaps = Vec::new();
        for (index, system_a) in systems.iter().enumerate() {
            for system_b in &systems[index + 1..] {
                overlaps.push(SystemOverlap {
                    system_a: *system_a,
                    system_b: *system_b,
                    shared_names: *pair_counts.get(&(*system_a, *system_b)).unwrap_or(&0),
                });
            }
        }
        overlaps
    }
}

fn distinct_systems(refs: &[ConstantRef]) -> Vec<SourceSystem> {
    let mut systems: Vec<SourceSystem> = refs
        .iter()
        .map(|constant_ref| constant_ref.source)
        .collect();
    systems.sort_by_key(|system| *system as u8);
    systems.dedup();
    systems
}

fn sorted_systems(mut systems: Vec<SourceSystem>) -> Vec<SourceSystem> {
    systems.sort_by_key(|system| *system as u8);
    systems
}

#[cfg(test)]
mod tests {
    use super::{CrossSystemIndex, SystemOverlap};
    use crate::equivalence::normalize_name;
    use crate::types::SourceSystem;

    #[test]
    fn test_index_and_find_matches() {
        let mut index = CrossSystemIndex::new();
        index.index_constant("Nat.add_comm", SourceSystem::Lean4, 0, 1);
        index.index_constant("PeanoNat.Nat.add_comm", SourceSystem::Coq, 1, 2);
        index.index_constant("Mathlib.Nat.add_comm", SourceSystem::Lean4, 2, 3);

        assert_eq!(index.total_indexed(), 3);

        let matches = index.find_matches(2);
        assert_eq!(matches.len(), 1);

        let matched = &matches[0];
        assert_eq!(matched.canonical_name, "nat_add_comm");
        assert_eq!(matched.system_count, 2);
        assert_eq!(matched.refs.len(), 3);
        assert!((matched.confidence - 1.0).abs() < f32::EPSILON);
        assert_eq!(
            matched
                .refs
                .iter()
                .filter(|constant_ref| constant_ref.source == SourceSystem::Lean4)
                .count(),
            2
        );
        assert_eq!(
            matched
                .refs
                .iter()
                .filter(|constant_ref| constant_ref.source == SourceSystem::Coq)
                .count(),
            1
        );
    }

    #[test]
    fn test_no_matches_single_system() {
        let mut index = CrossSystemIndex::new();
        index.index_constant("Nat.add_comm", SourceSystem::Lean4, 0, 1);
        index.index_constant("Mathlib.Nat.add_comm", SourceSystem::Lean4, 1, 2);
        index.index_constant("Nat.mul_comm", SourceSystem::Lean4, 2, 3);

        assert!(index.find_matches(2).is_empty());
    }

    #[test]
    fn test_overlap_matrix() {
        let mut index = CrossSystemIndex::new();
        index.index_constant("add_comm", SourceSystem::Lean4, 0, 1);
        index.index_constant("add_comm", SourceSystem::Coq, 1, 2);
        index.index_constant("mul_comm", SourceSystem::Lean4, 2, 3);
        index.index_constant("Theory.mul_comm", SourceSystem::Isabelle, 3, 4);
        index.index_constant("assoc", SourceSystem::Lean4, 4, 5);
        index.index_constant("assoc", SourceSystem::Coq, 5, 6);
        index.index_constant("Theory.assoc", SourceSystem::Isabelle, 6, 7);

        let overlaps = index.overlap_matrix();
        assert_eq!(overlaps.len(), 3);
        assert_eq!(
            lookup_overlap(&overlaps, SourceSystem::Lean4, SourceSystem::Coq),
            2
        );
        assert_eq!(
            lookup_overlap(&overlaps, SourceSystem::Lean4, SourceSystem::Isabelle),
            2
        );
        assert_eq!(
            lookup_overlap(&overlaps, SourceSystem::Coq, SourceSystem::Isabelle),
            1
        );
    }

    #[test]
    fn test_generate_report() {
        let mut index = CrossSystemIndex::new();
        index.index_constant("add_comm", SourceSystem::Lean4, 0, 1);
        index.index_constant("add_comm", SourceSystem::Coq, 1, 2);
        index.index_constant("Theory.add_comm", SourceSystem::Isabelle, 2, 3);
        index.index_constant("mul_comm", SourceSystem::Lean4, 3, 4);
        index.index_constant("mul_comm", SourceSystem::Coq, 4, 5);
        index.index_constant("only_lean", SourceSystem::Lean4, 5, 6);

        let report = index.generate_report(1);
        assert_eq!(report.total_constants, 6);
        assert_eq!(report.total_systems, 3);
        assert_eq!(report.multi_system_count, 2);
        assert_eq!(report.top_cross_referenced.len(), 1);
        assert_eq!(report.overlap_matrix.len(), 3);

        let top_match = &report.top_cross_referenced[0];
        assert_eq!(top_match.canonical_name, "add_comm");
        assert_eq!(top_match.system_count, 3);
        assert_eq!(top_match.refs.len(), 3);
        assert!((top_match.confidence - 1.0).abs() < f32::EPSILON);
        assert_eq!(
            lookup_overlap(
                &report.overlap_matrix,
                SourceSystem::Lean4,
                SourceSystem::Coq
            ),
            2
        );
        assert_eq!(
            lookup_overlap(
                &report.overlap_matrix,
                SourceSystem::Lean4,
                SourceSystem::Isabelle
            ),
            1
        );
        assert_eq!(
            lookup_overlap(
                &report.overlap_matrix,
                SourceSystem::Coq,
                SourceSystem::Isabelle
            ),
            1
        );
    }

    #[test]
    fn test_normalize_integration() {
        let lean_name = "Mathlib.Nat.add_comm";
        let coq_name = "PeanoNat.Nat.add_comm";

        let lean_canonical = normalize_name(lean_name, SourceSystem::Lean4);
        let coq_canonical = normalize_name(coq_name, SourceSystem::Coq);
        assert_eq!(lean_canonical, "nat_add_comm");
        assert_eq!(lean_canonical, coq_canonical);

        let mut index = CrossSystemIndex::new();
        index.index_constant(lean_name, SourceSystem::Lean4, 7, 8);
        index.index_constant(coq_name, SourceSystem::Coq, 9, 10);

        let matches = index.find_matches(2);
        assert_eq!(matches.len(), 1);
        assert_eq!(matches[0].canonical_name, "nat_add_comm");
        assert_eq!(matches[0].refs.len(), 2);
        assert_eq!(matches[0].refs[0].original_name, lean_name);
        assert_eq!(matches[0].refs[1].original_name, coq_name);
    }

    fn lookup_overlap(
        overlaps: &[SystemOverlap],
        system_a: SourceSystem,
        system_b: SourceSystem,
    ) -> usize {
        overlaps
            .iter()
            .find(|overlap| overlap.system_a == system_a && overlap.system_b == system_b)
            .unwrap()
            .shared_names
    }
}
