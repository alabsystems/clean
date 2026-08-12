// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Cross-system HOL constant unification.
//!
//! When importing constants from multiple HOL-family systems (HOL Light,
//! HOL4, Isabelle), the same mathematical concept often appears under
//! different names or with slightly different type encodings. This module
//! provides a unifier that:
//!
//! 1. Collects constants from all three HOL systems into a single registry.
//! 2. Assigns each constant a unique internal ID.
//! 3. Detects potential equivalences across systems by name matching.
//! 4. Produces a unified constant table for the Mathverse library.

use std::collections::HashMap;

use crate::types::{AxiomProfile, SourceSystem, TrustLevel};

/// Unique identifier for a constant within the cross-system registry.
pub(crate) type ConstantId = u32;

/// Confidence score for a unification match, in [0.0, 1.0].
pub(crate) type MatchScore = f64;

/// A record for a single constant imported from any HOL-family system.
#[derive(Clone, Debug)]
pub(crate) struct HolConstantRecord {
    /// Internal ID within the unifier registry.
    pub(crate) id: ConstantId,
    /// Display name of the constant (e.g., `HOL.True`, `Nat.Suc`).
    pub(crate) name: String,
    /// Which HOL system this constant was imported from.
    pub(crate) source_system: SourceSystem,
    /// String representation of the constant's type expression.
    /// Stored as a string to allow comparison across systems without
    /// requiring `Expr: Eq` (kernel expressions use structural sharing).
    pub(crate) type_repr: String,
    /// Axiom profile for this constant.
    pub(crate) axiom_profile: AxiomProfile,
    /// Trust level assigned to this constant.
    pub(crate) trust_level: TrustLevel,
}

/// Statistics for a single source system's contribution to the unifier.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct SystemContribution {
    /// Number of constants added from this system.
    pub(crate) constant_count: usize,
    /// Number of constants with `CertificateReplayed` trust level.
    pub(crate) proved_count: usize,
    /// Number of constants with `PartiallyAxiomatized` or lower trust.
    pub(crate) axiomatized_count: usize,
}

/// Aggregate statistics across all source systems.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct UnifierStatistics {
    /// Total number of constants in the registry.
    pub(crate) total_constants: usize,
    /// Number of equivalence pairs detected.
    pub(crate) equivalence_count: usize,
    /// Contribution from HOL Light.
    pub(crate) hol_light: SystemContribution,
    /// Contribution from HOL4.
    pub(crate) hol4: SystemContribution,
    /// Contribution from Isabelle.
    pub(crate) isabelle: SystemContribution,
}

/// An equivalence pair: two constants from different systems that represent
/// the same mathematical concept.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct EquivalencePair {
    /// ID of the first constant.
    pub(crate) left: ConstantId,
    /// ID of the second constant.
    pub(crate) right: ConstantId,
    /// The shared base name that triggered the match.
    pub(crate) matched_name: String,
}

/// Tracks alignment of a single constant across HOL Light, HOL4, and Isabelle.
///
/// Each field holds the `ConstantId` from the unifier registry if that system
/// has a matching constant. A fully aligned constant has all three set.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct HolTheoryAlignment {
    /// The canonical base name shared across systems (e.g., `"True"`, `"add"`).
    pub(crate) base_name: String,
    /// Constant ID from HOL Light, if present.
    pub(crate) hol_light_id: Option<ConstantId>,
    /// Constant ID from HOL4, if present.
    pub(crate) hol4_id: Option<ConstantId>,
    /// Constant ID from Isabelle, if present.
    pub(crate) isabelle_id: Option<ConstantId>,
}

impl HolTheoryAlignment {
    /// Create a new alignment record for the given base name.
    #[must_use]
    pub(crate) fn new(base_name: &str) -> Self {
        Self {
            base_name: base_name.to_owned(),
            hol_light_id: None,
            hol4_id: None,
            isabelle_id: None,
        }
    }

    /// Number of systems that have a matching constant (0..=3).
    #[must_use]
    pub(crate) fn system_count(&self) -> usize {
        self.hol_light_id.is_some() as usize
            + self.hol4_id.is_some() as usize
            + self.isabelle_id.is_some() as usize
    }

    /// Whether this alignment has constants from at least two different systems.
    #[must_use]
    pub(crate) fn is_cross_system(&self) -> bool {
        self.system_count() >= 2
    }

    /// Whether all three HOL systems have a matching constant.
    #[must_use]
    pub(crate) fn is_fully_aligned(&self) -> bool {
        self.system_count() == 3
    }

    /// Set the constant ID for the given source system.
    pub(crate) fn set_id(&mut self, system: &SourceSystem, id: ConstantId) {
        match system {
            SourceSystem::HolLight => self.hol_light_id = Some(id),
            SourceSystem::Hol4 => self.hol4_id = Some(id),
            SourceSystem::Isabelle => self.isabelle_id = Some(id),
            _ => {}
        }
    }

    /// Get the constant ID for the given source system.
    #[must_use]
    pub(crate) fn get_id(&self, system: &SourceSystem) -> Option<ConstantId> {
        match system {
            SourceSystem::HolLight => self.hol_light_id,
            SourceSystem::Hol4 => self.hol4_id,
            SourceSystem::Isabelle => self.isabelle_id,
            _ => None,
        }
    }

    /// Collect all present constant IDs as a vector.
    #[must_use]
    pub(crate) fn all_ids(&self) -> Vec<ConstantId> {
        let mut ids = Vec::with_capacity(3);
        if let Some(id) = self.hol_light_id {
            ids.push(id);
        }
        if let Some(id) = self.hol4_id {
            ids.push(id);
        }
        if let Some(id) = self.isabelle_id {
            ids.push(id);
        }
        ids
    }
}

/// Result of attempting to unify a single constant across systems.
#[derive(Clone, Debug)]
pub(crate) struct UnificationResult {
    /// Base name that was unified.
    pub(crate) base_name: String,
    /// Confidence score in [0.0, 1.0] based on name and type matching.
    pub(crate) match_score: MatchScore,
    /// Evidence supporting the alignment (e.g., "exact name match", "type match").
    pub(crate) alignment_evidence: Vec<String>,
    /// Reasons for potential conflict (e.g., "type mismatch", "different arity").
    pub(crate) conflict_reasons: Vec<String>,
    /// The alignment record produced.
    pub(crate) alignment: HolTheoryAlignment,
}

impl UnificationResult {
    /// Whether this unification produced a confident match (score >= 0.5).
    #[must_use]
    pub(crate) fn is_confident(&self) -> bool {
        self.match_score >= 0.5
    }

    /// Whether there are any conflicts in the unification.
    #[must_use]
    pub(crate) fn has_conflicts(&self) -> bool {
        !self.conflict_reasons.is_empty()
    }
}

/// Aggregate statistics about cross-system unification.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct CrossSystemStatistics {
    /// Number of base names that matched across at least two systems.
    pub(crate) matched: usize,
    /// Number of base names that appear in only one system.
    pub(crate) unmatched: usize,
    /// Number of base names where type or arity conflicts were detected.
    pub(crate) conflicts: usize,
    /// Number of base names with multiple candidates in the same system.
    pub(crate) ambiguous: usize,
}

/// An efficient lookup index over constants, keyed by base name and type signature.
///
/// Accelerates cross-system matching by providing O(1) lookup by base name
/// and O(n) lookup by type signature within a name group.
#[derive(Clone, Debug)]
pub(crate) struct HolConstantIndex {
    /// Map from base name to list of (ConstantId, type_repr, SourceSystem).
    by_name: HashMap<String, Vec<ConstantIndexEntry>>,
    /// Map from type_repr to list of ConstantId.
    by_type: HashMap<String, Vec<ConstantId>>,
}

/// A single entry in the constant index.
#[derive(Clone, Debug)]
struct ConstantIndexEntry {
    id: ConstantId,
    type_repr: String,
    source_system: SourceSystem,
}

impl HolConstantIndex {
    /// Create an empty index.
    #[must_use]
    pub(crate) fn new() -> Self {
        Self {
            by_name: HashMap::new(),
            by_type: HashMap::new(),
        }
    }

    /// Build an index from a slice of constant records.
    #[must_use]
    pub(crate) fn from_records(records: &[HolConstantRecord]) -> Self {
        let mut index = Self::new();
        for record in records {
            index.insert(record);
        }
        index
    }

    /// Insert a constant record into the index.
    pub(crate) fn insert(&mut self, record: &HolConstantRecord) {
        let base = base_name(&record.name);
        self.by_name
            .entry(base)
            .or_default()
            .push(ConstantIndexEntry {
                id: record.id,
                type_repr: record.type_repr.clone(),
                source_system: record.source_system,
            });
        self.by_type
            .entry(record.type_repr.clone())
            .or_default()
            .push(record.id);
    }

    /// Look up constants by base name.
    #[must_use]
    pub(crate) fn lookup_by_name(&self, base: &str) -> Vec<ConstantId> {
        self.by_name
            .get(base)
            .map(|entries| entries.iter().map(|e| e.id).collect())
            .unwrap_or_default()
    }

    /// Look up constants by exact type representation.
    #[must_use]
    pub(crate) fn lookup_by_type(&self, type_repr: &str) -> Vec<ConstantId> {
        self.by_type.get(type_repr).cloned().unwrap_or_default()
    }

    /// Look up constants by base name AND type repr (intersection).
    #[must_use]
    pub(crate) fn lookup_by_name_and_type(&self, base: &str, type_repr: &str) -> Vec<ConstantId> {
        self.by_name
            .get(base)
            .map(|entries| {
                entries
                    .iter()
                    .filter(|e| e.type_repr == type_repr)
                    .map(|e| e.id)
                    .collect()
            })
            .unwrap_or_default()
    }

    /// Look up constants by base name, filtering to a specific source system.
    #[must_use]
    pub(crate) fn lookup_by_name_and_system(
        &self,
        base: &str,
        system: &SourceSystem,
    ) -> Vec<ConstantId> {
        self.by_name
            .get(base)
            .map(|entries| {
                entries
                    .iter()
                    .filter(|e| &e.source_system == system)
                    .map(|e| e.id)
                    .collect()
            })
            .unwrap_or_default()
    }

    /// Number of distinct base names in the index.
    #[must_use]
    pub(crate) fn distinct_names(&self) -> usize {
        self.by_name.len()
    }

    /// Number of distinct type representations in the index.
    #[must_use]
    pub(crate) fn distinct_types(&self) -> usize {
        self.by_type.len()
    }

    /// Total number of indexed entries.
    #[must_use]
    pub(crate) fn total_entries(&self) -> usize {
        self.by_name.values().map(|v| v.len()).sum()
    }

    /// All distinct base names in the index.
    #[must_use]
    pub(crate) fn all_base_names(&self) -> Vec<String> {
        let mut names: Vec<String> = self.by_name.keys().cloned().collect();
        names.sort();
        names
    }
}

/// Cross-system HOL constant unifier.
///
/// Collects constants from HOL Light, HOL4, and Isabelle into a single
/// registry. Detects potential equivalences by matching on the base name
/// (the portion after the last `.` in a qualified name).
///
/// # Usage
///
/// ```text
/// let mut unifier = HolUnifier::new();
/// unifier.add_hol_light_constant("HOL.True", "Prop", AxiomProfile::CLASSICAL, TrustLevel::CertificateReplayed);
/// unifier.add_hol4_constant("HOL.True", "Prop", AxiomProfile::CLASSICAL, TrustLevel::CertificateReplayed);
/// let pairs = unifier.find_equivalences();
/// assert_eq!(pairs.len(), 1);
/// ```
pub(crate) struct HolUnifier {
    /// All registered constants, keyed by auto-incrementing ID.
    constants: Vec<HolConstantRecord>,
    /// Next ID to assign.
    next_id: ConstantId,
}

impl HolUnifier {
    /// Create an empty unifier.
    #[must_use]
    pub(crate) fn new() -> Self {
        Self {
            constants: Vec::new(),
            next_id: 0,
        }
    }

    /// Number of constants currently registered.
    #[must_use]
    pub(crate) fn len(&self) -> usize {
        self.constants.len()
    }

    /// Whether the registry is empty.
    #[must_use]
    pub(crate) fn is_empty(&self) -> bool {
        self.constants.is_empty()
    }

    /// Add a constant from HOL Light.
    ///
    /// Returns the assigned constant ID.
    pub(crate) fn add_hol_light_constant(
        &mut self,
        name: &str,
        type_repr: &str,
        axiom_profile: AxiomProfile,
        trust_level: TrustLevel,
    ) -> ConstantId {
        self.add_constant(
            name,
            SourceSystem::HolLight,
            type_repr,
            axiom_profile,
            trust_level,
        )
    }

    /// Add a constant from HOL4.
    ///
    /// Returns the assigned constant ID.
    pub(crate) fn add_hol4_constant(
        &mut self,
        name: &str,
        type_repr: &str,
        axiom_profile: AxiomProfile,
        trust_level: TrustLevel,
    ) -> ConstantId {
        self.add_constant(
            name,
            SourceSystem::Hol4,
            type_repr,
            axiom_profile,
            trust_level,
        )
    }

    /// Add a constant from Isabelle.
    ///
    /// Returns the assigned constant ID.
    pub(crate) fn add_isabelle_constant(
        &mut self,
        name: &str,
        type_repr: &str,
        axiom_profile: AxiomProfile,
        trust_level: TrustLevel,
    ) -> ConstantId {
        self.add_constant(
            name,
            SourceSystem::Isabelle,
            type_repr,
            axiom_profile,
            trust_level,
        )
    }

    /// Internal helper to add a constant from any source system.
    fn add_constant(
        &mut self,
        name: &str,
        source_system: SourceSystem,
        type_repr: &str,
        axiom_profile: AxiomProfile,
        trust_level: TrustLevel,
    ) -> ConstantId {
        let id = self.next_id;
        self.next_id += 1;
        self.constants.push(HolConstantRecord {
            id,
            name: name.to_owned(),
            source_system,
            type_repr: type_repr.to_owned(),
            axiom_profile,
            trust_level,
        });
        id
    }

    /// Get a constant record by ID.
    #[must_use]
    pub(crate) fn get(&self, id: ConstantId) -> Option<&HolConstantRecord> {
        self.constants.iter().find(|c| c.id == id)
    }

    /// Return all registered constants as a slice.
    #[must_use]
    pub(crate) fn unified_constants(&self) -> &[HolConstantRecord] {
        &self.constants
    }

    /// Detect equivalence pairs: constants from *different* source systems
    /// that share the same base name (the segment after the last `.`).
    ///
    /// Returns pairs of constant IDs. Each pair appears exactly once
    /// (no `(a,b)` and `(b,a)` duplicates).
    #[must_use]
    pub(crate) fn find_equivalences(&self) -> Vec<EquivalencePair> {
        // Group constants by base name.
        let mut by_base: HashMap<String, Vec<&HolConstantRecord>> = HashMap::new();
        for record in &self.constants {
            let base = base_name(&record.name);
            by_base.entry(base).or_default().push(record);
        }

        let mut pairs = Vec::new();
        for (base, group) in &by_base {
            // Only consider groups with constants from different systems.
            if group.len() < 2 {
                continue;
            }
            // Generate all cross-system pairs within this base name group.
            for i in 0..group.len() {
                for j in (i + 1)..group.len() {
                    if group[i].source_system != group[j].source_system {
                        pairs.push(EquivalencePair {
                            left: group[i].id,
                            right: group[j].id,
                            matched_name: base.clone(),
                        });
                    }
                }
            }
        }

        // Sort for deterministic output.
        pairs.sort_by(|a, b| a.left.cmp(&b.left).then(a.right.cmp(&b.right)));
        pairs
    }

    /// Compute aggregate statistics across all registered constants.
    #[must_use]
    pub(crate) fn statistics(&self) -> UnifierStatistics {
        let mut stats = UnifierStatistics {
            total_constants: self.constants.len(),
            equivalence_count: self.find_equivalences().len(),
            ..UnifierStatistics::default()
        };

        for record in &self.constants {
            let contrib = match record.source_system {
                SourceSystem::HolLight => &mut stats.hol_light,
                SourceSystem::Hol4 => &mut stats.hol4,
                SourceSystem::Isabelle => &mut stats.isabelle,
                _ => continue,
            };
            contrib.constant_count += 1;
            match record.trust_level {
                TrustLevel::CertificateReplayed | TrustLevel::KernelVerified => {
                    contrib.proved_count += 1;
                }
                _ => {
                    contrib.axiomatized_count += 1;
                }
            }
        }

        stats
    }

    /// Return constants filtered by source system.
    #[must_use]
    pub(crate) fn constants_from(&self, system: &SourceSystem) -> Vec<&HolConstantRecord> {
        self.constants
            .iter()
            .filter(|c| &c.source_system == system)
            .collect()
    }

    /// Find all constants whose name contains the given substring.
    #[must_use]
    pub(crate) fn search_by_name(&self, query: &str) -> Vec<&HolConstantRecord> {
        self.constants
            .iter()
            .filter(|c| c.name.contains(query))
            .collect()
    }

    /// Merge another unifier into this one, re-assigning IDs for the
    /// incoming constants. Returns a mapping from old IDs to new IDs.
    pub(crate) fn merge(&mut self, other: &HolUnifier) -> Vec<(ConstantId, ConstantId)> {
        let mut id_map = Vec::with_capacity(other.constants.len());
        for record in &other.constants {
            let old_id = record.id;
            let new_id = self.add_constant(
                &record.name,
                record.source_system,
                &record.type_repr,
                record.axiom_profile,
                record.trust_level,
            );
            id_map.push((old_id, new_id));
        }
        id_map
    }

    /// Build an efficient lookup index over all registered constants.
    #[must_use]
    pub(crate) fn build_index(&self) -> HolConstantIndex {
        HolConstantIndex::from_records(&self.constants)
    }

    /// Compute theory alignments: for each base name, determine which
    /// systems have a matching constant.
    ///
    /// Returns alignments sorted by base name. Only base names with at
    /// least one constant are included.
    #[must_use]
    pub(crate) fn compute_alignments(&self) -> Vec<HolTheoryAlignment> {
        let mut by_base: HashMap<String, HolTheoryAlignment> = HashMap::new();

        for record in &self.constants {
            let base = base_name(&record.name);
            let alignment = by_base
                .entry(base.clone())
                .or_insert_with(|| HolTheoryAlignment::new(&base));
            alignment.set_id(&record.source_system, record.id);
        }

        let mut alignments: Vec<HolTheoryAlignment> = by_base.into_values().collect();
        alignments.sort_by(|a, b| a.base_name.cmp(&b.base_name));
        alignments
    }

    /// Attempt to unify a single base name across all registered constants.
    ///
    /// Produces a `UnificationResult` with a match score based on:
    /// - Name match (base name equality): 0.5
    /// - Type match (all systems share the same type_repr): +0.5
    /// - Type conflict: score capped at 0.5, conflict recorded
    /// - Ambiguity (multiple constants from same system): score reduced
    #[must_use]
    pub(crate) fn unify_constant(&self, base: &str) -> UnificationResult {
        let mut alignment = HolTheoryAlignment::new(base);
        let mut evidence = Vec::new();
        let mut conflicts = Vec::new();
        let mut types_seen: HashMap<String, Vec<SourceSystem>> = HashMap::new();
        let mut system_counts: HashMap<SourceSystem, usize> = HashMap::new();

        for record in &self.constants {
            let record_base = base_name(&record.name);
            if record_base != base {
                continue;
            }
            alignment.set_id(&record.source_system, record.id);
            types_seen
                .entry(record.type_repr.clone())
                .or_default()
                .push(record.source_system);
            *system_counts.entry(record.source_system).or_insert(0) += 1;
        }

        let sys_count = alignment.system_count();
        if sys_count == 0 {
            return UnificationResult {
                base_name: base.to_owned(),
                match_score: 0.0,
                alignment_evidence: evidence,
                conflict_reasons: vec!["no constants found with this base name".to_owned()],
                alignment,
            };
        }

        // Base score: 0.5 if at least two systems match on name.
        let mut score: f64 = if sys_count >= 2 { 0.5 } else { 0.25 };
        if sys_count >= 2 {
            evidence.push(format!(
                "base name '{}' matched across {} systems",
                base, sys_count
            ));
        }

        // Type consistency check.
        if types_seen.len() == 1 {
            // All constants share the same type representation.
            score += 0.5;
            evidence.push("all systems share identical type representation".to_owned());
        } else if types_seen.len() > 1 {
            // Type mismatch across systems.
            let type_list: Vec<&String> = types_seen.keys().collect();
            conflicts.push(format!(
                "type mismatch: {} distinct type representations: {:?}",
                types_seen.len(),
                type_list
            ));
            // Cap score at 0.5 on type conflict.
            score = score.min(0.5);
        }

        // Ambiguity penalty: if any system has multiple constants with the same base name.
        let ambiguous_systems: Vec<&SourceSystem> = system_counts
            .iter()
            .filter(|(_, &count)| count > 1)
            .map(|(sys, _)| sys)
            .collect();
        if !ambiguous_systems.is_empty() {
            conflicts.push(format!(
                "ambiguous: {} system(s) have multiple constants named '{}'",
                ambiguous_systems.len(),
                base
            ));
            score *= 0.8; // Reduce confidence.
        }

        UnificationResult {
            base_name: base.to_owned(),
            match_score: score,
            alignment_evidence: evidence,
            conflict_reasons: conflicts,
            alignment,
        }
    }

    /// Batch-unify all base names found in the registry.
    ///
    /// Returns one `UnificationResult` per distinct base name, sorted by
    /// base name. This is the primary entry point for bulk cross-system analysis.
    #[must_use]
    pub(crate) fn batch_unify(&self) -> Vec<UnificationResult> {
        let mut base_names: Vec<String> = self
            .constants
            .iter()
            .map(|r| base_name(&r.name))
            .collect::<std::collections::HashSet<_>>()
            .into_iter()
            .collect();
        base_names.sort();

        base_names
            .iter()
            .map(|name| self.unify_constant(name))
            .collect()
    }

    /// Compute cross-system statistics summarizing the unification state.
    #[must_use]
    pub(crate) fn cross_system_statistics(&self) -> CrossSystemStatistics {
        let results = self.batch_unify();
        let mut stats = CrossSystemStatistics::default();

        for result in &results {
            if result.alignment.is_cross_system() {
                stats.matched += 1;
            } else {
                stats.unmatched += 1;
            }
            if result.has_conflicts() {
                stats.conflicts += 1;
            }
        }

        // Count ambiguous base names: those where a single system has
        // multiple constants with the same base name.
        let mut by_base: HashMap<String, HashMap<SourceSystem, usize>> = HashMap::new();
        for record in &self.constants {
            let base = base_name(&record.name);
            *by_base
                .entry(base)
                .or_default()
                .entry(record.source_system)
                .or_insert(0) += 1;
        }
        for system_counts in by_base.values() {
            if system_counts.values().any(|&count| count > 1) {
                stats.ambiguous += 1;
            }
        }

        stats
    }
}

/// Extract the base name from a qualified name.
///
/// `HOL.True` -> `True`, `Nat.Suc` -> `Suc`, `simple` -> `simple`.
fn base_name(name: &str) -> String {
    name.rsplit('.').next().unwrap_or(name).to_owned()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn profile() -> AxiomProfile {
        AxiomProfile::CLASSICAL | AxiomProfile::EXTENSIONALITY | AxiomProfile::HOL_EMBEDDING
    }

    #[test]
    fn test_unifier_empty() {
        let u = HolUnifier::new();
        assert!(u.is_empty());
        assert_eq!(u.len(), 0);
        assert!(u.unified_constants().is_empty());
        assert!(u.find_equivalences().is_empty());
    }

    #[test]
    fn test_add_hol_light_constant() {
        let mut u = HolUnifier::new();
        let id = u.add_hol_light_constant(
            "HOL.True",
            "Prop",
            profile(),
            TrustLevel::CertificateReplayed,
        );
        assert_eq!(id, 0);
        assert_eq!(u.len(), 1);
        let rec = u.get(id).expect("should find constant by ID");
        assert_eq!(rec.name, "HOL.True");
        assert_eq!(rec.source_system, SourceSystem::HolLight);
        assert_eq!(rec.type_repr, "Prop");
    }

    #[test]
    fn test_add_hol4_constant() {
        let mut u = HolUnifier::new();
        let id = u.add_hol4_constant(
            "boolTheory.T",
            "bool",
            profile(),
            TrustLevel::CertificateReplayed,
        );
        assert_eq!(id, 0);
        let rec = u.get(id).expect("should find constant by ID");
        assert_eq!(rec.source_system, SourceSystem::Hol4);
    }

    #[test]
    fn test_add_isabelle_constant() {
        let mut u = HolUnifier::new();
        let id = u.add_isabelle_constant(
            "HOL.True",
            "Prop",
            profile(),
            TrustLevel::CertificateReplayed,
        );
        assert_eq!(id, 0);
        let rec = u.get(id).expect("should find constant by ID");
        assert_eq!(rec.source_system, SourceSystem::Isabelle);
    }

    #[test]
    fn test_auto_increment_ids() {
        let mut u = HolUnifier::new();
        let id0 = u.add_hol_light_constant("c0", "T", profile(), TrustLevel::CertificateReplayed);
        let id1 = u.add_hol4_constant("c1", "T", profile(), TrustLevel::CertificateReplayed);
        let id2 = u.add_isabelle_constant("c2", "T", profile(), TrustLevel::CertificateReplayed);
        assert_eq!(id0, 0);
        assert_eq!(id1, 1);
        assert_eq!(id2, 2);
        assert_eq!(u.len(), 3);
    }

    #[test]
    fn test_find_equivalences_same_base_name_different_systems() {
        let mut u = HolUnifier::new();
        u.add_hol_light_constant(
            "HOL.True",
            "Prop",
            profile(),
            TrustLevel::CertificateReplayed,
        );
        u.add_hol4_constant(
            "boolTheory.True",
            "Prop",
            profile(),
            TrustLevel::CertificateReplayed,
        );

        let pairs = u.find_equivalences();
        assert_eq!(pairs.len(), 1);
        assert_eq!(pairs[0].matched_name, "True");
    }

    #[test]
    fn test_find_equivalences_no_match_different_base_names() {
        let mut u = HolUnifier::new();
        u.add_hol_light_constant(
            "HOL.True",
            "Prop",
            profile(),
            TrustLevel::CertificateReplayed,
        );
        u.add_hol4_constant(
            "boolTheory.False",
            "Prop",
            profile(),
            TrustLevel::CertificateReplayed,
        );

        let pairs = u.find_equivalences();
        assert!(pairs.is_empty());
    }

    #[test]
    fn test_find_equivalences_same_system_no_match() {
        let mut u = HolUnifier::new();
        u.add_hol_light_constant(
            "HOL.True",
            "Prop",
            profile(),
            TrustLevel::CertificateReplayed,
        );
        u.add_hol_light_constant(
            "Logic.True",
            "Prop",
            profile(),
            TrustLevel::CertificateReplayed,
        );

        // Same source system -> not an equivalence pair
        let pairs = u.find_equivalences();
        assert!(pairs.is_empty());
    }

    #[test]
    fn test_find_equivalences_three_way_match() {
        let mut u = HolUnifier::new();
        u.add_hol_light_constant(
            "HOL.True",
            "Prop",
            profile(),
            TrustLevel::CertificateReplayed,
        );
        u.add_hol4_constant(
            "boolTheory.True",
            "Prop",
            profile(),
            TrustLevel::CertificateReplayed,
        );
        u.add_isabelle_constant(
            "HOL.True",
            "Prop",
            profile(),
            TrustLevel::CertificateReplayed,
        );

        let pairs = u.find_equivalences();
        // 3 systems with same base name -> 3 pairs: (HL,H4), (HL,Isa), (H4,Isa)
        assert_eq!(pairs.len(), 3);
    }

    #[test]
    fn test_unified_constants_returns_all() {
        let mut u = HolUnifier::new();
        u.add_hol_light_constant("a", "T", profile(), TrustLevel::CertificateReplayed);
        u.add_hol4_constant("b", "T", profile(), TrustLevel::PartiallyAxiomatized);
        u.add_isabelle_constant("c", "T", profile(), TrustLevel::CertificateReplayed);

        let all = u.unified_constants();
        assert_eq!(all.len(), 3);
    }

    #[test]
    fn test_unify_constant_reports_alignment_evidence() {
        let mut u = HolUnifier::new();
        u.add_hol_light_constant(
            "HOL.True",
            "Prop",
            profile(),
            TrustLevel::CertificateReplayed,
        );
        u.add_hol4_constant(
            "boolTheory.True",
            "Prop",
            profile(),
            TrustLevel::CertificateReplayed,
        );

        let result = u.unify_constant("True");
        assert!(result.is_confident());
        assert_eq!(result.match_score, 1.0);
        assert_eq!(result.alignment.system_count(), 2);
        assert_eq!(
            result.alignment_evidence,
            [
                "base name 'True' matched across 2 systems",
                "all systems share identical type representation",
            ]
        );
    }

    #[test]
    fn test_statistics_counts() {
        let mut u = HolUnifier::new();
        u.add_hol_light_constant("a.X", "T", profile(), TrustLevel::CertificateReplayed);
        u.add_hol_light_constant("b.Y", "T", profile(), TrustLevel::PartiallyAxiomatized);
        u.add_hol4_constant("c.X", "T", profile(), TrustLevel::CertificateReplayed);
        u.add_isabelle_constant("d.Z", "T", profile(), TrustLevel::CertificateReplayed);

        let stats = u.statistics();
        assert_eq!(stats.total_constants, 4);
        assert_eq!(stats.hol_light.constant_count, 2);
        assert_eq!(stats.hol_light.proved_count, 1);
        assert_eq!(stats.hol_light.axiomatized_count, 1);
        assert_eq!(stats.hol4.constant_count, 1);
        assert_eq!(stats.hol4.proved_count, 1);
        assert_eq!(stats.isabelle.constant_count, 1);
        assert_eq!(stats.isabelle.proved_count, 1);
        // a.X (HolLight) and c.X (Hol4) share base name "X"
        assert_eq!(stats.equivalence_count, 1);
    }

    #[test]
    fn test_constants_from_filters_correctly() {
        let mut u = HolUnifier::new();
        u.add_hol_light_constant("hl1", "T", profile(), TrustLevel::CertificateReplayed);
        u.add_hol_light_constant("hl2", "T", profile(), TrustLevel::CertificateReplayed);
        u.add_hol4_constant("h4", "T", profile(), TrustLevel::CertificateReplayed);

        let hl = u.constants_from(&SourceSystem::HolLight);
        assert_eq!(hl.len(), 2);
        let h4 = u.constants_from(&SourceSystem::Hol4);
        assert_eq!(h4.len(), 1);
        let isa = u.constants_from(&SourceSystem::Isabelle);
        assert!(isa.is_empty());
    }

    #[test]
    fn test_search_by_name() {
        let mut u = HolUnifier::new();
        u.add_hol_light_constant("Nat.add", "T", profile(), TrustLevel::CertificateReplayed);
        u.add_hol4_constant("Nat.mul", "T", profile(), TrustLevel::CertificateReplayed);
        u.add_isabelle_constant("Int.add", "T", profile(), TrustLevel::CertificateReplayed);

        let results = u.search_by_name("add");
        assert_eq!(results.len(), 2);
        let results = u.search_by_name("Nat");
        assert_eq!(results.len(), 2);
        let results = u.search_by_name("nonexistent");
        assert!(results.is_empty());
    }

    #[test]
    fn test_merge_unifiers() {
        let mut u1 = HolUnifier::new();
        u1.add_hol_light_constant("a", "T", profile(), TrustLevel::CertificateReplayed);

        let mut u2 = HolUnifier::new();
        u2.add_hol4_constant("b", "T", profile(), TrustLevel::CertificateReplayed);
        u2.add_isabelle_constant("c", "T", profile(), TrustLevel::CertificateReplayed);

        let id_map = u1.merge(&u2);
        assert_eq!(u1.len(), 3);
        assert_eq!(id_map.len(), 2);
        // Old IDs from u2 (0, 1) map to new IDs in u1 (1, 2)
        assert_eq!(id_map[0], (0, 1));
        assert_eq!(id_map[1], (1, 2));
    }

    #[test]
    fn test_get_nonexistent_id_returns_none() {
        let u = HolUnifier::new();
        assert!(u.get(999).is_none());
    }

    #[test]
    fn test_base_name_extraction() {
        assert_eq!(base_name("HOL.True"), "True");
        assert_eq!(base_name("Nat.Suc"), "Suc");
        assert_eq!(base_name("a.b.c.Deep"), "Deep");
        assert_eq!(base_name("simple"), "simple");
    }

    #[test]
    fn test_equivalence_pair_deterministic_order() {
        let mut u = HolUnifier::new();
        // Add in reverse order to test sorting
        u.add_isabelle_constant("z.Comm", "T", profile(), TrustLevel::CertificateReplayed);
        u.add_hol4_constant("y.Comm", "T", profile(), TrustLevel::CertificateReplayed);
        u.add_hol_light_constant("x.Comm", "T", profile(), TrustLevel::CertificateReplayed);

        let pairs = u.find_equivalences();
        assert_eq!(pairs.len(), 3);
        // Should be sorted by (left, right)
        for i in 1..pairs.len() {
            let prev = (pairs[i - 1].left, pairs[i - 1].right);
            let curr = (pairs[i].left, pairs[i].right);
            assert!(prev <= curr, "pairs should be sorted: {prev:?} vs {curr:?}");
        }
    }
}
