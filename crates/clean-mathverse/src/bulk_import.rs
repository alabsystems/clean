// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Batch processing pipeline for importing multiple theorems from multiple source systems.
//!
//! [`BulkImporter`] accumulates constants and their dependency edges, then
//! [`BulkImporter::finalize`] runs axiom-profile propagation, trust-gate
//! enforcement, and training-export filtering in a single pass to produce a
//! [`BulkImportResult`] with a full [`AuditReport`].

use hashbrown::HashMap;
use thiserror::Error;

use crate::trust::audit_report::{AuditReport, AuditReportBuilder};
use crate::trust::axiom_propagation::DependencyGraph;
use crate::trust::graph_gate::{TrainingExportGate, TrustGate, TrustViolation};
use crate::types::{AxiomProfile, Provenance, SourceSystem, TrustLevel};

// ---------------------------------------------------------------------------
// Error
// ---------------------------------------------------------------------------

/// Errors that can occur during bulk import.
#[non_exhaustive]
#[derive(Debug, Error)]
pub enum BulkImportError {
    /// Axiom profile propagation (cycle or bounds) failed.
    #[error("axiom propagation failed: {0}")]
    PropagationFailed(String),

    /// Trust gate detected an illegal dependency.
    #[error("trust violation: {0}")]
    TrustViolation(String),

    /// A constant with the same name was already added (and duplicates disallowed).
    #[error("duplicate constant: {name}")]
    DuplicateConstant { name: String },

    /// The batch exceeded the configured capacity limit.
    #[error("capacity exceeded: max {max}, attempted {attempted}")]
    CapacityExceeded { max: usize, attempted: usize },

    /// An index referenced a constant that does not exist.
    #[error("node index out of bounds: {index}")]
    IndexOutOfBounds { index: u32 },
}

// ---------------------------------------------------------------------------
// ImportedConstant
// ---------------------------------------------------------------------------

/// A constant staged for bulk import.
#[derive(Clone, Debug)]
pub struct ImportedConstant {
    pub name: String,
    pub source: SourceSystem,
    pub axiom_profile: AxiomProfile,
    pub trust_level: TrustLevel,
    pub provenance: Provenance,
    pub dependencies: Vec<u32>,
}

// ---------------------------------------------------------------------------
// BulkImportConfig + builder
// ---------------------------------------------------------------------------

/// Configuration for a bulk import session.
#[derive(Clone, Debug)]
pub struct BulkImportConfig {
    max_constants: usize,
    enforce_trust_gate: bool,
    allow_duplicates: bool,
    custom_trust_gate: Option<TrustGate>,
}

impl Default for BulkImportConfig {
    fn default() -> Self {
        Self {
            max_constants: 1_000_000,
            enforce_trust_gate: true,
            allow_duplicates: false,
            custom_trust_gate: None,
        }
    }
}

impl BulkImportConfig {
    /// Start building a configuration with defaults.
    pub fn builder() -> BulkImportConfigBuilder {
        BulkImportConfigBuilder::default()
    }
}

/// Builder for [`BulkImportConfig`].
#[derive(Clone, Debug)]
#[must_use]
#[derive(Default)]
pub struct BulkImportConfigBuilder {
    config: BulkImportConfig,
}

impl BulkImportConfigBuilder {
    /// Maximum number of constants the batch will accept.
    pub fn max_constants(mut self, max: usize) -> Self {
        self.config.max_constants = max;
        self
    }

    /// Whether to enforce trust-gate rules during finalization.
    pub fn enforce_trust_gate(mut self, enforce: bool) -> Self {
        self.config.enforce_trust_gate = enforce;
        self
    }

    /// Whether to allow constants with the same name.
    pub fn allow_duplicates(mut self, allow: bool) -> Self {
        self.config.allow_duplicates = allow;
        self
    }

    /// Provide a custom trust gate policy (overrides the default hierarchical policy).
    pub fn trust_gate(mut self, gate: TrustGate) -> Self {
        self.config.custom_trust_gate = Some(gate);
        self
    }

    /// Consume the builder and produce the final configuration.
    pub fn build(self) -> BulkImportConfig {
        self.config
    }
}

// ---------------------------------------------------------------------------
// BulkImportResult
// ---------------------------------------------------------------------------

/// Summary produced by [`BulkImporter::finalize`].
#[derive(Debug)]
pub struct BulkImportResult {
    /// Total number of constants in the batch.
    pub total_constants: usize,
    /// Whether axiom-profile propagation succeeded and the invariant holds.
    pub propagation_ok: bool,
    /// Trust violations detected during the trust-gate audit.
    pub trust_violations: Vec<TrustViolation>,
    /// Full audit report with breakdowns and findings.
    pub audit_report: AuditReport,
    /// Number of constants eligible for AI training export.
    pub exportable_count: usize,
    /// Count of constants grouped by source system name.
    pub by_source: HashMap<String, usize>,
}

impl BulkImportResult {
    /// True when propagation succeeded, no trust violations, and the audit is clean.
    #[must_use]
    pub fn is_clean(&self) -> bool {
        self.propagation_ok && self.trust_violations.is_empty() && self.audit_report.is_clean()
    }

    /// Number of distinct source systems in the batch.
    #[must_use]
    pub fn source_count(&self) -> usize {
        self.by_source.len()
    }
}

// ---------------------------------------------------------------------------
// BulkImporter
// ---------------------------------------------------------------------------

/// Accumulates constants and dependency edges, then finalizes the import by
/// running axiom-profile propagation, trust-gate audit, and training-export
/// filtering.
pub struct BulkImporter {
    constants: Vec<ImportedConstant>,
    name_index: HashMap<String, u32>,
    config: BulkImportConfig,
}

impl BulkImporter {
    /// Create a new importer with the given configuration.
    #[must_use]
    pub fn new(config: BulkImportConfig) -> Self {
        Self {
            constants: Vec::new(),
            name_index: HashMap::new(),
            config,
        }
    }

    /// Add a constant to the import batch. Returns the assigned index.
    ///
    /// # Errors
    ///
    /// - [`BulkImportError::CapacityExceeded`] if the batch is full.
    /// - [`BulkImportError::DuplicateConstant`] if duplicates are disallowed and the
    ///   name already exists.
    pub fn add_constant(&mut self, constant: ImportedConstant) -> Result<u32, BulkImportError> {
        if self.constants.len() >= self.config.max_constants {
            return Err(BulkImportError::CapacityExceeded {
                max: self.config.max_constants,
                attempted: self.constants.len() + 1,
            });
        }

        if !self.config.allow_duplicates {
            if let Some(&existing) = self.name_index.get(&constant.name) {
                return Err(BulkImportError::DuplicateConstant {
                    name: format!("{} (existing index {})", constant.name, existing),
                });
            }
        }

        let idx = self.constants.len() as u32;
        self.name_index.insert(constant.name.clone(), idx);
        self.constants.push(constant);
        Ok(idx)
    }

    /// Add a dependency edge: `from` depends on `to`.
    ///
    /// # Errors
    ///
    /// Returns [`BulkImportError::IndexOutOfBounds`] if either index is invalid.
    pub fn add_dependency(&mut self, from: u32, to: u32) -> Result<(), BulkImportError> {
        if from as usize >= self.constants.len() {
            return Err(BulkImportError::IndexOutOfBounds { index: from });
        }
        if to as usize >= self.constants.len() {
            return Err(BulkImportError::IndexOutOfBounds { index: to });
        }
        self.constants[from as usize].dependencies.push(to);
        Ok(())
    }

    /// Number of constants currently staged.
    #[must_use]
    pub fn constant_count(&self) -> usize {
        self.constants.len()
    }

    /// Look up a constant index by name.
    #[must_use]
    pub fn lookup_by_name(&self, name: &str) -> Option<u32> {
        self.name_index.get(name).copied()
    }

    /// Finalize the import: propagate axiom profiles, enforce trust gate,
    /// filter training exports, and build the audit report.
    ///
    /// # Errors
    ///
    /// Returns [`BulkImportError::PropagationFailed`] if the dependency graph
    /// contains a cycle or an out-of-bounds node reference.
    pub fn finalize(&self) -> Result<BulkImportResult, BulkImportError> {
        let n = self.constants.len();

        // 1. Build dependency graph.
        let mut graph = DependencyGraph::new(n);
        for (i, c) in self.constants.iter().enumerate() {
            graph
                .set_initial_profile(i as u32, c.axiom_profile)
                .map_err(|e| BulkImportError::PropagationFailed(e.to_string()))?;
            for &dep in &c.dependencies {
                graph
                    .add_edge(i as u32, dep)
                    .map_err(|e| BulkImportError::PropagationFailed(e.to_string()))?;
            }
        }

        // 2. Propagate axiom profiles transitively.
        graph
            .propagate()
            .map_err(|e| BulkImportError::PropagationFailed(e.to_string()))?;

        let propagation_ok = graph.verify_invariant().is_ok();

        // 3. Trust gate audit.
        let gate = self
            .config
            .custom_trust_gate
            .as_ref()
            .cloned()
            .unwrap_or_else(TrustGate::default_policy);

        let trust_levels: Vec<TrustLevel> = self.constants.iter().map(|c| c.trust_level).collect();

        let trust_violations = if self.config.enforce_trust_gate {
            gate.audit_graph(&graph, &trust_levels)
        } else {
            Vec::new()
        };

        // 4. Training export gate.
        let exportable_pairs: Vec<(AxiomProfile, TrustLevel)> = (0..n)
            .map(|i| (graph.profile(i as u32), self.constants[i].trust_level))
            .collect();
        let exportable_count = TrainingExportGate::count_exportable(&exportable_pairs);

        // 5. Build audit report.
        let mut report_builder = AuditReportBuilder::new();
        let mut by_source: HashMap<String, usize> = HashMap::new();

        for (i, c) in self.constants.iter().enumerate() {
            let source_name = format!("{:?}", c.source);
            report_builder.add_constant(c.trust_level, &source_name, graph.profile(i as u32));
            *by_source.entry(source_name).or_insert(0) += 1;
        }
        for v in &trust_violations {
            report_builder.add_violation(v.clone());
        }
        let audit_report = report_builder.build();

        Ok(BulkImportResult {
            total_constants: n,
            propagation_ok,
            trust_violations,
            audit_report,
            exportable_count,
            by_source,
        })
    }
}

// ---------------------------------------------------------------------------
// BulkImportStats
// ---------------------------------------------------------------------------

/// Summary statistics for a completed bulk import.
#[derive(Clone, Debug)]
pub struct BulkImportStats {
    /// Total number of constants imported.
    pub total_constants: usize,
    /// Count of constants grouped by source system.
    pub by_source: HashMap<String, usize>,
    /// Count of constants grouped by trust level.
    pub by_trust_level: HashMap<TrustLevel, usize>,
    /// Count of constants grouped by axiom profile (key = profile.0).
    pub by_axiom_profile: HashMap<u64, usize>,
}

impl BulkImportStats {
    /// Compute stats from a bulk import result.
    #[must_use]
    pub fn from_result(result: &BulkImportResult) -> Self {
        Self {
            total_constants: result.total_constants,
            by_source: result.by_source.clone(),
            by_trust_level: result.audit_report.by_trust_level.clone(),
            by_axiom_profile: HashMap::new(), // populated from constants if available
        }
    }

    /// Number of distinct source systems.
    #[must_use]
    pub fn source_count(&self) -> usize {
        self.by_source.len()
    }

    /// Number of distinct trust levels used.
    #[must_use]
    pub fn trust_level_count(&self) -> usize {
        self.by_trust_level.len()
    }
}

/// Human-readable import report.
#[derive(Clone, Debug)]
pub struct BulkImportReport {
    /// The underlying stats.
    pub stats: BulkImportStats,
    /// Whether the import was clean (no violations, propagation ok).
    pub is_clean: bool,
    /// Count of trust violations detected.
    pub violation_count: usize,
    /// Count of constants exportable for training.
    pub exportable_count: usize,
}

impl BulkImportReport {
    /// Build a report from a bulk import result.
    #[must_use]
    pub fn from_result(result: &BulkImportResult) -> Self {
        Self {
            stats: BulkImportStats::from_result(result),
            is_clean: result.is_clean(),
            violation_count: result.trust_violations.len(),
            exportable_count: result.exportable_count,
        }
    }

    /// Render the report as a human-readable summary.
    #[must_use]
    pub fn summary(&self) -> String {
        let mut lines = Vec::with_capacity(16);
        lines.push("=== Bulk Import Report ===".to_string());
        lines.push(format!("Total constants: {}", self.stats.total_constants));
        lines.push(format!("Source systems: {}", self.stats.source_count()));
        lines.push(format!(
            "Trust levels used: {}",
            self.stats.trust_level_count()
        ));
        lines.push(format!("Trust violations: {}", self.violation_count));
        lines.push(format!(
            "Exportable for training: {}",
            self.exportable_count
        ));

        let status = if self.is_clean {
            "CLEAN"
        } else {
            "ISSUES FOUND"
        };
        lines.push(format!("Status: {}", status));

        // Source breakdown.
        if !self.stats.by_source.is_empty() {
            lines.push("By source:".to_owned());
            let mut sources: Vec<_> = self.stats.by_source.iter().collect();
            sources.sort_by_key(|(left, _)| *left);
            for (name, count) in sources {
                lines.push(format!("  {}: {}", name, count));
            }
        }

        // Trust level breakdown.
        if !self.stats.by_trust_level.is_empty() {
            lines.push("By trust level:".to_owned());
            let mut levels: Vec<_> = self.stats.by_trust_level.iter().collect();
            levels.sort_by_key(|(level, _)| **level);
            for (level, count) in levels {
                lines.push(format!("  {:?}: {}", level, count));
            }
        }

        lines.join("\n")
    }
}

// ---------------------------------------------------------------------------
// BulkImporter extensions
// ---------------------------------------------------------------------------

impl BulkImporter {
    /// Validate the import batch before finalization.
    ///
    /// Runs pre-flight checks:
    /// 1. No empty batch (at least one constant).
    /// 2. All dependency indices are valid.
    /// 3. No self-referential dependencies.
    ///
    /// # Errors
    ///
    /// Returns the first validation error found.
    pub fn validate_before_finalize(&self) -> Result<(), BulkImportError> {
        if self.constants.is_empty() {
            return Err(BulkImportError::PropagationFailed(
                "empty batch: no constants to import".to_owned(),
            ));
        }

        let n = self.constants.len();
        for (i, c) in self.constants.iter().enumerate() {
            for &dep in &c.dependencies {
                if dep as usize >= n {
                    return Err(BulkImportError::IndexOutOfBounds { index: dep });
                }
                if dep as usize == i {
                    return Err(BulkImportError::PropagationFailed(format!(
                        "self-referential dependency: constant {} depends on itself",
                        c.name
                    )));
                }
            }
        }

        Ok(())
    }

    /// Convenience method: import a batch of constants from a single source system.
    ///
    /// All constants in the batch share the same source, trust level, and axiom profile.
    /// Dependencies between them are specified as pairs of names.
    ///
    /// # Errors
    ///
    /// Returns errors from `add_constant` or `add_dependency`.
    pub fn import_from_source(
        &mut self,
        source: SourceSystem,
        trust: TrustLevel,
        profile: AxiomProfile,
        names: &[&str],
        deps: &[(&str, &str)],
    ) -> Result<Vec<u32>, BulkImportError> {
        let mut indices = Vec::with_capacity(names.len());
        let mut name_to_idx = HashMap::new();

        for &name in names {
            let idx = self.add_constant(ImportedConstant {
                name: name.to_owned(),
                source,
                axiom_profile: profile,
                trust_level: trust,
                provenance: Provenance {
                    source,
                    original_name: name.to_owned(),
                    source_file: None,
                    axiom_profile: profile,
                },
                dependencies: Vec::new(),
            })?;
            name_to_idx.insert(name, idx);
            indices.push(idx);
        }

        for &(from_name, to_name) in deps {
            let from_idx = name_to_idx.get(from_name).copied().ok_or_else(|| {
                BulkImportError::PropagationFailed(format!(
                    "dependency source '{}' not found in batch",
                    from_name
                ))
            })?;
            let to_idx = name_to_idx.get(to_name).copied().ok_or_else(|| {
                BulkImportError::PropagationFailed(format!(
                    "dependency target '{}' not found in batch",
                    to_name
                ))
            })?;
            self.add_dependency(from_idx, to_idx)?;
        }

        Ok(indices)
    }

    /// Compute detailed stats from the finalized result, including
    /// per-axiom-profile breakdown.
    #[must_use]
    pub fn compute_stats(&self) -> BulkImportStats {
        let mut by_source: HashMap<String, usize> = HashMap::new();
        let mut by_trust_level: HashMap<TrustLevel, usize> = HashMap::new();
        let mut by_axiom_profile: HashMap<u64, usize> = HashMap::new();

        for c in &self.constants {
            let source_name = format!("{:?}", c.source);
            *by_source.entry(source_name).or_insert(0) += 1;
            *by_trust_level.entry(c.trust_level).or_insert(0) += 1;
            *by_axiom_profile.entry(c.axiom_profile.0).or_insert(0) += 1;
        }

        BulkImportStats {
            total_constants: self.constants.len(),
            by_source,
            by_trust_level,
            by_axiom_profile,
        }
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    /// Helper: build a kernel-verified constant with no axiom deps.
    fn make_pure(name: &str, source: SourceSystem) -> ImportedConstant {
        ImportedConstant {
            name: name.to_owned(),
            source,
            axiom_profile: AxiomProfile::NONE,
            trust_level: TrustLevel::KernelVerified,
            provenance: Provenance {
                source,
                original_name: name.to_owned(),
                source_file: None,
                axiom_profile: AxiomProfile::NONE,
            },
            dependencies: Vec::new(),
        }
    }

    /// Helper: build a constant with the given profile and trust level.
    fn make_constant(
        name: &str,
        source: SourceSystem,
        profile: AxiomProfile,
        trust: TrustLevel,
    ) -> ImportedConstant {
        ImportedConstant {
            name: name.to_owned(),
            source,
            axiom_profile: profile,
            trust_level: trust,
            provenance: Provenance {
                source,
                original_name: name.to_owned(),
                source_file: None,
                axiom_profile: profile,
            },
            dependencies: Vec::new(),
        }
    }

    // -----------------------------------------------------------------------
    // Adding constants from multiple sources
    // -----------------------------------------------------------------------

    #[test]
    fn test_add_constants_from_multiple_sources() {
        let config = BulkImportConfig::builder().build();
        let mut importer = BulkImporter::new(config);

        let idx0 = importer
            .add_constant(make_pure("Nat.add_comm", SourceSystem::Lean4))
            .expect("add Lean4");
        let idx1 = importer
            .add_constant(make_pure("nat_add_comm", SourceSystem::Coq))
            .expect("add Coq");
        let idx2 = importer
            .add_constant(make_pure("ADD_COMM", SourceSystem::Metamath))
            .expect("add Metamath");

        assert_eq!(idx0, 0);
        assert_eq!(idx1, 1);
        assert_eq!(idx2, 2);
        assert_eq!(importer.constant_count(), 3);
    }

    // -----------------------------------------------------------------------
    // Dependency tracking
    // -----------------------------------------------------------------------

    #[test]
    fn test_dependency_tracking() {
        let config = BulkImportConfig::builder()
            .enforce_trust_gate(false)
            .build();
        let mut importer = BulkImporter::new(config);

        let a = importer
            .add_constant(make_pure("A", SourceSystem::Lean4))
            .expect("add A");
        let b = importer
            .add_constant(make_constant(
                "B",
                SourceSystem::Lean4,
                AxiomProfile::CLASSICAL,
                TrustLevel::AxiomDependent,
            ))
            .expect("add B");

        importer.add_dependency(b, a).expect("B depends on A");

        assert_eq!(importer.constants[b as usize].dependencies, vec![a]);

        let result = importer.finalize().expect("finalize");
        assert_eq!(result.total_constants, 2);
        assert!(result.propagation_ok);
    }

    #[test]
    fn test_add_dependency_out_of_range() {
        let config = BulkImportConfig::builder().build();
        let mut importer = BulkImporter::new(config);

        importer
            .add_constant(make_pure("A", SourceSystem::Lean4))
            .expect("add A");

        let err = importer.add_dependency(0, 99).unwrap_err();
        match err {
            BulkImportError::IndexOutOfBounds { index } => assert_eq!(index, 99),
            other => panic!("expected IndexOutOfBounds, got: {other}"),
        }
    }

    // -----------------------------------------------------------------------
    // Finalize with propagation
    // -----------------------------------------------------------------------

    #[test]
    fn test_finalize_propagates_axiom_profiles() {
        let config = BulkImportConfig::builder()
            .enforce_trust_gate(false)
            .build();
        let mut importer = BulkImporter::new(config);

        // Constant 0: has CLASSICAL
        let a = importer
            .add_constant(make_constant(
                "Base",
                SourceSystem::HolLight,
                AxiomProfile::CLASSICAL,
                TrustLevel::CertificateReplayed,
            ))
            .expect("add Base");

        // Constant 1: has EXTENSIONALITY, depends on 0
        let mut derived = make_constant(
            "Derived",
            SourceSystem::HolLight,
            AxiomProfile::EXTENSIONALITY,
            TrustLevel::CertificateReplayed,
        );
        derived.dependencies.push(a);
        importer.add_constant(derived).expect("add Derived");

        let result = importer.finalize().expect("finalize");
        assert!(result.propagation_ok);
        assert_eq!(result.total_constants, 2);
        // Neither is kernel-verified, so none exportable.
        assert_eq!(result.exportable_count, 0);
    }

    #[test]
    fn test_finalize_simple_pure() {
        let config = BulkImportConfig::builder().build();
        let mut importer = BulkImporter::new(config);

        importer
            .add_constant(make_pure("Nat.zero", SourceSystem::Lean4))
            .expect("add");
        importer
            .add_constant(make_pure("Nat.succ", SourceSystem::Lean4))
            .expect("add");

        let result = importer.finalize().expect("finalize");
        assert_eq!(result.total_constants, 2);
        assert!(result.propagation_ok);
        assert!(result.trust_violations.is_empty());
        assert_eq!(result.exportable_count, 2);
    }

    // -----------------------------------------------------------------------
    // Trust gate violations
    // -----------------------------------------------------------------------

    #[test]
    fn test_trust_gate_violations_detected() {
        let config = BulkImportConfig::builder().enforce_trust_gate(true).build();
        let mut importer = BulkImporter::new(config);

        // KernelVerified depends on TrustedOracle — violates default policy.
        let oracle = importer
            .add_constant(make_constant(
                "oracle_result",
                SourceSystem::SmtSolver,
                AxiomProfile::SMT_ORACLE,
                TrustLevel::TrustedOracle,
            ))
            .expect("add oracle");

        let mut kv = make_pure("proven_via_oracle", SourceSystem::Lean4);
        kv.dependencies.push(oracle);
        importer.add_constant(kv).expect("add kv");

        let result = importer.finalize().expect("finalize");
        assert!(
            !result.trust_violations.is_empty(),
            "KernelVerified depending on TrustedOracle should violate default policy"
        );
        assert!(!result.is_clean());
    }

    #[test]
    fn test_trust_gate_violations_suppressed_when_disabled() {
        let config = BulkImportConfig::builder()
            .enforce_trust_gate(false)
            .build();
        let mut importer = BulkImporter::new(config);

        let oracle = importer
            .add_constant(make_constant(
                "oracle_result",
                SourceSystem::SmtSolver,
                AxiomProfile::SMT_ORACLE,
                TrustLevel::TrustedOracle,
            ))
            .expect("add oracle");

        let mut kv = make_pure("proven_via_oracle", SourceSystem::Lean4);
        kv.dependencies.push(oracle);
        importer.add_constant(kv).expect("add kv");

        let result = importer.finalize().expect("finalize");
        assert!(result.trust_violations.is_empty());
    }

    // -----------------------------------------------------------------------
    // Capacity limits
    // -----------------------------------------------------------------------

    #[test]
    fn test_capacity_exceeded() {
        let config = BulkImportConfig::builder().max_constants(2).build();
        let mut importer = BulkImporter::new(config);

        importer
            .add_constant(make_pure("A", SourceSystem::Lean4))
            .expect("add A");
        importer
            .add_constant(make_pure("B", SourceSystem::Lean4))
            .expect("add B");

        let err = importer
            .add_constant(make_pure("C", SourceSystem::Lean4))
            .unwrap_err();
        match err {
            BulkImportError::CapacityExceeded { max, attempted } => {
                assert_eq!(max, 2);
                assert_eq!(attempted, 3);
            }
            other => panic!("expected CapacityExceeded, got: {other}"),
        }
    }

    // -----------------------------------------------------------------------
    // Duplicate detection
    // -----------------------------------------------------------------------

    #[test]
    fn test_duplicate_detection() {
        let config = BulkImportConfig::builder().allow_duplicates(false).build();
        let mut importer = BulkImporter::new(config);

        importer
            .add_constant(make_pure("Nat.add_comm", SourceSystem::Lean4))
            .expect("add first");

        let err = importer
            .add_constant(make_pure("Nat.add_comm", SourceSystem::Coq))
            .unwrap_err();
        match err {
            BulkImportError::DuplicateConstant { name } => {
                assert!(name.contains("Nat.add_comm"));
            }
            other => panic!("expected DuplicateConstant, got: {other}"),
        }
    }

    #[test]
    fn test_allow_duplicates() {
        let config = BulkImportConfig::builder().allow_duplicates(true).build();
        let mut importer = BulkImporter::new(config);

        importer
            .add_constant(make_pure("Nat.add_comm", SourceSystem::Lean4))
            .expect("first");
        importer
            .add_constant(make_pure("Nat.add_comm", SourceSystem::Coq))
            .expect("duplicate should succeed");

        assert_eq!(importer.constant_count(), 2);
    }

    // -----------------------------------------------------------------------
    // Training export gate filtering
    // -----------------------------------------------------------------------

    #[test]
    fn test_training_export_gate_only_kernel_verified() {
        let config = BulkImportConfig::builder()
            .enforce_trust_gate(false)
            .build();
        let mut importer = BulkImporter::new(config);

        // KernelVerified + NONE => exportable
        importer
            .add_constant(make_pure("Pure", SourceSystem::Lean4))
            .expect("add Pure");

        // CertificateReplayed + CLASSICAL => not exportable
        importer
            .add_constant(make_constant(
                "Replayed",
                SourceSystem::HolLight,
                AxiomProfile::CLASSICAL,
                TrustLevel::CertificateReplayed,
            ))
            .expect("add Replayed");

        // TrustedOracle => not exportable
        importer
            .add_constant(make_constant(
                "Oracle",
                SourceSystem::SmtSolver,
                AxiomProfile::SMT_ORACLE,
                TrustLevel::TrustedOracle,
            ))
            .expect("add Oracle");

        let result = importer.finalize().expect("finalize");
        assert_eq!(
            result.exportable_count, 1,
            "only KernelVerified+NONE is exportable"
        );
    }

    #[test]
    fn test_training_export_kernel_verified_with_axioms_not_exportable() {
        let config = BulkImportConfig::builder()
            .enforce_trust_gate(false)
            .build();
        let mut importer = BulkImporter::new(config);

        // KernelVerified but has CLASSICAL bits => NOT exportable
        importer
            .add_constant(make_constant(
                "WithAxioms",
                SourceSystem::Lean4,
                AxiomProfile::CLASSICAL,
                TrustLevel::KernelVerified,
            ))
            .expect("add");

        let result = importer.finalize().expect("finalize");
        assert_eq!(
            result.exportable_count, 0,
            "KernelVerified with axiom bits is not exportable"
        );
    }

    // -----------------------------------------------------------------------
    // Lookup
    // -----------------------------------------------------------------------

    #[test]
    fn test_lookup_by_name() {
        let config = BulkImportConfig::builder().build();
        let mut importer = BulkImporter::new(config);

        importer
            .add_constant(make_pure("Nat.add_comm", SourceSystem::Lean4))
            .expect("add");

        assert_eq!(importer.lookup_by_name("Nat.add_comm"), Some(0));
        assert_eq!(importer.lookup_by_name("nonexistent"), None);
    }

    // -----------------------------------------------------------------------
    // By-source aggregation
    // -----------------------------------------------------------------------

    #[test]
    fn test_by_source_aggregation() {
        let config = BulkImportConfig::builder()
            .enforce_trust_gate(false)
            .build();
        let mut importer = BulkImporter::new(config);

        importer
            .add_constant(make_pure("A", SourceSystem::Lean4))
            .expect("add A");
        importer
            .add_constant(make_pure("B", SourceSystem::Lean4))
            .expect("add B");
        importer
            .add_constant(make_pure("C", SourceSystem::Coq))
            .expect("add C");
        importer
            .add_constant(make_pure("D", SourceSystem::Metamath))
            .expect("add D");

        let result = importer.finalize().expect("finalize");
        assert_eq!(result.by_source.get("Lean4"), Some(&2));
        assert_eq!(result.by_source.get("Coq"), Some(&1));
        assert_eq!(result.by_source.get("Metamath"), Some(&1));
        assert_eq!(result.source_count(), 3);
    }

    // -----------------------------------------------------------------------
    // Propagation failure (cycle)
    // -----------------------------------------------------------------------

    #[test]
    fn test_finalize_cycle_detection() {
        let config = BulkImportConfig::builder()
            .enforce_trust_gate(false)
            .build();
        let mut importer = BulkImporter::new(config);

        let mut a = make_pure("A", SourceSystem::Lean4);
        a.dependencies.push(1); // A depends on B
        importer.add_constant(a).expect("add A");

        let mut b = make_pure("B", SourceSystem::Lean4);
        b.dependencies.push(0); // B depends on A -- cycle
        importer.add_constant(b).expect("add B");

        let err = importer.finalize().unwrap_err();
        match err {
            BulkImportError::PropagationFailed(msg) => {
                assert!(msg.contains("cycle") || msg.contains("Cycle"), "msg: {msg}");
            }
            other => panic!("expected PropagationFailed, got: {other}"),
        }
    }

    // -----------------------------------------------------------------------
    // Result / audit report integration
    // -----------------------------------------------------------------------

    #[test]
    fn test_result_is_clean() {
        let config = BulkImportConfig::builder()
            .enforce_trust_gate(false)
            .build();
        let mut importer = BulkImporter::new(config);

        importer
            .add_constant(make_pure("A", SourceSystem::Lean4))
            .expect("add A");

        let result = importer.finalize().expect("finalize");
        assert!(result.is_clean());
        assert_eq!(result.audit_report.total_constants, 1);
    }

    #[test]
    fn test_audit_report_trust_breakdown() {
        let config = BulkImportConfig::builder()
            .enforce_trust_gate(false)
            .build();
        let mut importer = BulkImporter::new(config);

        importer
            .add_constant(make_pure("A", SourceSystem::Lean4))
            .expect("add A");
        importer
            .add_constant(make_constant(
                "B",
                SourceSystem::HolLight,
                AxiomProfile::CLASSICAL,
                TrustLevel::CertificateReplayed,
            ))
            .expect("add B");
        importer
            .add_constant(make_constant(
                "C",
                SourceSystem::SmtSolver,
                AxiomProfile::SMT_ORACLE,
                TrustLevel::TrustedOracle,
            ))
            .expect("add C");

        let result = importer.finalize().expect("finalize");
        let report = &result.audit_report;

        assert_eq!(report.total_constants, 3);
        assert_eq!(report.by_trust_level[&TrustLevel::KernelVerified], 1);
        assert_eq!(report.by_trust_level[&TrustLevel::CertificateReplayed], 1);
        assert_eq!(report.by_trust_level[&TrustLevel::TrustedOracle], 1);
        assert_eq!(report.exportable_for_training, 1);
    }

    // -----------------------------------------------------------------------
    // Empty import
    // -----------------------------------------------------------------------

    #[test]
    fn test_empty_finalize() {
        let config = BulkImportConfig::builder()
            .enforce_trust_gate(false)
            .build();
        let importer = BulkImporter::new(config);

        let result = importer.finalize().expect("finalize");
        assert_eq!(result.total_constants, 0);
        assert!(result.propagation_ok);
        assert!(result.trust_violations.is_empty());
        assert_eq!(result.exportable_count, 0);
        assert!(result.is_clean());
    }

    // -----------------------------------------------------------------------
    // Builder pattern
    // -----------------------------------------------------------------------

    #[test]
    fn test_builder_defaults() {
        let config = BulkImportConfig::builder().build();
        assert_eq!(config.max_constants, 1_000_000);
        assert!(config.enforce_trust_gate);
        assert!(!config.allow_duplicates);
        assert!(config.custom_trust_gate.is_none());
    }

    #[test]
    fn test_builder_custom() {
        let config = BulkImportConfig::builder()
            .max_constants(500)
            .enforce_trust_gate(false)
            .allow_duplicates(true)
            .build();
        assert_eq!(config.max_constants, 500);
        assert!(!config.enforce_trust_gate);
        assert!(config.allow_duplicates);
    }
}
