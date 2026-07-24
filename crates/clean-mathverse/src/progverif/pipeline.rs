// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Unified program verification import pipeline.
//!
//! Provides a single entry point for importing verification results from
//! any supported program verification system. The pipeline registers importers
//! by name and dispatches import operations based on source system tags.
//!
//! This module consolidates the individual importers (Dafny, Why3, F*, Metamath,
//! PVS, ACL2, Nuprl, LiquidHaskell, KeY/Frama-C/SPARK) into a unified
//! pipeline that tracks statistics and axiom profiles across all imports.

use hashbrown::HashMap;
use serde::{Deserialize, Serialize};

use crate::types::{AxiomProfile, SourceSystem, TrustLevel};

use super::dafny::DafnyImporter;
use super::fstar::FStarImporter;
use super::metamath::MetamathImporter;
use super::why3::Why3Importer;

// ============================================================================
// Errors
// ============================================================================

/// Errors raised during pipeline operations.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum PipelineError {
    /// No importer registered for the given source system.
    #[error("no importer registered for source: {system}")]
    NoImporter { system: String },

    /// Import operation failed.
    #[error("import failed for `{name}` ({system}): {reason}")]
    ImportFailed {
        name: String,
        system: String,
        reason: String,
    },

    /// Pipeline configuration error.
    #[error("pipeline configuration error: {reason}")]
    ConfigError { reason: String },
}

// ============================================================================
// Import result
// ============================================================================

/// Unified result from importing a single verification artifact.
///
/// Normalizes the output of all tool-specific importers into a common
/// format for downstream consumers (trust tracking, metrics, reporting).
#[derive(Debug, Clone, Serialize, Deserialize)]
#[non_exhaustive]
pub struct ProgverifImportResult {
    /// Source system that produced this result.
    pub source: SourceSystem,
    /// Name of the imported artifact (module, session, database, etc.).
    pub name: String,
    /// Total number of verification conditions.
    pub vc_count: usize,
    /// Number of VCs successfully verified.
    pub verified_count: usize,
    /// Axiom profile for the imported result.
    pub axiom_profile: AxiomProfile,
    /// Trust level assigned to the imported result.
    pub trust_level: TrustLevel,
    /// Diagnostic messages from the import process.
    pub diagnostics: Vec<String>,
}

impl ProgverifImportResult {
    /// Whether all VCs were verified.
    #[must_use]
    pub fn is_fully_verified(&self) -> bool {
        self.vc_count > 0 && self.verified_count == self.vc_count
    }

    /// Verification ratio as a fraction (0.0 to 1.0).
    #[must_use]
    pub fn verification_ratio(&self) -> f64 {
        if self.vc_count == 0 {
            0.0
        } else {
            self.verified_count as f64 / self.vc_count as f64
        }
    }
}

// ============================================================================
// Importer registration
// ============================================================================

/// An entry in the importer registry.
///
/// Pairs a source system tag with metadata about the registered importer.
#[derive(Debug, Clone)]
pub(crate) struct ImporterEntry {
    /// Human-readable name.
    pub(crate) name: String,
    /// Source system tag.
    pub(crate) source: SourceSystem,
    /// Whether this importer is enabled.
    pub(crate) enabled: bool,
}

// ============================================================================
// Pipeline
// ============================================================================

/// Unified pipeline for importing verification results from multiple systems.
///
/// Importers are registered by name and dispatched based on the source system
/// tag provided with each input. The pipeline tracks aggregate statistics
/// across all imports.
pub struct ProgverifPipeline {
    /// Registered importers, keyed by name.
    importers: HashMap<String, ImporterEntry>,
    /// Whether certificate replay is enabled for tool-specific importers.
    cert_replay_enabled: bool,
}

impl Default for ProgverifPipeline {
    fn default() -> Self {
        Self::new()
    }
}

impl ProgverifPipeline {
    /// Create a new empty pipeline.
    #[must_use]
    pub fn new() -> Self {
        Self {
            importers: HashMap::new(),
            cert_replay_enabled: false,
        }
    }

    /// Enable certificate replay for all registered importers.
    #[must_use]
    pub fn with_cert_replay(mut self, enabled: bool) -> Self {
        self.cert_replay_enabled = enabled;
        self
    }

    /// Register an importer for a given source system.
    ///
    /// The `name` is used to key the importer and must be unique.
    /// If an importer with the same name is already registered, it is replaced.
    pub fn register_importer(&mut self, name: &str, source: SourceSystem) {
        self.importers.insert(
            name.to_string(),
            ImporterEntry {
                name: name.to_string(),
                source,
                enabled: true,
            },
        );
    }

    /// Disable a registered importer by name.
    ///
    /// Disabled importers are skipped during `import_all`.
    pub fn disable_importer(&mut self, name: &str) {
        if let Some(entry) = self.importers.get_mut(name) {
            entry.enabled = false;
        }
    }

    /// Enable a previously disabled importer by name.
    pub fn enable_importer(&mut self, name: &str) {
        if let Some(entry) = self.importers.get_mut(name) {
            entry.enabled = true;
        }
    }

    /// Get the number of registered importers.
    #[must_use]
    pub fn importer_count(&self) -> usize {
        self.importers.len()
    }

    /// Get the number of enabled importers.
    #[must_use]
    pub fn enabled_importer_count(&self) -> usize {
        self.importers.values().filter(|e| e.enabled).count()
    }

    /// Check if an importer is registered for the given name.
    #[must_use]
    pub fn has_importer(&self, name: &str) -> bool {
        self.importers.contains_key(name)
    }

    /// List all registered importer names and their source systems.
    #[must_use]
    pub fn list_importers(&self) -> Vec<(&str, &SourceSystem, bool)> {
        let mut result: Vec<_> = self
            .importers
            .values()
            .map(|e| (e.name.as_str(), &e.source, e.enabled))
            .collect();
        result.sort_by_key(|(name, _, _)| *name);
        result
    }

    /// Import all provided inputs, dispatching to the appropriate importer.
    ///
    /// Each input is a `(importer_name, artifact_text)` pair. The importer
    /// name must match a registered importer. Unknown or disabled importers
    /// produce diagnostic entries in the results.
    ///
    /// Returns one `ProgverifImportResult` per input.
    #[must_use]
    pub fn import_all(&self, inputs: &[(String, String)]) -> Vec<ProgverifImportResult> {
        inputs
            .iter()
            .map(|(importer_name, text)| self.import_one(importer_name, text))
            .collect()
    }

    /// Import a single artifact by importer name and text.
    fn import_one(&self, importer_name: &str, text: &str) -> ProgverifImportResult {
        let entry = match self.importers.get(importer_name) {
            Some(e) => e,
            None => {
                return ProgverifImportResult {
                    source: SourceSystem::SmtSolver, // placeholder
                    name: importer_name.to_string(),
                    vc_count: 0,
                    verified_count: 0,
                    axiom_profile: AxiomProfile::NONE,
                    trust_level: TrustLevel::TrustedOracle,
                    diagnostics: vec![format!("no importer registered for: {importer_name}")],
                };
            }
        };

        if !entry.enabled {
            return ProgverifImportResult {
                source: entry.source,
                name: importer_name.to_string(),
                vc_count: 0,
                verified_count: 0,
                axiom_profile: AxiomProfile::NONE,
                trust_level: TrustLevel::TrustedOracle,
                diagnostics: vec![format!("importer disabled: {importer_name}")],
            };
        }

        match entry.source {
            SourceSystem::Dafny => self.import_dafny(text),
            SourceSystem::Why3 => self.import_why3(text),
            SourceSystem::FStar => self.import_fstar(text),
            SourceSystem::Metamath => self.import_metamath(text),
            _ => ProgverifImportResult {
                source: entry.source,
                name: importer_name.to_string(),
                vc_count: 0,
                verified_count: 0,
                axiom_profile: AxiomProfile::NONE,
                trust_level: TrustLevel::TrustedOracle,
                diagnostics: vec![format!(
                    "importer for {:?} not yet integrated into pipeline",
                    entry.source
                )],
            },
        }
    }

    /// Dispatch to the Dafny importer.
    fn import_dafny(&self, text: &str) -> ProgverifImportResult {
        let importer = DafnyImporter::new().with_cert_replay(self.cert_replay_enabled);
        match importer.import_boogie_vc(text) {
            Ok(vc) => {
                let vc_name = vc.name.clone();
                let result = importer.import_dafny_result(&vc_name, &[vc], true);
                ProgverifImportResult {
                    source: SourceSystem::Dafny,
                    name: result.name,
                    vc_count: result.vc_count,
                    verified_count: result.verified_count,
                    axiom_profile: result.axiom_profile,
                    trust_level: result.trust_level,
                    diagnostics: result.diagnostics,
                }
            }
            Err(e) => ProgverifImportResult {
                source: SourceSystem::Dafny,
                name: "dafny_error".to_string(),
                vc_count: 0,
                verified_count: 0,
                axiom_profile: AxiomProfile::NONE,
                trust_level: TrustLevel::TrustedOracle,
                diagnostics: vec![format!("Dafny import error: {e}")],
            },
        }
    }

    /// Dispatch to the Why3 importer.
    fn import_why3(&self, text: &str) -> ProgverifImportResult {
        let importer = Why3Importer::new();
        match importer.import_session(text) {
            Ok(session) => {
                let result = importer.import_result(&session);
                ProgverifImportResult {
                    source: SourceSystem::Why3,
                    name: result.name,
                    vc_count: result.goal_count,
                    verified_count: result.proved_count,
                    axiom_profile: result.axiom_profile,
                    trust_level: result.trust_level,
                    diagnostics: result.diagnostics,
                }
            }
            Err(e) => ProgverifImportResult {
                source: SourceSystem::Why3,
                name: "why3_error".to_string(),
                vc_count: 0,
                verified_count: 0,
                axiom_profile: AxiomProfile::NONE,
                trust_level: TrustLevel::TrustedOracle,
                diagnostics: vec![format!("Why3 import error: {e}")],
            },
        }
    }

    /// Dispatch to the F* importer.
    fn import_fstar(&self, text: &str) -> ProgverifImportResult {
        let importer = FStarImporter::new().with_cert_replay(self.cert_replay_enabled);
        match importer.import_module(text) {
            Ok(module) => {
                let result = importer.import_result(&module);
                ProgverifImportResult {
                    source: SourceSystem::FStar,
                    name: result.name,
                    vc_count: result.vc_count,
                    verified_count: result.verified_count,
                    axiom_profile: result.axiom_profile,
                    trust_level: result.trust_level,
                    diagnostics: result.diagnostics,
                }
            }
            Err(e) => ProgverifImportResult {
                source: SourceSystem::FStar,
                name: "fstar_error".to_string(),
                vc_count: 0,
                verified_count: 0,
                axiom_profile: AxiomProfile::NONE,
                trust_level: TrustLevel::TrustedOracle,
                diagnostics: vec![format!("F* import error: {e}")],
            },
        }
    }

    /// Dispatch to the Metamath importer.
    fn import_metamath(&self, text: &str) -> ProgverifImportResult {
        let importer = MetamathImporter::new();
        match importer.import_database(text) {
            Ok(db) => {
                let result = importer.import_result(&db);
                ProgverifImportResult {
                    source: SourceSystem::Metamath,
                    name: result.name,
                    vc_count: result.vc_count,
                    verified_count: result.verified_count,
                    axiom_profile: result.axiom_profile,
                    trust_level: result.trust_level,
                    diagnostics: result.diagnostics,
                }
            }
            Err(e) => ProgverifImportResult {
                source: SourceSystem::Metamath,
                name: "metamath_error".to_string(),
                vc_count: 0,
                verified_count: 0,
                axiom_profile: AxiomProfile::NONE,
                trust_level: TrustLevel::TrustedOracle,
                diagnostics: vec![format!("Metamath import error: {e}")],
            },
        }
    }
}

// ============================================================================
// Aggregate statistics
// ============================================================================

/// Aggregate statistics from a batch of import results.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[non_exhaustive]
pub struct PipelineStats {
    /// Total number of artifacts imported.
    pub total_artifacts: usize,
    /// Total number of VCs across all artifacts.
    pub total_vc_count: usize,
    /// Total number of verified VCs.
    pub total_verified_count: usize,
    /// Number of fully verified artifacts.
    pub fully_verified_count: usize,
    /// Combined axiom profile (union of all imports).
    pub combined_axiom_profile: AxiomProfile,
    /// Distribution of trust levels.
    pub trust_level_counts: HashMap<String, usize>,
    /// Distribution of source systems.
    pub source_counts: HashMap<String, usize>,
}

impl PipelineStats {
    /// Compute aggregate statistics from a set of import results.
    #[must_use]
    pub fn from_results(results: &[ProgverifImportResult]) -> Self {
        let mut combined_axiom_profile = AxiomProfile::NONE;
        let mut trust_level_counts: HashMap<String, usize> = HashMap::new();
        let mut source_counts: HashMap<String, usize> = HashMap::new();
        let mut total_vc_count = 0usize;
        let mut total_verified_count = 0usize;
        let mut fully_verified_count = 0usize;

        for result in results {
            total_vc_count += result.vc_count;
            total_verified_count += result.verified_count;
            combined_axiom_profile |= result.axiom_profile;

            if result.is_fully_verified() {
                fully_verified_count += 1;
            }

            let trust_key = format!("{:?}", result.trust_level);
            *trust_level_counts.entry(trust_key).or_insert(0) += 1;

            let source_key = format!("{:?}", result.source);
            *source_counts.entry(source_key).or_insert(0) += 1;
        }

        Self {
            total_artifacts: results.len(),
            total_vc_count,
            total_verified_count,
            fully_verified_count,
            combined_axiom_profile,
            trust_level_counts,
            source_counts,
        }
    }

    /// Overall verification ratio.
    #[must_use]
    pub fn verification_ratio(&self) -> f64 {
        if self.total_vc_count == 0 {
            0.0
        } else {
            self.total_verified_count as f64 / self.total_vc_count as f64
        }
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    fn make_pipeline() -> ProgverifPipeline {
        let mut pipeline = ProgverifPipeline::new();
        pipeline.register_importer("dafny", SourceSystem::Dafny);
        pipeline.register_importer("why3", SourceSystem::Why3);
        pipeline.register_importer("fstar", SourceSystem::FStar);
        pipeline.register_importer("metamath", SourceSystem::Metamath);
        pipeline
    }

    #[test]
    fn test_pipeline_register_and_list() {
        let pipeline = make_pipeline();
        assert_eq!(pipeline.importer_count(), 4);
        assert!(pipeline.has_importer("dafny"));
        assert!(pipeline.has_importer("why3"));
        assert!(pipeline.has_importer("fstar"));
        assert!(pipeline.has_importer("metamath"));
        assert!(!pipeline.has_importer("unknown"));
    }

    #[test]
    fn test_pipeline_list_importers_sorted() {
        let pipeline = make_pipeline();
        let importers = pipeline.list_importers();
        let names: Vec<&str> = importers.iter().map(|(n, _, _)| *n).collect();
        assert_eq!(names, vec!["dafny", "fstar", "metamath", "why3"]);
    }

    #[test]
    fn test_pipeline_disable_enable() {
        let mut pipeline = make_pipeline();
        assert_eq!(pipeline.enabled_importer_count(), 4);

        pipeline.disable_importer("dafny");
        assert_eq!(pipeline.enabled_importer_count(), 3);

        pipeline.enable_importer("dafny");
        assert_eq!(pipeline.enabled_importer_count(), 4);
    }

    #[test]
    fn test_pipeline_import_dafny() {
        let pipeline = make_pipeline();
        let dafny_vc = "\
;; VC: Increment::postcondition::0
;; Method: Increment
;; File: counter.dfy
;; Line: 42
(set-logic ALL)
(assert (=> (>= x 0) (> (+ x 1) 0)))
(check-sat)";

        let results = pipeline.import_all(&[("dafny".to_string(), dafny_vc.to_string())]);
        assert_eq!(results.len(), 1);
        let r = &results[0];
        assert_eq!(r.source, SourceSystem::Dafny);
        assert_eq!(r.name, "Increment::postcondition::0");
        assert_eq!(r.vc_count, 1);
        assert_eq!(r.verified_count, 1);
    }

    #[test]
    fn test_pipeline_import_why3() {
        let pipeline = make_pipeline();
        let session_xml = r#"<?xml version="1.0" encoding="UTF-8"?>
<why3session>
  <file name="test.mlw">
    <theory name="TestTheory">
      <goal name="g1" expl="postcondition" proved="true">
        <proof prover="Z3" time="0.01">
          <result status="valid"/>
        </proof>
      </goal>
    </theory>
  </file>
</why3session>"#;

        let results = pipeline.import_all(&[("why3".to_string(), session_xml.to_string())]);
        assert_eq!(results.len(), 1);
        let r = &results[0];
        assert_eq!(r.source, SourceSystem::Why3);
        assert_eq!(r.name, "TestTheory");
        assert_eq!(r.vc_count, 1);
        assert_eq!(r.verified_count, 1);
    }

    #[test]
    fn test_pipeline_import_fstar() {
        let pipeline = make_pipeline();
        let fstar_mod = "\
(* Module: Test.Mod *)
(* val: f : int -> Tot int verified *)
(* let: f Tot verified *)";

        let results = pipeline.import_all(&[("fstar".to_string(), fstar_mod.to_string())]);
        assert_eq!(results.len(), 1);
        let r = &results[0];
        assert_eq!(r.source, SourceSystem::FStar);
        assert_eq!(r.name, "Test.Mod");
        assert_eq!(r.vc_count, 2);
        assert_eq!(r.verified_count, 2);
        assert!(r.axiom_profile.contains(AxiomProfile::EXTENSIONALITY));
    }

    #[test]
    fn test_pipeline_import_metamath() {
        let pipeline = make_pipeline();
        let mm_db = "\
$( Database: test.mm $)
ax-1 $a |- ( ph -> ( ps -> ph ) ) $.
thm1 $p |- ( ph -> ph ) $= ax-1 ax-1 $.
";

        let results = pipeline.import_all(&[("metamath".to_string(), mm_db.to_string())]);
        assert_eq!(results.len(), 1);
        let r = &results[0];
        assert_eq!(r.source, SourceSystem::Metamath);
        assert_eq!(r.name, "test.mm");
        assert_eq!(r.vc_count, 1);
        assert_eq!(r.verified_count, 1);
    }

    #[test]
    fn test_pipeline_import_unknown_importer() {
        let pipeline = make_pipeline();
        let results = pipeline.import_all(&[("nonexistent".to_string(), "data".to_string())]);
        assert_eq!(results.len(), 1);
        let r = &results[0];
        assert!(r.diagnostics.iter().any(|d| d.contains("no importer")));
    }

    #[test]
    fn test_pipeline_import_disabled_importer() {
        let mut pipeline = make_pipeline();
        pipeline.disable_importer("dafny");

        let results = pipeline.import_all(&[("dafny".to_string(), "(assert true)".to_string())]);
        assert_eq!(results.len(), 1);
        let r = &results[0];
        assert!(r.diagnostics.iter().any(|d| d.contains("disabled")));
    }

    #[test]
    fn test_pipeline_import_error_handling() {
        let pipeline = make_pipeline();
        // Empty input to trigger parse error.
        let results = pipeline.import_all(&[("dafny".to_string(), String::new())]);
        assert_eq!(results.len(), 1);
        let r = &results[0];
        assert!(r.diagnostics.iter().any(|d| d.contains("error")));
    }

    #[test]
    fn test_pipeline_import_multiple() {
        let pipeline = make_pipeline();
        let inputs = vec![
            (
                "fstar".to_string(),
                "(* Module: M1 *)\n(* val: f : int -> Tot int verified *)".to_string(),
            ),
            (
                "metamath".to_string(),
                "$( Database: db1 $)\nax $a |- ph $.\nth $p |- ph $= ax $.".to_string(),
            ),
        ];
        let results = pipeline.import_all(&inputs);
        assert_eq!(results.len(), 2);
        assert_eq!(results[0].source, SourceSystem::FStar);
        assert_eq!(results[1].source, SourceSystem::Metamath);
    }

    #[test]
    fn test_import_result_is_fully_verified() {
        let result = ProgverifImportResult {
            source: SourceSystem::Dafny,
            name: "test".to_string(),
            vc_count: 3,
            verified_count: 3,
            axiom_profile: AxiomProfile::NONE,
            trust_level: TrustLevel::KernelVerified,
            diagnostics: Vec::new(),
        };
        assert!(result.is_fully_verified());
        assert!((result.verification_ratio() - 1.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_import_result_partial_verification_ratio() {
        let result = ProgverifImportResult {
            source: SourceSystem::Why3,
            name: "test".to_string(),
            vc_count: 4,
            verified_count: 2,
            axiom_profile: AxiomProfile::NONE,
            trust_level: TrustLevel::TrustedOracle,
            diagnostics: Vec::new(),
        };
        assert!(!result.is_fully_verified());
        assert!((result.verification_ratio() - 0.5).abs() < f64::EPSILON);
    }

    #[test]
    fn test_import_result_zero_vc_ratio() {
        let result = ProgverifImportResult {
            source: SourceSystem::Dafny,
            name: "empty".to_string(),
            vc_count: 0,
            verified_count: 0,
            axiom_profile: AxiomProfile::NONE,
            trust_level: TrustLevel::TrustedOracle,
            diagnostics: Vec::new(),
        };
        assert!(!result.is_fully_verified());
        assert!((result.verification_ratio() - 0.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_pipeline_stats_from_results() {
        let results = vec![
            ProgverifImportResult {
                source: SourceSystem::Dafny,
                name: "mod1".to_string(),
                vc_count: 5,
                verified_count: 5,
                axiom_profile: AxiomProfile::SMT_ORACLE,
                trust_level: TrustLevel::TrustedOracle,
                diagnostics: Vec::new(),
            },
            ProgverifImportResult {
                source: SourceSystem::FStar,
                name: "mod2".to_string(),
                vc_count: 3,
                verified_count: 2,
                axiom_profile: AxiomProfile::EXTENSIONALITY,
                trust_level: TrustLevel::TrustedOracle,
                diagnostics: Vec::new(),
            },
            ProgverifImportResult {
                source: SourceSystem::Metamath,
                name: "db1".to_string(),
                vc_count: 10,
                verified_count: 10,
                axiom_profile: AxiomProfile::NONE,
                trust_level: TrustLevel::KernelVerified,
                diagnostics: Vec::new(),
            },
        ];

        let stats = PipelineStats::from_results(&results);
        assert_eq!(stats.total_artifacts, 3);
        assert_eq!(stats.total_vc_count, 18);
        assert_eq!(stats.total_verified_count, 17);
        assert_eq!(stats.fully_verified_count, 2);
        assert!(stats
            .combined_axiom_profile
            .contains(AxiomProfile::SMT_ORACLE));
        assert!(stats
            .combined_axiom_profile
            .contains(AxiomProfile::EXTENSIONALITY));
        assert!((stats.verification_ratio() - 17.0 / 18.0).abs() < 0.001);
    }

    #[test]
    fn test_pipeline_stats_empty() {
        let stats = PipelineStats::from_results(&[]);
        assert_eq!(stats.total_artifacts, 0);
        assert_eq!(stats.total_vc_count, 0);
        assert!((stats.verification_ratio() - 0.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_pipeline_default() {
        let pipeline = ProgverifPipeline::default();
        assert_eq!(pipeline.importer_count(), 0);
    }

    #[test]
    fn test_pipeline_with_cert_replay() {
        let mut pipeline = ProgverifPipeline::new().with_cert_replay(true);
        pipeline.register_importer("fstar", SourceSystem::FStar);

        let fstar_mod = "\
(* Module: CertMod *)
(* val: f : int -> Tot int verified *)
(* let: f Tot verified *)";

        let results = pipeline.import_all(&[("fstar".to_string(), fstar_mod.to_string())]);
        assert_eq!(results.len(), 1);
        let r = &results[0];
        // With cert replay + all verified, should get CertificateReplayed.
        assert_eq!(r.trust_level, TrustLevel::CertificateReplayed);
        assert!(r.axiom_profile.contains(AxiomProfile::SAT_CERT));
    }
}
