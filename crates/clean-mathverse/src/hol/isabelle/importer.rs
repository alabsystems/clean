// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Full Isabelle import pipeline.
//!
//! Orchestrates parsing of Isabelle `.yxml` exports, translation to clean
//! kernel expressions, and collection of import statistics including axiom
//! profile summaries.
//!
//! # Architecture
//!
//! The importer combines three lower-level modules:
//!
//! 1. **`yxml_parser`** -- parses raw `.yxml` bytes into `IsaTheoryExport`
//! 2. **`IsabelleTranslator`** -- translates Isabelle types/terms to clean `Expr`
//! 3. **`importer` (this module)** -- orchestrates the pipeline, collects
//!    statistics, and handles errors gracefully
//!
//! # Usage
//!
//! ```text
//! use clean_mathverse::hol::isabelle::importer::{IsabelleImporter, IsabelleImportConfig};
//!
//! let config = IsabelleImportConfig::builder()
//!     .include_proofs(false)
//!     .trust_level(TrustLevel::PartiallyAxiomatized)
//!     .build();
//! let importer = IsabelleImporter::new(config);
//!
//! let result = importer.import_yxml(yxml_content)?;
//! println!("Imported {} theorems", result.statistics.theorems_imported);
//! ```

use std::path::{Path, PathBuf};

use hashbrown::HashMap;
use thiserror::Error;

use super::translate::{IsabelleTranslator, TranslateError, TranslatedTheorem};
use super::types::{IsaTheorem, IsaTheoryExport, ProofStatus};
use super::yxml_parser::{self, YxmlError};
use crate::types::{AxiomProfile, Provenance, SourceSystem, TrustLevel};

// ---------------------------------------------------------------------------
// Error types
// ---------------------------------------------------------------------------

/// Errors that can occur during Isabelle import.
#[derive(Debug, Error)]
#[non_exhaustive]
pub enum IsabelleImportError {
    /// YXML parsing failure.
    #[error("YXML parse error: {0}")]
    YxmlParse(#[from] YxmlError),

    /// Translation failure for a specific theorem.
    #[error("translation error: {0}")]
    Translation(#[from] TranslateError),

    /// I/O error reading a file or directory.
    #[error("I/O error: {}: {source}", path.display())]
    Io {
        path: PathBuf,
        source: std::io::Error,
    },

    /// No `.yxml` files found in the specified directory.
    #[error("no .yxml files found in directory: {}", _0.display())]
    NoYxmlFiles(PathBuf),

    /// Theory export has no theory name.
    #[error("theory export missing name")]
    MissingTheoryName,

    /// A theorem was skipped because its proof status did not meet the
    /// configured trust level.
    #[error("theorem '{name}' skipped: proof status {status:?} below trust level {required:?}")]
    TrustLevelMismatch {
        name: String,
        status: ProofStatus,
        required: TrustLevel,
    },

    /// Multiple errors accumulated during a batch import.
    #[error("{count} errors during import (first: {first})")]
    Batch {
        count: usize,
        first: String,
        errors: Vec<IsabelleImportError>,
    },
}

impl IsabelleImportError {
    /// Wrap an `std::io::Error` with the path that caused it.
    fn io(path: &Path, source: std::io::Error) -> Self {
        Self::Io {
            path: path.to_path_buf(),
            source,
        }
    }
}

// ---------------------------------------------------------------------------
// Configuration
// ---------------------------------------------------------------------------

/// Configuration for the Isabelle import pipeline.
#[derive(Clone, Debug)]
pub struct IsabelleImportConfig {
    /// Directories to search for `.yxml` theory exports.
    pub theory_search_paths: Vec<PathBuf>,
    /// Whether to import theorems with full proof terms (when available).
    pub include_proofs: bool,
    /// Minimum trust level required for import. Theorems below this level
    /// are skipped and counted in `theorems_skipped`.
    pub trust_level: TrustLevel,
    /// Whether to continue importing on individual theorem translation errors
    /// (true) or abort on the first error (false).
    pub continue_on_error: bool,
    /// Optional filter: only import theorems whose names contain this substring.
    pub name_filter: Option<String>,
    /// Maximum number of theorems to import per theory (0 = unlimited).
    pub max_theorems_per_theory: usize,
}

impl Default for IsabelleImportConfig {
    fn default() -> Self {
        Self {
            theory_search_paths: Vec::new(),
            include_proofs: false,
            trust_level: TrustLevel::PartiallyAxiomatized,
            continue_on_error: true,
            name_filter: None,
            max_theorems_per_theory: 0,
        }
    }
}

impl IsabelleImportConfig {
    /// Create a new builder for `IsabelleImportConfig`.
    pub fn builder() -> IsabelleImportConfigBuilder {
        IsabelleImportConfigBuilder::default()
    }
}

/// Builder for `IsabelleImportConfig`.
#[derive(Clone, Debug, Default)]
#[must_use]
pub struct IsabelleImportConfigBuilder {
    config: IsabelleImportConfig,
}

impl IsabelleImportConfigBuilder {
    /// Add a theory search path.
    pub fn theory_search_path(mut self, path: impl Into<PathBuf>) -> Self {
        self.config.theory_search_paths.push(path.into());
        self
    }

    /// Set whether to include proof terms.
    pub fn include_proofs(mut self, include: bool) -> Self {
        self.config.include_proofs = include;
        self
    }

    /// Set the minimum trust level for imported theorems.
    pub fn trust_level(mut self, level: TrustLevel) -> Self {
        self.config.trust_level = level;
        self
    }

    /// Set whether to continue on individual theorem errors.
    pub fn continue_on_error(mut self, cont: bool) -> Self {
        self.config.continue_on_error = cont;
        self
    }

    /// Set a name filter for theorem selection.
    pub fn name_filter(mut self, filter: impl Into<String>) -> Self {
        self.config.name_filter = Some(filter.into());
        self
    }

    /// Set the maximum theorems per theory (0 = unlimited).
    pub fn max_theorems_per_theory(mut self, max: usize) -> Self {
        self.config.max_theorems_per_theory = max;
        self
    }

    /// Build the configuration.
    pub fn build(self) -> IsabelleImportConfig {
        self.config
    }
}

// ---------------------------------------------------------------------------
// Import results
// ---------------------------------------------------------------------------

/// A single imported constant from Isabelle.
#[derive(Clone, Debug)]
pub struct IsaImportedConstant {
    /// The constant's name (fully qualified).
    pub name: String,
    /// The translated theorem ready for Mathverse registration.
    pub translated: TranslatedTheorem,
    /// Provenance tracking for this constant.
    pub provenance: Provenance,
    /// Trust level assigned during import.
    pub trust_level: TrustLevel,
    /// Axiom profile (transitive axiom dependencies).
    pub axiom_profile: AxiomProfile,
}

/// Statistics collected during an Isabelle import run.
#[derive(Clone, Debug, Default)]
pub struct IsabelleStatistics {
    /// Number of theory files processed.
    pub theories_processed: usize,
    /// Number of theorems successfully imported.
    pub theorems_imported: usize,
    /// Number of theorems skipped (trust level, name filter, etc.).
    pub theorems_skipped: usize,
    /// Number of translation errors encountered.
    pub translation_errors: usize,
    /// Summary of axiom profiles across all imported constants.
    pub axiom_profile_summary: HashMap<AxiomProfile, usize>,
    /// Number of constants with each trust level.
    pub trust_level_summary: HashMap<TrustLevelKey, usize>,
    /// Total types declared across all theories.
    pub types_declared: usize,
    /// Total constants declared across all theories.
    pub consts_declared: usize,
    /// Total dependencies (imports) across all theories.
    pub dependencies_count: usize,
    /// Names of theories that were successfully processed.
    pub theory_names: Vec<String>,
}

/// Wrapper for `TrustLevel` that implements `Hash` + `Eq` for use as a
/// `HashMap` key. `TrustLevel` already derives these traits, but we provide
/// a named wrapper for clarity in statistics contexts.
pub type TrustLevelKey = TrustLevel;

impl IsabelleStatistics {
    /// Record a successfully imported constant's axiom profile and trust level.
    fn record_import(&mut self, profile: AxiomProfile, trust: TrustLevel) {
        self.theorems_imported += 1;
        *self.axiom_profile_summary.entry(profile).or_insert(0) += 1;
        *self.trust_level_summary.entry(trust).or_insert(0) += 1;
    }

    /// Record a skipped theorem.
    fn record_skip(&mut self) {
        self.theorems_skipped += 1;
    }

    /// Record a translation error.
    fn record_error(&mut self) {
        self.translation_errors += 1;
    }

    /// Record a theory's structural metadata.
    fn record_theory_metadata(&mut self, export: &IsaTheoryExport) {
        self.theories_processed += 1;
        self.types_declared += export.types.len();
        self.consts_declared += export.consts.len();
        self.dependencies_count += export.dependencies.len();
        self.theory_names.push(export.theory_name.clone());
    }

    /// Merge another statistics block into this one (for directory imports).
    pub fn merge(&mut self, other: &IsabelleStatistics) {
        self.theories_processed += other.theories_processed;
        self.theorems_imported += other.theorems_imported;
        self.theorems_skipped += other.theorems_skipped;
        self.translation_errors += other.translation_errors;
        self.types_declared += other.types_declared;
        self.consts_declared += other.consts_declared;
        self.dependencies_count += other.dependencies_count;
        self.theory_names.extend(other.theory_names.iter().cloned());
        for (&profile, &count) in &other.axiom_profile_summary {
            *self.axiom_profile_summary.entry(profile).or_insert(0) += count;
        }
        for (&trust, &count) in &other.trust_level_summary {
            *self.trust_level_summary.entry(trust).or_insert(0) += count;
        }
    }
}

/// Result of an Isabelle import operation.
#[derive(Debug)]
pub struct IsabelleImportResult {
    /// Successfully imported constants.
    pub constants: Vec<IsaImportedConstant>,
    /// Import statistics.
    pub statistics: IsabelleStatistics,
    /// Non-fatal errors encountered during import.
    pub errors: Vec<IsabelleImportError>,
}

impl IsabelleImportResult {
    /// Create an empty result.
    fn new() -> Self {
        Self {
            constants: Vec::new(),
            statistics: IsabelleStatistics::default(),
            errors: Vec::new(),
        }
    }

    /// Merge another result into this one (for multi-theory imports).
    pub fn merge(&mut self, other: IsabelleImportResult) {
        self.constants.extend(other.constants);
        self.statistics.merge(&other.statistics);
        self.errors.extend(other.errors);
    }

    /// Returns true if there are any imported constants.
    #[must_use]
    pub fn has_constants(&self) -> bool {
        !self.constants.is_empty()
    }

    /// Returns true if there were any errors during import.
    #[must_use]
    pub fn has_errors(&self) -> bool {
        !self.errors.is_empty()
    }

    /// Total number of theorems processed (imported + skipped + errors).
    #[must_use]
    pub fn total_theorems_processed(&self) -> usize {
        self.statistics.theorems_imported
            + self.statistics.theorems_skipped
            + self.statistics.translation_errors
    }
}

// ---------------------------------------------------------------------------
// Importer
// ---------------------------------------------------------------------------

/// Isabelle import pipeline.
///
/// Orchestrates the full flow from `.yxml` bytes or theory export structures
/// through translation and into importable constants with statistics.
pub struct IsabelleImporter {
    config: IsabelleImportConfig,
}

impl IsabelleImporter {
    /// Create a new importer with the given configuration.
    #[must_use]
    pub fn new(config: IsabelleImportConfig) -> Self {
        Self { config }
    }

    /// Create an importer with default configuration.
    #[must_use]
    pub fn with_defaults() -> Self {
        Self::new(IsabelleImportConfig::default())
    }

    /// Get a reference to the importer's configuration.
    #[must_use]
    pub fn config(&self) -> &IsabelleImportConfig {
        &self.config
    }

    // -- Import from `IsaTheoryExport` (pre-parsed) -------------------------

    /// Import a pre-parsed theory export.
    ///
    /// This is the core import method. All other entry points parse their
    /// input into an `IsaTheoryExport` and then delegate here.
    ///
    /// # Errors
    ///
    /// Returns `IsabelleImportError` if `continue_on_error` is `false` and
    /// any theorem translation fails.
    pub fn import_theory(
        &self,
        export: &IsaTheoryExport,
    ) -> Result<IsabelleImportResult, IsabelleImportError> {
        let mut result = IsabelleImportResult::new();
        result.statistics.record_theory_metadata(export);

        let translator = IsabelleTranslator::new(&export.theory_name);

        let theorems = self.filter_theorems(&export.theorems);

        for thm in &theorems {
            match self.import_single_theorem(&translator, thm, &export.theory_name) {
                Ok(Some(constant)) => {
                    result
                        .statistics
                        .record_import(constant.axiom_profile, constant.trust_level);
                    result.constants.push(constant);
                }
                Ok(None) => {
                    // Theorem was skipped (trust level, etc.)
                    result.statistics.record_skip();
                }
                Err(e) => {
                    result.statistics.record_error();
                    if self.config.continue_on_error {
                        result.errors.push(e);
                    } else {
                        return Err(e);
                    }
                }
            }
        }

        // Count theorems filtered out by name_filter/max as skipped.
        let filtered_count = export.theorems.len().saturating_sub(theorems.len());
        for _ in 0..filtered_count {
            result.statistics.record_skip();
        }

        Ok(result)
    }

    // -- Import from YXML bytes / string ------------------------------------

    /// Import from YXML content provided as a string.
    ///
    /// Parses the YXML into an `IsaTheoryExport` and then runs the import
    /// pipeline.
    ///
    /// # Errors
    ///
    /// Returns `IsabelleImportError` on parse or translation failure.
    pub fn import_yxml(
        &self,
        yxml_content: &str,
    ) -> Result<IsabelleImportResult, IsabelleImportError> {
        let export = yxml_parser::parse_theory_export(yxml_content.as_bytes())?;
        self.import_theory(&export)
    }

    /// Import from YXML content provided as bytes.
    ///
    /// # Errors
    ///
    /// Returns `IsabelleImportError` on parse or translation failure.
    pub fn import_yxml_bytes(
        &self,
        yxml_bytes: &[u8],
    ) -> Result<IsabelleImportResult, IsabelleImportError> {
        let export = yxml_parser::parse_theory_export(yxml_bytes)?;
        self.import_theory(&export)
    }

    // -- Import from file system --------------------------------------------

    /// Import from a single `.yxml` file.
    ///
    /// # Errors
    ///
    /// Returns `IsabelleImportError` on I/O, parse, or translation failure.
    pub fn import_file(&self, path: &Path) -> Result<IsabelleImportResult, IsabelleImportError> {
        let bytes = std::fs::read(path).map_err(|e| IsabelleImportError::io(path, e))?;
        self.import_yxml_bytes(&bytes)
    }

    /// Import all `.yxml` files in a directory (non-recursive).
    ///
    /// Each file is imported independently and results are merged. Errors in
    /// individual files are collected into `result.errors` when
    /// `continue_on_error` is true.
    ///
    /// # Errors
    ///
    /// Returns `IsabelleImportError` if the directory cannot be read, or if
    /// no `.yxml` files are found, or if `continue_on_error` is false and
    /// any file fails.
    pub fn import_directory(
        &self,
        dir: &Path,
    ) -> Result<IsabelleImportResult, IsabelleImportError> {
        let entries = std::fs::read_dir(dir).map_err(|e| IsabelleImportError::io(dir, e))?;

        let mut yxml_paths: Vec<PathBuf> = Vec::new();
        for entry in entries {
            let entry = entry.map_err(|e| IsabelleImportError::io(dir, e))?;
            let path = entry.path();
            if path.extension().and_then(|e| e.to_str()) == Some("yxml") {
                yxml_paths.push(path);
            }
        }

        if yxml_paths.is_empty() {
            return Err(IsabelleImportError::NoYxmlFiles(dir.to_path_buf()));
        }

        // Sort for deterministic ordering.
        yxml_paths.sort();

        let mut combined = IsabelleImportResult::new();

        for path in &yxml_paths {
            match self.import_file(path) {
                Ok(file_result) => {
                    combined.merge(file_result);
                }
                Err(e) => {
                    if self.config.continue_on_error {
                        combined.errors.push(e);
                    } else {
                        return Err(e);
                    }
                }
            }
        }

        Ok(combined)
    }

    /// Import from all configured theory search paths.
    ///
    /// Iterates over `config.theory_search_paths` and imports from each
    /// directory. Results are merged across all directories.
    ///
    /// # Errors
    ///
    /// Returns `IsabelleImportError` if any directory fails and
    /// `continue_on_error` is false.
    pub fn import_all_search_paths(&self) -> Result<IsabelleImportResult, IsabelleImportError> {
        let mut combined = IsabelleImportResult::new();

        for path in &self.config.theory_search_paths {
            match self.import_directory(path) {
                Ok(dir_result) => {
                    combined.merge(dir_result);
                }
                Err(e) => {
                    if self.config.continue_on_error {
                        combined.errors.push(e);
                    } else {
                        return Err(e);
                    }
                }
            }
        }

        Ok(combined)
    }

    // -- Internal helpers ---------------------------------------------------

    /// Filter theorems according to config (name filter, max count).
    fn filter_theorems<'a>(&self, theorems: &'a [IsaTheorem]) -> Vec<&'a IsaTheorem> {
        let mut filtered: Vec<&IsaTheorem> = theorems.iter().collect();

        // Apply name filter.
        if let Some(ref filter) = self.config.name_filter {
            filtered.retain(|thm| thm.name.contains(filter.as_str()));
        }

        // Apply max count.
        if self.config.max_theorems_per_theory > 0 {
            filtered.truncate(self.config.max_theorems_per_theory);
        }

        filtered
    }

    /// Import a single theorem, returning `None` if it should be skipped.
    fn import_single_theorem(
        &self,
        translator: &IsabelleTranslator,
        thm: &IsaTheorem,
        theory_name: &str,
    ) -> Result<Option<IsaImportedConstant>, IsabelleImportError> {
        // Check trust level: skip axiomatized theorems if config requires proved.
        let thm_trust = match thm.proof_status {
            ProofStatus::Proved => TrustLevel::CertificateReplayed,
            ProofStatus::Axiomatized => TrustLevel::PartiallyAxiomatized,
        };

        if thm_trust > self.config.trust_level {
            return Ok(None);
        }

        // Translate via the existing translator.
        let translated = translator.translate_theorem(thm)?;

        let constant = IsaImportedConstant {
            name: translated.name.clone(),
            provenance: Provenance {
                source: SourceSystem::Isabelle,
                original_name: thm.name.clone(),
                source_file: Some(format!("{theory_name}.thy")),
                axiom_profile: translated.axiom_profile,
            },
            trust_level: translated.trust_level,
            axiom_profile: translated.axiom_profile,
            translated,
        };

        Ok(Some(constant))
    }
}

// ---------------------------------------------------------------------------
// Convenience functions
// ---------------------------------------------------------------------------

/// Import a single theory export with default configuration.
///
/// This is a convenience wrapper around `IsabelleImporter::with_defaults()`.
///
/// # Errors
///
/// Returns `IsabelleImportError` on translation failure.
pub fn import_theory_default(
    export: &IsaTheoryExport,
) -> Result<IsabelleImportResult, IsabelleImportError> {
    let importer = IsabelleImporter::with_defaults();
    importer.import_theory(export)
}

/// Import from YXML content with default configuration.
///
/// # Errors
///
/// Returns `IsabelleImportError` on parse or translation failure.
pub fn import_yxml_default(
    yxml_content: &str,
) -> Result<IsabelleImportResult, IsabelleImportError> {
    let importer = IsabelleImporter::with_defaults();
    importer.import_yxml(yxml_content)
}
