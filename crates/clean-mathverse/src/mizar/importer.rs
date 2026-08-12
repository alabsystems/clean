// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Article-level Mizar importer: parses XML, translates to kernel constants.
//!
//! [`MizarImporter`] is the high-level entry point for importing an entire
//! Mizar article (or a fragment thereof) from the `mizar-items` XML export
//! format. It wraps the XML parser and FOL-to-DTT translation, producing
//! [`MizImportedConstant`] records with axiom profiles and trust metadata.

use super::translate::{translate_article_item, MizTranslateError, MizTranslationContext};
use super::xml_parser::parse_article;
#[cfg(test)]
use crate::types::SourceSystem;
use crate::types::{AxiomProfile, Provenance, TrustLevel};
use clean_kernel::Expr;
use thiserror::Error;

// ════════════════════════════════════════════════════════════════════════════
// Configuration
// ════════════════════════════════════════════════════════════════════════════

/// Configuration for a Mizar article import.
#[derive(Clone, Debug)]
pub struct MizarImportConfig {
    /// Whether to translate proof objects (when available).
    pub translate_proofs: bool,
    /// Whether to axiomatize items that lack proofs (theorems without proof blocks).
    pub axiomatize_unproved: bool,
}

impl Default for MizarImportConfig {
    fn default() -> Self {
        Self {
            translate_proofs: false,
            axiomatize_unproved: true,
        }
    }
}

// ════════════════════════════════════════════════════════════════════════════
// Imported constant kinds
// ════════════════════════════════════════════════════════════════════════════

/// Kind of a Mizar imported constant.
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum MizConstantKind {
    /// A proved or axiomatized theorem.
    Theorem,
    /// A mode, functor, predicate, attribute, or structure definition.
    Definition,
    /// A second-order scheme.
    Scheme,
    /// A cluster registration (existential, conditional, or functorial).
    Registration,
    /// A notation declaration (synonym or antonym).
    Notation,
}

// ════════════════════════════════════════════════════════════════════════════
// Imported constant
// ════════════════════════════════════════════════════════════════════════════

/// A single constant produced by importing a Mizar article item.
#[derive(Clone, Debug)]
pub struct MizImportedConstant {
    /// clean-facing name for this constant (e.g., `Mizar.XBOOLE_0.T1`).
    pub name: String,
    /// String representation of the translated type expression.
    pub type_expr: String,
    /// Kernel type expression for shard serialization.
    ///
    /// Populated when the translation produces a proper kernel `Expr`.
    /// Used by the mathverse_convert shard writer to emit FlatExpr records.
    pub kernel_type_expr: Option<Expr>,
    /// What kind of Mizar item this came from.
    pub kind: MizConstantKind,
    /// Axiom profile for this constant.
    pub axiom_profile: AxiomProfile,
    /// Trust level assigned to this constant.
    pub trust_level: TrustLevel,
    /// Full provenance record.
    pub provenance: Provenance,
}

// ════════════════════════════════════════════════════════════════════════════
// Import result
// ════════════════════════════════════════════════════════════════════════════

/// Result of importing a complete Mizar article.
#[derive(Clone, Debug)]
pub struct MizarImportResult {
    /// Name of the imported article (e.g., `XBOOLE_0`).
    pub article_name: String,
    /// All constants produced from this article.
    pub constants: Vec<MizImportedConstant>,
    /// Number of theorem items translated.
    pub theorem_count: usize,
    /// Number of definition items translated.
    pub definition_count: usize,
    /// Number of items that were axiomatized (no proof available).
    pub axiomatized_count: usize,
    /// Diagnostic messages collected during import (warnings, skipped items).
    pub diagnostics: Vec<String>,
}

impl MizarImportResult {
    /// Total number of constants produced.
    #[must_use]
    pub fn total_constants(&self) -> usize {
        self.constants.len()
    }

    /// Number of constants that are kernel-verified (no axiom dependencies).
    #[must_use]
    pub fn kernel_verified_count(&self) -> usize {
        self.constants
            .iter()
            .filter(|c| c.axiom_profile.is_kernel_verified())
            .count()
    }

    /// Number of constants that are partially axiomatized.
    #[must_use]
    pub fn partially_axiomatized_count(&self) -> usize {
        self.constants
            .iter()
            .filter(|c| c.trust_level == TrustLevel::PartiallyAxiomatized)
            .count()
    }

    /// Whether the import produced any diagnostics.
    #[must_use]
    pub fn has_diagnostics(&self) -> bool {
        !self.diagnostics.is_empty()
    }
}

// ════════════════════════════════════════════════════════════════════════════
// Importer
// ════════════════════════════════════════════════════════════════════════════

/// High-level Mizar article importer.
///
/// Parses the `mizar-items` XML for an article, translates each item to a
/// Clean kernel constant, and collects trust/axiom metadata.
pub struct MizarImporter {
    /// Name of the article being imported.
    article_name: String,
    /// Import configuration.
    config: MizarImportConfig,
}

impl MizarImporter {
    /// Create a new importer for the given article.
    #[must_use]
    pub fn new(article_name: &str, config: MizarImportConfig) -> Self {
        Self {
            article_name: article_name.to_owned(),
            config,
        }
    }

    /// Create a new importer with default configuration.
    #[must_use]
    pub fn with_defaults(article_name: &str) -> Self {
        Self::new(article_name, MizarImportConfig::default())
    }

    /// The article name this importer is configured for.
    #[must_use]
    pub fn article_name(&self) -> &str {
        &self.article_name
    }

    /// Import a Mizar article from its XML representation.
    ///
    /// Parses the XML, translates each article item, and collects all
    /// constants with their trust metadata.
    ///
    /// # Errors
    ///
    /// Returns `MizTranslateError` if XML parsing or translation fails
    /// on a required item.
    pub fn import_article_xml(&self, xml: &str) -> Result<MizarImportResult, MizTranslateError> {
        let article = parse_article(xml).map_err(|e| MizTranslateError::Unsupported {
            desc: format!("XML parse error: {e}"),
        })?;

        let mut ctx = MizTranslationContext::new();
        let mut constants = Vec::new();
        let mut diagnostics = Vec::new();
        let mut theorem_count = 0usize;
        let mut definition_count = 0usize;
        let mut axiomatized_count = 0usize;

        let effective_article_name = if article.name.is_empty() {
            &self.article_name
        } else {
            &article.name
        };

        for (idx, item) in article.items.iter().enumerate() {
            match translate_article_item(&mut ctx, item, effective_article_name, &self.config) {
                Ok(Some(imported)) => {
                    match imported.kind {
                        MizConstantKind::Theorem => theorem_count += 1,
                        MizConstantKind::Definition => definition_count += 1,
                        _ => {}
                    }
                    if imported.trust_level == TrustLevel::PartiallyAxiomatized {
                        axiomatized_count += 1;
                    }
                    constants.push(imported);
                }
                Ok(None) => {
                    diagnostics.push(format!("item {idx}: skipped (notation or unsupported)"));
                }
                Err(e) => {
                    diagnostics.push(format!("item {idx}: translation error: {e}"));
                }
            }
        }

        Ok(MizarImportResult {
            article_name: effective_article_name.to_owned(),
            constants,
            theorem_count,
            definition_count,
            axiomatized_count,
            diagnostics,
        })
    }
}

// ════════════════════════════════════════════════════════════════════════════
// Import error (thiserror)
// ════════════════════════════════════════════════════════════════════════════

/// Errors that can occur during Mizar article import.
#[derive(Debug, Error)]
#[non_exhaustive]
pub enum MizarImportError {
    /// XML parsing failed.
    #[error("parse error: {0}")]
    ParseError(#[from] super::xml_parser::MizXmlError),
    /// Translation from Mizar FOL to clean DTT failed.
    #[error("translation error: {0}")]
    TranslationError(#[from] MizTranslateError),
    /// I/O error (e.g., reading XML files from disk).
    #[error("I/O error: {0}")]
    IoError(#[from] std::io::Error),
    /// Article XML is not valid Mizar format.
    #[error("invalid article format: {detail}")]
    InvalidFormat { detail: String },
}

// ════════════════════════════════════════════════════════════════════════════
// Import report (per-article statistics)
// ════════════════════════════════════════════════════════════════════════════

/// Per-article import statistics.
#[derive(Clone, Debug, Default)]
pub struct MizarImportReport {
    /// Name of the article.
    pub article_name: String,
    /// Total items encountered.
    pub total_items: usize,
    /// Number of theorems imported.
    pub theorems_imported: usize,
    /// Number of definitions imported.
    pub definitions_imported: usize,
    /// Number of schemes imported.
    pub schemes_imported: usize,
    /// Number of registrations imported.
    pub registrations_imported: usize,
    /// Number of items axiomatized (no proof).
    pub axiomatized: usize,
    /// Number of items skipped (unsupported or malformed).
    pub skipped: usize,
    /// Number of items that produced translation errors.
    pub errors: usize,
    /// Diagnostic messages.
    pub diagnostics: Vec<String>,
}

impl MizarImportReport {
    /// Total constants produced (successful imports).
    #[must_use]
    pub fn constants_produced(&self) -> usize {
        self.theorems_imported
            + self.definitions_imported
            + self.schemes_imported
            + self.registrations_imported
    }

    /// Whether all items were successfully imported.
    #[must_use]
    pub fn is_complete(&self) -> bool {
        self.errors == 0 && self.skipped == 0
    }

    /// Human-readable summary.
    #[must_use]
    pub fn summary(&self) -> String {
        format!(
            "{}: {} items, {} imported ({} thm, {} def, {} sch, {} reg), {} axiomatized, {} skipped, {} errors",
            self.article_name,
            self.total_items,
            self.constants_produced(),
            self.theorems_imported,
            self.definitions_imported,
            self.schemes_imported,
            self.registrations_imported,
            self.axiomatized,
            self.skipped,
            self.errors,
        )
    }
}

// ════════════════════════════════════════════════════════════════════════════
// Batch import report
// ════════════════════════════════════════════════════════════════════════════

/// Report for a batch import of multiple articles.
#[derive(Clone, Debug, Default)]
pub struct MizarBatchImportReport {
    /// Per-article reports.
    pub articles: Vec<MizarImportReport>,
    /// Articles that failed to parse at all.
    pub failed_articles: Vec<(String, String)>,
    /// Total constants produced across all articles.
    pub total_constants: usize,
    /// Total errors across all articles.
    pub total_errors: usize,
}

impl MizarBatchImportReport {
    /// Number of articles successfully imported (at least partially).
    #[must_use]
    pub fn articles_imported(&self) -> usize {
        self.articles.len()
    }

    /// Number of articles that completely failed.
    #[must_use]
    pub fn articles_failed(&self) -> usize {
        self.failed_articles.len()
    }

    /// Whether all articles were imported without any errors.
    #[must_use]
    pub fn is_clean(&self) -> bool {
        self.total_errors == 0 && self.failed_articles.is_empty()
    }

    /// Human-readable summary of the batch.
    #[must_use]
    pub fn summary(&self) -> String {
        format!(
            "Batch import: {} articles ({} failed), {} total constants, {} total errors",
            self.articles.len(),
            self.failed_articles.len(),
            self.total_constants,
            self.total_errors,
        )
    }
}

// ════════════════════════════════════════════════════════════════════════════
// Extended importer methods
// ════════════════════════════════════════════════════════════════════════════

impl MizarImporter {
    /// Import a Mizar article from XML with a detailed import report.
    ///
    /// This is similar to [`import_article_xml`] but returns a [`MizarImportReport`]
    /// with richer per-category statistics.
    pub fn import_article_with_report(
        &self,
        xml: &str,
    ) -> Result<(MizarImportResult, MizarImportReport), MizarImportError> {
        let result = self
            .import_article_xml(xml)
            .map_err(MizarImportError::TranslationError)?;

        let mut report = MizarImportReport {
            article_name: result.article_name.clone(),
            total_items: result.constants.len() + result.diagnostics.len(),
            theorems_imported: result.theorem_count,
            definitions_imported: result.definition_count,
            axiomatized: result.axiomatized_count,
            diagnostics: result.diagnostics.clone(),
            ..MizarImportReport::default()
        };

        // Count schemes and registrations from the constants.
        for c in &result.constants {
            match c.kind {
                MizConstantKind::Scheme => report.schemes_imported += 1,
                MizConstantKind::Registration => report.registrations_imported += 1,
                _ => {}
            }
        }

        // Count errors and skips from diagnostics.
        for diag in &result.diagnostics {
            if diag.contains("error") {
                report.errors += 1;
            } else {
                report.skipped += 1;
            }
        }

        Ok((result, report))
    }

    /// Import a Mizar article from a file path.
    ///
    /// Reads the file, then delegates to [`import_article_xml`].
    pub fn import_article_file(
        &self,
        path: &std::path::Path,
    ) -> Result<MizarImportResult, MizarImportError> {
        let xml = std::fs::read_to_string(path)?;
        self.import_article_xml(&xml)
            .map_err(MizarImportError::TranslationError)
    }

    /// Import all `.xml` files from a directory.
    ///
    /// Iterates over directory entries, imports each `.xml` file as a Mizar
    /// article, and collects results and a batch report.
    pub fn import_directory(
        &self,
        dir: &std::path::Path,
    ) -> Result<(Vec<MizarImportResult>, MizarBatchImportReport), MizarImportError> {
        let mut results = Vec::new();
        let mut batch = MizarBatchImportReport::default();

        let entries = std::fs::read_dir(dir)?;

        for entry in entries {
            let entry = entry?;
            let path = entry.path();

            // Only process .xml files.
            let is_xml = path.extension().is_some_and(|ext| ext == "xml");
            if !is_xml {
                continue;
            }

            let file_name = path
                .file_stem()
                .and_then(|s| s.to_str())
                .unwrap_or("unknown")
                .to_owned();

            match self.import_article_file(&path) {
                Ok(result) => {
                    let report = MizarImportReport {
                        article_name: result.article_name.clone(),
                        total_items: result.constants.len() + result.diagnostics.len(),
                        theorems_imported: result.theorem_count,
                        definitions_imported: result.definition_count,
                        axiomatized: result.axiomatized_count,
                        errors: result
                            .diagnostics
                            .iter()
                            .filter(|d| d.contains("error"))
                            .count(),
                        skipped: result
                            .diagnostics
                            .iter()
                            .filter(|d| !d.contains("error"))
                            .count(),
                        diagnostics: result.diagnostics.clone(),
                        ..MizarImportReport::default()
                    };
                    batch.total_constants += result.constants.len();
                    batch.total_errors += report.errors;
                    batch.articles.push(report);
                    results.push(result);
                }
                Err(e) => {
                    batch.failed_articles.push((file_name, format!("{e}")));
                    batch.total_errors += 1;
                }
            }
        }

        Ok((results, batch))
    }

    /// Validate an XML string as a Mizar article without performing full import.
    ///
    /// Returns `Ok(article_name)` if the XML parses as a valid article,
    /// or an error describing why it fails.
    pub fn validate_article_xml(xml: &str) -> Result<String, MizarImportError> {
        let article = parse_article(xml).map_err(MizarImportError::ParseError)?;
        if article.name.is_empty() {
            return Err(MizarImportError::InvalidFormat {
                detail: "article has empty aid attribute".to_owned(),
            });
        }
        Ok(article.name)
    }

    /// Get the environment dependencies of an article XML without importing.
    ///
    /// Useful for dependency resolution before committing to a full import.
    pub fn article_dependencies(xml: &str) -> Result<Vec<String>, MizarImportError> {
        let article = parse_article(xml).map_err(MizarImportError::ParseError)?;
        Ok(article.environ.all_dependencies())
    }
}

// ════════════════════════════════════════════════════════════════════════════
// Tests
// ════════════════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_import_empty_article() {
        let importer = MizarImporter::with_defaults("TEST");
        let xml = r#"<Article aid="TEST"/>"#;
        let result = importer
            .import_article_xml(xml)
            .expect("should import empty article");
        assert_eq!(result.article_name, "TEST");
        assert!(result.constants.is_empty());
        assert_eq!(result.theorem_count, 0);
        assert_eq!(result.definition_count, 0);
        assert_eq!(result.axiomatized_count, 0);
        assert_eq!(result.total_constants(), 0);
    }

    #[test]
    fn test_import_article_with_theorem() {
        let importer = MizarImporter::with_defaults("TEST");
        let xml = r#"<Article aid="TEST">
  <Theorem nr="1">
    <For vid="x1">
      <Typ kind="M" nr="1"/>
      <Pred kind="R" nr="1"><Var nr="1"/></Pred>
    </For>
  </Theorem>
</Article>"#;
        let result = importer
            .import_article_xml(xml)
            .expect("should import article");
        assert_eq!(result.article_name, "TEST");
        assert_eq!(result.theorem_count, 1);
        assert_eq!(result.total_constants(), 1);
        let c = &result.constants[0];
        assert_eq!(c.kind, MizConstantKind::Theorem);
        assert!(c.name.contains("TEST"));
        assert_eq!(c.provenance.source, SourceSystem::Mizar);
    }

    #[test]
    fn test_import_axiomatized_theorem() {
        let config = MizarImportConfig {
            translate_proofs: false,
            axiomatize_unproved: true,
        };
        let importer = MizarImporter::new("AX", config);
        let xml = r#"<Article aid="AX">
  <Theorem nr="1">
    <Pred kind="R" nr="1"/>
  </Theorem>
</Article>"#;
        let result = importer.import_article_xml(xml).expect("should import");
        assert_eq!(result.axiomatized_count, 1);
        let c = &result.constants[0];
        assert_eq!(c.trust_level, TrustLevel::PartiallyAxiomatized);
        assert!(c.axiom_profile.contains(AxiomProfile::MIZAR_SOFT_TYPE));
    }

    #[test]
    fn test_import_config_defaults() {
        let config = MizarImportConfig::default();
        assert!(!config.translate_proofs);
        assert!(config.axiomatize_unproved);
    }

    #[test]
    fn test_import_result_diagnostics() {
        let importer = MizarImporter::with_defaults("TEST");
        let xml = r#"<Article aid="TEST"/>"#;
        let result = importer.import_article_xml(xml).expect("should import");
        assert!(!result.has_diagnostics());
    }

    #[test]
    fn test_import_constant_kinds() {
        assert_ne!(MizConstantKind::Theorem, MizConstantKind::Definition);
        assert_ne!(MizConstantKind::Scheme, MizConstantKind::Registration);
        assert_ne!(MizConstantKind::Notation, MizConstantKind::Theorem);
    }

    #[test]
    fn test_import_article_name_from_xml() {
        let importer = MizarImporter::with_defaults("FALLBACK");
        let xml = r#"<Article aid="FROMXML"/>"#;
        let result = importer.import_article_xml(xml).expect("should import");
        // Article name should come from XML when present.
        assert_eq!(result.article_name, "FROMXML");
    }

    #[test]
    fn test_import_article_name_fallback() {
        let importer = MizarImporter::with_defaults("FALLBACK");
        let xml = r#"<Article aid=""/>"#;
        let result = importer.import_article_xml(xml).expect("should import");
        // Empty aid in XML => use importer's article_name.
        assert_eq!(result.article_name, "FALLBACK");
    }

    #[test]
    fn test_import_invalid_xml_returns_error() {
        let importer = MizarImporter::with_defaults("TEST");
        let xml = r#"<Invalid>"#;
        let result = importer.import_article_xml(xml);
        assert!(result.is_err());
    }

    #[test]
    fn test_import_result_kernel_verified_count() {
        let importer = MizarImporter::with_defaults("TEST");
        let xml = r#"<Article aid="TEST"/>"#;
        let result = importer.import_article_xml(xml).expect("should import");
        assert_eq!(result.kernel_verified_count(), 0);
    }

    #[test]
    fn test_import_result_partially_axiomatized_count() {
        let config = MizarImportConfig {
            translate_proofs: false,
            axiomatize_unproved: true,
        };
        let importer = MizarImporter::new("TEST", config);
        let xml = r#"<Article aid="TEST">
  <Theorem nr="1"><Pred kind="R" nr="1"/></Theorem>
  <Theorem nr="2"><Pred kind="R" nr="2"/></Theorem>
</Article>"#;
        let result = importer.import_article_xml(xml).expect("should import");
        assert_eq!(result.partially_axiomatized_count(), 2);
    }
}
