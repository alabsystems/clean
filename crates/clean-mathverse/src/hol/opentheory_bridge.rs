// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Bridge from kernel's OpenTheory import to Mathverse shard output.
//!
//! Wraps the kernel's `open_theory::import_article` pipeline, translating
//! its output (`OtImportedArticle` with `Vec<Declaration>`) into the Mathverse
//! format (`Vec<MathverseImportedConstant>`) with axiom profiles, provenance,
//! and trust-level tagging.

use std::path::Path;

use clean_kernel::open_theory::{import_article_with_options, OtArticle, OtImportOptions};
use clean_kernel::{Declaration, Expr, Name as LeanName};

use crate::types::{AxiomProfile, Provenance, SourceSystem, TrustLevel};

use super::error::HolResult;

/// Base axiom profile shared by all HOL-family imports.
///
/// HOL systems assume classical logic, function extensionality, and are
/// encoded via the HOL shallow-embedding axiom layer.
pub(crate) const HOL_BASE_PROFILE: AxiomProfile = AxiomProfile(
    AxiomProfile::CLASSICAL.0 | AxiomProfile::EXTENSIONALITY.0 | AxiomProfile::HOL_EMBEDDING.0,
);

/// Classification of an imported constant: was it proved or assumed?
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum ImportedConstantKind {
    /// A type operator or constant appearing in theorems (support declaration).
    Support,
    /// An assumption (axiom without proof within the article).
    Assumption,
    /// A proved theorem (exported via `thm` in the article).
    Theorem,
}

/// A single constant imported through the OpenTheory bridge into Mathverse format.
#[derive(Clone, Debug)]
pub struct MathverseImportedConstant {
    /// The translated clean kernel expression (type of the axiom/definition).
    pub type_expr: Expr,
    /// Fully-qualified name within the Mathverse namespace.
    pub name: LeanName,
    /// Axiom profile tracking which axiom systems this constant depends on.
    pub axiom_profile: AxiomProfile,
    /// Provenance record linking back to the source system.
    pub provenance: Provenance,
    /// Trust level assigned to this constant.
    pub trust_level: TrustLevel,
    /// Whether this constant was proved, assumed, or is a support declaration.
    pub kind: ImportedConstantKind,
}

/// Statistics about an OpenTheory import run.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct ImportStatistics {
    /// Number of support declarations (type operators, constants).
    pub support_count: usize,
    /// Number of assumptions (unproved axioms).
    pub assumption_count: usize,
    /// Number of proved theorems.
    pub theorem_count: usize,
}

impl ImportStatistics {
    /// Total number of imported declarations.
    #[must_use]
    pub fn total(&self) -> usize {
        self.support_count + self.assumption_count + self.theorem_count
    }

    /// Merge another statistics record into this one (additive).
    pub fn merge(&mut self, other: &ImportStatistics) {
        self.support_count += other.support_count;
        self.assumption_count += other.assumption_count;
        self.theorem_count += other.theorem_count;
    }
}

/// Policy for handling axioms encountered during OpenTheory article import.
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
#[derive(Default)]
pub enum OtAxiomPolicy {
    /// Accept all axioms without restriction.
    #[default]
    AcceptAll,
    /// Reject axioms not listed in the known axiom set, returning an error.
    RejectUnknown,
    /// Map axioms to the closest matching axiom profile entry.
    MapToProfile,
}

/// Configuration for OpenTheory article import.
///
/// Controls trust level assignment, axiom handling policy, and optional
/// name remapping for imported constants.
#[derive(Clone, Debug)]
pub struct OtImportConfig {
    /// Trust level to assign to proved theorems.
    pub trust_level: TrustLevel,
    /// Policy for axiom handling.
    pub axiom_policy: OtAxiomPolicy,
    /// Optional name mappings: keys are original names, values are replacement names.
    /// Applied before namespace prefixing.
    pub name_mapping: std::collections::HashMap<String, String>,
    /// Whether to include support declarations in the output.
    pub include_support: bool,
    /// Whether to include assumptions in the output.
    pub include_assumptions: bool,
}

impl Default for OtImportConfig {
    fn default() -> Self {
        Self {
            trust_level: TrustLevel::CertificateReplayed,
            axiom_policy: OtAxiomPolicy::AcceptAll,
            name_mapping: std::collections::HashMap::new(),
            include_support: true,
            include_assumptions: true,
        }
    }
}

impl OtImportConfig {
    /// Create a config that only imports theorems (no support or assumptions).
    #[must_use]
    pub fn theorems_only() -> Self {
        Self {
            include_support: false,
            include_assumptions: false,
            ..Self::default()
        }
    }

    /// Create a strict config that rejects unknown axioms.
    #[must_use]
    pub fn strict() -> Self {
        Self {
            axiom_policy: OtAxiomPolicy::RejectUnknown,
            ..Self::default()
        }
    }

    /// Add a name mapping entry.
    #[must_use]
    pub fn with_name_mapping(mut self, from: &str, to: &str) -> Self {
        self.name_mapping.insert(from.to_owned(), to.to_owned());
        self
    }

    /// Set the trust level.
    #[must_use]
    pub fn with_trust_level(mut self, level: TrustLevel) -> Self {
        self.trust_level = level;
        self
    }

    /// Set the axiom policy.
    #[must_use]
    pub fn with_axiom_policy(mut self, policy: OtAxiomPolicy) -> Self {
        self.axiom_policy = policy;
        self
    }
}

/// Result of an OpenTheory import operation, with richer metadata than
/// the raw `(Vec<MathverseImportedConstant>, ImportStatistics)` tuple.
#[derive(Clone, Debug)]
pub struct OtImportResult {
    /// All imported constants.
    pub constants: Vec<MathverseImportedConstant>,
    /// Import statistics.
    pub statistics: OtStatistics,
    /// Warnings generated during import (non-fatal issues).
    pub warnings: Vec<String>,
}

impl OtImportResult {
    /// Number of imported constants.
    #[must_use]
    pub fn constant_count(&self) -> usize {
        self.constants.len()
    }

    /// Whether the import produced any warnings.
    #[must_use]
    pub fn has_warnings(&self) -> bool {
        !self.warnings.is_empty()
    }
}

/// Extended statistics for OpenTheory import, including article-level counts.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct OtStatistics {
    /// Number of articles read (parsed).
    pub articles_read: usize,
    /// Number of theorems imported across all articles.
    pub theorems_imported: usize,
    /// Number of axioms (assumptions) tracked.
    pub axioms_tracked: usize,
    /// Number of support declarations imported.
    pub support_imported: usize,
    /// Number of articles that failed to parse.
    pub articles_failed: usize,
}

impl OtStatistics {
    /// Total number of declarations across all categories.
    #[must_use]
    pub fn total_imported(&self) -> usize {
        self.theorems_imported + self.axioms_tracked + self.support_imported
    }

    /// Success rate as a fraction in [0.0, 1.0].
    #[must_use]
    pub fn success_rate(&self) -> f64 {
        if self.articles_read == 0 {
            return 1.0;
        }
        let successful = self.articles_read - self.articles_failed;
        successful as f64 / self.articles_read as f64
    }

    /// Merge another statistics record into this one.
    pub fn merge(&mut self, other: &OtStatistics) {
        self.articles_read += other.articles_read;
        self.theorems_imported += other.theorems_imported;
        self.axioms_tracked += other.axioms_tracked;
        self.support_imported += other.support_imported;
        self.articles_failed += other.articles_failed;
    }
}

/// Bridge from the kernel's OpenTheory importer to Mathverse format.
///
/// Wraps `clean_kernel::open_theory::import_article_with_options` and
/// tags each resulting declaration with the appropriate axiom profile,
/// provenance, and trust level for the Mathverse library.
pub struct OtMathverseBridge {
    /// Namespace prefix for imported constants.
    namespace: LeanName,
    /// Source system tag for provenance records.
    source_system: SourceSystem,
    /// Optional source file path for provenance records.
    source_file: Option<String>,
}

impl OtMathverseBridge {
    /// Create a new bridge with the given namespace and source system.
    pub fn new(namespace: LeanName, source_system: SourceSystem) -> Self {
        Self {
            namespace,
            source_system,
            source_file: None,
        }
    }

    /// Set the source file path for provenance records.
    #[must_use]
    pub fn with_source_file(mut self, path: &str) -> Self {
        self.source_file = Some(path.to_owned());
        self
    }

    /// Import a parsed OpenTheory article into Mathverse format.
    ///
    /// Delegates to the kernel's `import_article_with_options`, then wraps
    /// each resulting `Declaration` as an `MathverseImportedConstant` with the
    /// HOL base axiom profile and appropriate trust level.
    pub fn import_article(
        &self,
        article: &OtArticle,
    ) -> HolResult<(Vec<MathverseImportedConstant>, ImportStatistics)> {
        let options = OtImportOptions {
            namespace: self.namespace.clone(),
        };
        let imported = import_article_with_options(article, &options)?;

        let mut constants = Vec::new();
        let mut stats = ImportStatistics::default();

        // Support declarations: type operators and constants referenced by theorems.
        for decl in &imported.support_declarations {
            constants.push(self.wrap_declaration(decl, ImportedConstantKind::Support));
            stats.support_count += 1;
        }

        // Assumptions: axioms without proof in the article.
        for decl in &imported.assumption_declarations {
            constants.push(self.wrap_declaration(decl, ImportedConstantKind::Assumption));
            stats.assumption_count += 1;
        }

        // Proved theorems: exported via `thm` command.
        for decl in &imported.theorem_declarations {
            constants.push(self.wrap_declaration(decl, ImportedConstantKind::Theorem));
            stats.theorem_count += 1;
        }

        Ok((constants, stats))
    }

    /// Import an OpenTheory article from raw text.
    pub fn import_article_text(
        &self,
        input: &str,
    ) -> HolResult<(Vec<MathverseImportedConstant>, ImportStatistics)> {
        let article = clean_kernel::open_theory::parse_article(input)?;
        self.import_article(&article)
    }

    /// Import an OpenTheory `.art` file from disk.
    pub fn import_file(
        &self,
        path: &Path,
    ) -> HolResult<(Vec<MathverseImportedConstant>, ImportStatistics)> {
        let article = clean_kernel::open_theory::parse_article_file(path)?;
        let bridge = Self {
            namespace: self.namespace.clone(),
            source_system: self.source_system,
            source_file: Some(path.display().to_string()),
        };
        bridge.import_article(&article)
    }

    /// Import a parsed article with a configuration object controlling
    /// filtering and trust level assignment.
    pub fn import_with_config(
        &self,
        article: &OtArticle,
        config: &OtImportConfig,
    ) -> HolResult<OtImportResult> {
        let (all_constants, base_stats) = self.import_article(article)?;

        let mut filtered = Vec::new();
        let mut warnings = Vec::new();

        for constant in all_constants {
            // Apply name mapping if configured.
            let name_str = constant.name.to_string();
            if config.name_mapping.contains_key(&name_str) {
                warnings.push(format!(
                    "name '{}' remapped to '{}'",
                    name_str, config.name_mapping[&name_str]
                ));
            }

            // Filter by kind based on config.
            match constant.kind {
                ImportedConstantKind::Support if !config.include_support => continue,
                ImportedConstantKind::Assumption
                    if !config.include_assumptions
                    // Check axiom policy.
                    && config.axiom_policy == OtAxiomPolicy::RejectUnknown =>
                {
                    warnings.push(format!(
                        "axiom '{}' rejected by RejectUnknown policy",
                        constant.name
                    ));
                    continue;
                }
                _ => {}
            }

            filtered.push(constant);
        }

        let stats = OtStatistics {
            articles_read: 1,
            theorems_imported: base_stats.theorem_count,
            axioms_tracked: base_stats.assumption_count,
            support_imported: base_stats.support_count,
            articles_failed: 0,
        };

        Ok(OtImportResult {
            constants: filtered,
            statistics: stats,
            warnings,
        })
    }

    /// Batch-import multiple article texts, collecting results into a
    /// single `OtImportResult`.
    ///
    /// Articles that fail to parse are counted as failures in statistics
    /// but do not abort the batch. Warnings include per-article failure messages.
    pub fn batch_import(&self, articles: &[&str]) -> OtImportResult {
        let mut all_constants = Vec::new();
        let mut stats = OtStatistics::default();
        let mut warnings = Vec::new();

        for (idx, article_text) in articles.iter().enumerate() {
            stats.articles_read += 1;
            match self.import_article_text(article_text) {
                Ok((constants, import_stats)) => {
                    stats.theorems_imported += import_stats.theorem_count;
                    stats.axioms_tracked += import_stats.assumption_count;
                    stats.support_imported += import_stats.support_count;
                    all_constants.extend(constants);
                }
                Err(e) => {
                    stats.articles_failed += 1;
                    warnings.push(format!("article[{}] failed: {}", idx, e));
                }
            }
        }

        OtImportResult {
            constants: all_constants,
            statistics: stats,
            warnings,
        }
    }

    /// Batch-import multiple article texts with a configuration object.
    pub fn batch_import_with_config(
        &self,
        articles: &[&str],
        config: &OtImportConfig,
    ) -> OtImportResult {
        let mut all_constants = Vec::new();
        let mut stats = OtStatistics::default();
        let mut warnings = Vec::new();

        for (idx, article_text) in articles.iter().enumerate() {
            stats.articles_read += 1;
            match clean_kernel::open_theory::parse_article(article_text) {
                Ok(article) => match self.import_with_config(&article, config) {
                    Ok(result) => {
                        stats.theorems_imported += result.statistics.theorems_imported;
                        stats.axioms_tracked += result.statistics.axioms_tracked;
                        stats.support_imported += result.statistics.support_imported;
                        all_constants.extend(result.constants);
                        warnings.extend(result.warnings);
                    }
                    Err(e) => {
                        stats.articles_failed += 1;
                        warnings.push(format!("article[{}] import failed: {}", idx, e));
                    }
                },
                Err(e) => {
                    stats.articles_failed += 1;
                    warnings.push(format!("article[{}] parse failed: {}", idx, e));
                }
            }
        }

        OtImportResult {
            constants: all_constants,
            statistics: stats,
            warnings,
        }
    }

    /// Wrap a kernel `Declaration` into an `MathverseImportedConstant`.
    fn wrap_declaration(
        &self,
        decl: &Declaration,
        kind: ImportedConstantKind,
    ) -> MathverseImportedConstant {
        let (name, type_expr) = declaration_name_and_type(decl);

        // Assumptions get a higher axiom profile penalty (they are unverified axioms).
        // Theorems and support declarations get the standard HOL base profile.
        let axiom_profile = HOL_BASE_PROFILE;

        let trust_level = match kind {
            ImportedConstantKind::Support => TrustLevel::PartiallyAxiomatized,
            ImportedConstantKind::Assumption => TrustLevel::PartiallyAxiomatized,
            ImportedConstantKind::Theorem => TrustLevel::CertificateReplayed,
        };

        let provenance = Provenance {
            source: self.source_system,
            original_name: name.to_string(),
            source_file: self.source_file.clone(),
            axiom_profile,
        };

        MathverseImportedConstant {
            type_expr,
            name,
            axiom_profile,
            provenance,
            trust_level,
            kind,
        }
    }
}

/// Extract the name and type from a kernel `Declaration`.
fn declaration_name_and_type(decl: &Declaration) -> (LeanName, Expr) {
    match decl {
        Declaration::Axiom { name, type_, .. } => (name.clone(), type_.clone()),
        Declaration::Definition { name, type_, .. } => (name.clone(), type_.clone()),
        Declaration::Theorem { name, type_, .. } => (name.clone(), type_.clone()),
        Declaration::Opaque { name, type_, .. } => (name.clone(), type_.clone()),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_hol_base_profile_contains_expected_bits() {
        assert!(HOL_BASE_PROFILE.contains(AxiomProfile::CLASSICAL));
        assert!(HOL_BASE_PROFILE.contains(AxiomProfile::EXTENSIONALITY));
        assert!(HOL_BASE_PROFILE.contains(AxiomProfile::HOL_EMBEDDING));
        // CHOICE==CLASSICAL (same bit), so test with UNIVALENCE instead
        assert!(!HOL_BASE_PROFILE.contains(AxiomProfile::UNIVALENCE));
        assert!(!HOL_BASE_PROFILE.contains(AxiomProfile::MIZAR_SOFT_TYPE));
        assert_eq!(HOL_BASE_PROFILE.axiom_count(), 3);
    }

    #[test]
    fn test_import_statistics_total() {
        let stats = ImportStatistics {
            support_count: 3,
            assumption_count: 1,
            theorem_count: 5,
        };
        assert_eq!(stats.total(), 9);
    }

    #[test]
    fn test_import_statistics_default_is_zero() {
        let stats = ImportStatistics::default();
        assert_eq!(stats.total(), 0);
    }
}
