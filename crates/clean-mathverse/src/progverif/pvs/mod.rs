// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! PVS importer (higher-order translation with predicate subtypes).
//!
//! PVS (Prototype Verification System) uses higher-order logic with predicate
//! subtypes, dependent types, and a rich strategy language for interactive
//! proof. PVS theories contain lemmas proved by strategies like `grind`,
//! `assert`, `induct-and-simplify`, etc.
//!
//! Trust model:
//! - Decidable strategies (`assert`, `propax`, `tcc`): `CLASSICAL` axiom profile
//! - Arithmetic strategies (`grind`, `field`, `manip`): `SMT_ORACLE` axiom profile
//! - Unproved lemmas: `SMT_ORACLE` axiom profile, `TrustedOracle` trust level

use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::types::{AxiomProfile, Provenance, SourceSystem, TrustLevel};

// ════════════════════════════════════════════════════════════════════════════
// Errors
// ════════════════════════════════════════════════════════════════════════════

/// Errors raised during PVS import operations.
#[derive(Debug, Error)]
#[non_exhaustive]
pub enum PvsError {
    /// Failed to parse a PVS theory summary.
    #[error("failed to parse PVS theory: {reason}")]
    ParseError { reason: String },

    /// A PVS proof strategy is not supported for import.
    #[error("unsupported PVS strategy: `{strategy}`")]
    StrategyError { strategy: String },

    /// The PVS theory uses features we cannot import.
    #[error("unsupported PVS theory feature: {feature}")]
    UnsupportedTheory { feature: String },
}

// ════════════════════════════════════════════════════════════════════════════
// Data types
// ════════════════════════════════════════════════════════════════════════════

/// A single lemma from a PVS theory.
///
/// Each lemma has an associated proof status and optional strategy/script
/// from the PVS prover session.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub struct PvsLemma {
    /// Lemma name.
    pub name: String,
    /// Theory this lemma belongs to.
    pub theory: String,
    /// Whether the lemma has been proved.
    pub proved: bool,
    /// Top-level proof strategy used (e.g., `"grind"`, `"assert"`, `"induct-and-simplify"`).
    pub strategy: Option<String>,
    /// Full proof script, if available.
    pub proof_script: Option<String>,
}

/// A PVS theory containing lemmas and import declarations.
///
/// Theories are the top-level organizational unit in PVS, similar to Lean
/// modules or Isabelle locales.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub struct PvsTheory {
    /// Theory name.
    pub name: String,
    /// Lemmas declared in this theory.
    pub lemmas: Vec<PvsLemma>,
    /// Imported theory names.
    pub imports: Vec<String>,
}

/// Result of importing a PVS theory.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[non_exhaustive]
pub struct PvsImportResult {
    /// Name of the imported theory.
    pub name: String,
    /// Total number of lemmas in the theory.
    pub lemma_count: usize,
    /// Number of lemmas proved.
    pub proved_count: usize,
    /// Axiom profile for the imported result.
    pub axiom_profile: AxiomProfile,
    /// Trust level assigned to the imported result.
    pub trust_level: TrustLevel,
    /// Provenance record for the import.
    pub provenance: Provenance,
    /// Diagnostic messages from the import process.
    pub diagnostics: Vec<String>,
}

/// Strategy category for axiom profile classification.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum StrategyCategory {
    /// Decidable strategies that require only classical logic.
    /// Examples: `assert`, `propax`, `tcc`, `ground`, `model-check`.
    Decidable,
    /// Strategies relying on SMT-like arithmetic reasoning.
    /// Examples: `grind`, `field`, `manip`, `real-props`.
    SmtBased,
    /// Induction and structural strategies.
    /// Examples: `induct-and-simplify`, `measure-induct+`.
    Inductive,
    /// Unknown or custom strategy — treated as oracle.
    Unknown,
}

// ════════════════════════════════════════════════════════════════════════════
// Importer
// ════════════════════════════════════════════════════════════════════════════

/// Imports PVS theories into the Mathverse trust framework.
///
/// Parses PVS theory summaries (a structured text format listing theory name,
/// imports, lemmas, and proof status) and assigns trust levels based on the
/// proof strategies used.
pub struct PvsImporter {
    _private: (),
}

impl Default for PvsImporter {
    fn default() -> Self {
        Self::new()
    }
}

impl PvsImporter {
    /// Create a new PVS importer.
    #[must_use]
    pub fn new() -> Self {
        Self { _private: () }
    }

    /// Import a PVS theory from a structured text summary.
    ///
    /// Expected format (one section per line, lemmas indented):
    /// ```text
    /// Theory: <name>
    /// Imports: <theory1>, <theory2>, ...
    /// Lemma: <name> | proved: <true|false> | strategy: <name>
    /// Lemma: <name> | proved: <true|false> | strategy: <name> | script: <text>
    /// ```
    pub fn import_theory(&self, theory_text: &str) -> Result<PvsTheory, PvsError> {
        let trimmed = theory_text.trim();
        if trimmed.is_empty() {
            return Err(PvsError::ParseError {
                reason: "empty theory text".to_string(),
            });
        }

        let mut theory_name: Option<String> = None;
        let mut imports = Vec::new();
        let mut lemmas = Vec::new();

        for line in trimmed.lines() {
            let line = line.trim();
            if line.is_empty() || line.starts_with('#') || line.starts_with('%') {
                continue;
            }

            if let Some(rest) = line.strip_prefix("Theory:") {
                theory_name = Some(rest.trim().to_string());
            } else if let Some(rest) = line.strip_prefix("Imports:") {
                imports = rest
                    .split(',')
                    .map(|s| s.trim().to_string())
                    .filter(|s| !s.is_empty())
                    .collect();
            } else if let Some(rest) = line.strip_prefix("Lemma:") {
                let lemma = parse_lemma_line(rest, theory_name.as_deref().unwrap_or("unknown"))?;
                lemmas.push(lemma);
            }
            // Silently skip unrecognized lines for forward compatibility.
        }

        let name = theory_name.ok_or_else(|| PvsError::ParseError {
            reason: "missing 'Theory:' declaration".to_string(),
        })?;

        if lemmas.is_empty() {
            return Err(PvsError::ParseError {
                reason: format!("theory `{name}` has no lemmas"),
            });
        }

        Ok(PvsTheory {
            name,
            lemmas,
            imports,
        })
    }

    /// Produce an import result from a parsed PVS theory.
    #[must_use]
    pub fn import_result(&self, theory: &PvsTheory) -> PvsImportResult {
        let lemma_count = theory.lemmas.len();
        let proved_count = theory.lemmas.iter().filter(|l| l.proved).count();

        // Compute axiom profile as the union of all strategies used.
        let axiom_profile =
            theory
                .lemmas
                .iter()
                .filter(|l| l.proved)
                .fold(AxiomProfile::NONE, |acc, lemma| {
                    let cat = lemma
                        .strategy
                        .as_deref()
                        .map(classify_strategy)
                        .unwrap_or(StrategyCategory::Unknown);
                    acc | strategy_axiom_profile(cat)
                });

        // If no lemmas are proved, assign oracle trust with SMT_ORACLE profile.
        let (final_profile, trust_level) = if proved_count == 0 {
            (AxiomProfile::SMT_ORACLE, TrustLevel::TrustedOracle)
        } else if axiom_profile.contains(AxiomProfile::SMT_ORACLE) {
            // Any SMT-based strategy means oracle trust.
            (axiom_profile, TrustLevel::TrustedOracle)
        } else {
            // Pure decidable/inductive strategies get axiom-dependent trust.
            (axiom_profile, TrustLevel::AxiomDependent)
        };

        let mut diagnostics = Vec::new();
        if proved_count < lemma_count {
            let unproved = lemma_count - proved_count;
            diagnostics.push(format!("{unproved}/{lemma_count} lemmas unproved"));
        }

        // Collect unique strategies used.
        let mut strategies: Vec<&str> = theory
            .lemmas
            .iter()
            .filter_map(|l| l.strategy.as_deref())
            .collect();
        strategies.sort_unstable();
        strategies.dedup();
        if !strategies.is_empty() {
            diagnostics.push(format!("strategies: {}", strategies.join(", ")));
        }

        if !theory.imports.is_empty() {
            diagnostics.push(format!("imports: {}", theory.imports.join(", ")));
        }

        let provenance = Provenance {
            source: SourceSystem::Pvs,
            original_name: theory.name.clone(),
            source_file: None,
            axiom_profile: final_profile,
        };

        PvsImportResult {
            name: theory.name.clone(),
            lemma_count,
            proved_count,
            axiom_profile: final_profile,
            trust_level,
            provenance,
            diagnostics,
        }
    }
}

// ════════════════════════════════════════════════════════════════════════════
// Strategy classification
// ════════════════════════════════════════════════════════════════════════════

/// Classify a PVS strategy name into its category.
pub(crate) fn classify_strategy(name: &str) -> StrategyCategory {
    let lower = name.to_ascii_lowercase();

    // Decidable / classical strategies
    if matches!(
        lower.as_str(),
        "assert" | "propax" | "tcc" | "ground" | "model-check" | "simplify" | "flatten" | "split"
    ) {
        return StrategyCategory::Decidable;
    }

    // SMT-based / arithmetic strategies
    if matches!(
        lower.as_str(),
        "grind" | "field" | "manip" | "real-props" | "both-sides" | "cancel-nat"
    ) {
        return StrategyCategory::SmtBased;
    }

    // Induction strategies
    if lower.contains("induct") || lower.contains("measure-induct") {
        return StrategyCategory::Inductive;
    }

    StrategyCategory::Unknown
}

/// Map a strategy category to its axiom profile.
#[must_use]
pub(crate) fn strategy_axiom_profile(cat: StrategyCategory) -> AxiomProfile {
    match cat {
        StrategyCategory::Decidable => AxiomProfile::CLASSICAL,
        StrategyCategory::SmtBased => AxiomProfile::SMT_ORACLE,
        StrategyCategory::Inductive => AxiomProfile::CLASSICAL,
        StrategyCategory::Unknown => AxiomProfile::SMT_ORACLE,
    }
}

// ════════════════════════════════════════════════════════════════════════════
// Helpers
// ════════════════════════════════════════════════════════════════════════════

/// Parse a lemma from a pipe-delimited line.
///
/// Format: `<name> | proved: <bool> | strategy: <name> [| script: <text>]`
fn parse_lemma_line(line: &str, theory: &str) -> Result<PvsLemma, PvsError> {
    let parts: Vec<&str> = line.split('|').collect();
    if parts.is_empty() {
        return Err(PvsError::ParseError {
            reason: "empty lemma line".to_string(),
        });
    }

    let name = parts[0].trim().to_string();
    if name.is_empty() {
        return Err(PvsError::ParseError {
            reason: "lemma has no name".to_string(),
        });
    }

    let mut proved = false;
    let mut strategy = None;
    let mut proof_script = None;

    for part in &parts[1..] {
        let part = part.trim();
        if let Some(rest) = part.strip_prefix("proved:") {
            proved = rest.trim() == "true";
        } else if let Some(rest) = part.strip_prefix("strategy:") {
            let s = rest.trim();
            if !s.is_empty() {
                strategy = Some(s.to_string());
            }
        } else if let Some(rest) = part.strip_prefix("script:") {
            let s = rest.trim();
            if !s.is_empty() {
                proof_script = Some(s.to_string());
            }
        }
    }

    Ok(PvsLemma {
        name,
        theory: theory.to_string(),
        proved,
        strategy,
        proof_script,
    })
}

// ════════════════════════════════════════════════════════════════════════════
// Tests
// ════════════════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;

    const MOCK_THEORY: &str = "\
Theory: real_analysis
Imports: reals, orders, topology
Lemma: squeeze_theorem | proved: true | strategy: grind
Lemma: bolzano_weierstrass | proved: true | strategy: induct-and-simplify
Lemma: intermediate_value | proved: false | strategy: grind
Lemma: archimedean_prop | proved: true | strategy: assert";

    const MOCK_DECIDABLE_THEORY: &str = "\
Theory: propositional
Imports: booleans
Lemma: de_morgan_1 | proved: true | strategy: propax
Lemma: de_morgan_2 | proved: true | strategy: assert
Lemma: double_neg | proved: true | strategy: ground";

    #[test]
    fn test_import_theory_parses_structure() {
        let importer = PvsImporter::new();
        let theory = importer.import_theory(MOCK_THEORY).unwrap();

        assert_eq!(theory.name, "real_analysis");
        assert_eq!(theory.imports, vec!["reals", "orders", "topology"]);
        assert_eq!(theory.lemmas.len(), 4);

        let l0 = &theory.lemmas[0];
        assert_eq!(l0.name, "squeeze_theorem");
        assert_eq!(l0.theory, "real_analysis");
        assert!(l0.proved);
        assert_eq!(l0.strategy.as_deref(), Some("grind"));
        assert!(l0.proof_script.is_none());

        let l2 = &theory.lemmas[2];
        assert_eq!(l2.name, "intermediate_value");
        assert!(!l2.proved);
    }

    #[test]
    fn test_import_theory_empty_errors() {
        let importer = PvsImporter::new();
        let result = importer.import_theory("");
        assert!(result.is_err());
        assert!(matches!(result.unwrap_err(), PvsError::ParseError { .. }));
    }

    #[test]
    fn test_import_theory_no_name_errors() {
        let importer = PvsImporter::new();
        let result = importer.import_theory("Lemma: foo | proved: true | strategy: grind");
        assert!(result.is_err());
        assert!(matches!(result.unwrap_err(), PvsError::ParseError { .. }));
    }

    #[test]
    fn test_import_theory_no_lemmas_errors() {
        let importer = PvsImporter::new();
        let result = importer.import_theory("Theory: empty_theory\nImports: reals");
        assert!(result.is_err());
        let err = result.unwrap_err();
        assert!(
            matches!(err, PvsError::ParseError { ref reason } if reason.contains("no lemmas")),
            "expected no-lemmas error, got: {err:?}"
        );
    }

    #[test]
    fn test_import_result_mixed_strategies() {
        let importer = PvsImporter::new();
        let theory = importer.import_theory(MOCK_THEORY).unwrap();
        let result = importer.import_result(&theory);

        assert_eq!(result.name, "real_analysis");
        assert_eq!(result.lemma_count, 4);
        assert_eq!(result.proved_count, 3);
        // Contains grind (SMT_ORACLE), so trust is oracle level.
        assert!(result.axiom_profile.contains(AxiomProfile::SMT_ORACLE));
        assert_eq!(result.trust_level, TrustLevel::TrustedOracle);
        assert_eq!(result.provenance.source, SourceSystem::Pvs);
        assert!(
            result.diagnostics.iter().any(|d| d.contains("unproved")),
            "expected unproved diagnostic"
        );
        assert!(
            result.diagnostics.iter().any(|d| d.contains("strategies")),
            "expected strategies diagnostic"
        );
    }

    #[test]
    fn test_import_result_decidable_only() {
        let importer = PvsImporter::new();
        let theory = importer.import_theory(MOCK_DECIDABLE_THEORY).unwrap();
        let result = importer.import_result(&theory);

        assert_eq!(result.name, "propositional");
        assert_eq!(result.lemma_count, 3);
        assert_eq!(result.proved_count, 3);
        // All decidable strategies → CLASSICAL only.
        assert_eq!(result.axiom_profile, AxiomProfile::CLASSICAL);
        assert_eq!(result.trust_level, TrustLevel::AxiomDependent);
    }

    #[test]
    fn test_import_result_no_proved_lemmas() {
        let text = "\
Theory: failing
Lemma: broken | proved: false | strategy: grind";
        let importer = PvsImporter::new();
        let theory = importer.import_theory(text).unwrap();
        let result = importer.import_result(&theory);

        assert_eq!(result.proved_count, 0);
        assert_eq!(result.axiom_profile, AxiomProfile::SMT_ORACLE);
        assert_eq!(result.trust_level, TrustLevel::TrustedOracle);
    }

    #[test]
    fn test_classify_strategy_decidable() {
        assert_eq!(classify_strategy("assert"), StrategyCategory::Decidable);
        assert_eq!(classify_strategy("propax"), StrategyCategory::Decidable);
        assert_eq!(classify_strategy("tcc"), StrategyCategory::Decidable);
        assert_eq!(classify_strategy("ground"), StrategyCategory::Decidable);
    }

    #[test]
    fn test_classify_strategy_smt() {
        assert_eq!(classify_strategy("grind"), StrategyCategory::SmtBased);
        assert_eq!(classify_strategy("field"), StrategyCategory::SmtBased);
        assert_eq!(classify_strategy("manip"), StrategyCategory::SmtBased);
    }

    #[test]
    fn test_classify_strategy_inductive() {
        assert_eq!(
            classify_strategy("induct-and-simplify"),
            StrategyCategory::Inductive
        );
        assert_eq!(
            classify_strategy("measure-induct+"),
            StrategyCategory::Inductive
        );
    }

    #[test]
    fn test_classify_strategy_unknown() {
        assert_eq!(classify_strategy("custom-strat"), StrategyCategory::Unknown);
    }

    #[test]
    fn test_strategy_axiom_profile() {
        assert_eq!(
            strategy_axiom_profile(StrategyCategory::Decidable),
            AxiomProfile::CLASSICAL
        );
        assert_eq!(
            strategy_axiom_profile(StrategyCategory::SmtBased),
            AxiomProfile::SMT_ORACLE
        );
        assert_eq!(
            strategy_axiom_profile(StrategyCategory::Inductive),
            AxiomProfile::CLASSICAL
        );
        assert_eq!(
            strategy_axiom_profile(StrategyCategory::Unknown),
            AxiomProfile::SMT_ORACLE
        );
    }

    #[test]
    fn test_pvs_importer_default() {
        let _importer = PvsImporter::default();
    }

    #[test]
    fn test_parse_lemma_with_script() {
        let text = "\
Theory: test_th
Lemma: l1 | proved: true | strategy: grind | script: (grind :defs nil)";
        let importer = PvsImporter::new();
        let theory = importer.import_theory(text).unwrap();
        let lemma = &theory.lemmas[0];
        assert_eq!(lemma.proof_script.as_deref(), Some("(grind :defs nil)"));
    }

    #[test]
    fn test_comment_lines_skipped() {
        let text = "\
# This is a comment
% This is also a comment
Theory: commented
Lemma: foo | proved: true | strategy: assert";
        let importer = PvsImporter::new();
        let theory = importer.import_theory(text).unwrap();
        assert_eq!(theory.name, "commented");
        assert_eq!(theory.lemmas.len(), 1);
    }
}
