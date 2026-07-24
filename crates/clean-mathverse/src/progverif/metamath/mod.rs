// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Metamath proof database importer.
//!
//! Metamath is a minimalist formal proof language where proofs are sequences
//! of label references in a compressed RPN format. Metamath databases (`.mm`
//! files) contain axioms, theorems, and their proofs in a uniform syntax.
//!
//! Trust model:
//! - Fully verified databases (all proofs checked): `NONE` (kernel-level trust)
//! - Databases with classical axioms (set.mm): `CLASSICAL`, `AxiomDependent`
//! - Databases with unverified theorems: `SMT_ORACLE`, `TrustedOracle`
//!
//! Metamath's proof verification is so simple (~300 lines in any language) that
//! verified Metamath databases can be imported at the highest trust level.
//! The only axiom dependency comes from the logical axioms declared in the
//! database itself (e.g., set.mm includes classical logic).

use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::types::{AxiomProfile, Provenance, SourceSystem, TrustLevel};

pub mod verify;

// ============================================================================
// Errors
// ============================================================================

/// Errors raised during Metamath import operations.
#[derive(Debug, Error)]
#[non_exhaustive]
pub enum MetamathError {
    /// Failed to parse a Metamath database.
    #[error("failed to parse Metamath database: {reason}")]
    ParseError { reason: String },

    /// A proof step references a label that does not exist.
    #[error("unknown label `{label}` in proof of `{theorem}`")]
    UnknownLabel { theorem: String, label: String },

    /// A proof failed Metamath's stack-based verification.
    #[error("proof verification failed for `{theorem}`: {reason}")]
    ProofVerificationFailed { theorem: String, reason: String },

    /// Database structure is invalid (e.g., dangling scopes).
    #[error("Metamath database error: {reason}")]
    DatabaseError { reason: String },

    /// Unsupported Metamath feature (e.g., include files).
    #[error("unsupported Metamath feature: {feature}")]
    UnsupportedFeature { feature: String },
}

// ============================================================================
// Data types
// ============================================================================

/// A single statement in a Metamath database.
///
/// Metamath has two primary statement types that carry mathematical content:
/// axioms (`$a`) and theorems (`$p`). Other statement types (variable
/// declarations, disjoint variable conditions, etc.) are structural and
/// handled during parsing.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum MetamathStatement {
    /// An axiom (`$a` statement). Axioms are accepted without proof.
    Axiom {
        /// Label (name) of the axiom.
        name: String,
        /// Typecode and expression tokens (the mathematical content).
        expression: Vec<String>,
    },
    /// A theorem (`$p` statement) with a proof.
    Theorem {
        /// Label (name) of the theorem.
        name: String,
        /// Typecode and expression tokens.
        expression: Vec<String>,
        /// Proof steps (RPN labels or compressed proof string).
        proof_steps: Vec<String>,
    },
}

impl MetamathStatement {
    /// Get the label (name) of this statement.
    #[must_use]
    pub fn name(&self) -> &str {
        match self {
            Self::Axiom { name, .. } | Self::Theorem { name, .. } => name,
        }
    }

    /// Whether this statement is an axiom.
    #[must_use]
    pub fn is_axiom(&self) -> bool {
        matches!(self, Self::Axiom { .. })
    }

    /// Whether this statement is a theorem.
    #[must_use]
    pub fn is_theorem(&self) -> bool {
        matches!(self, Self::Theorem { .. })
    }
}

/// A Metamath database loaded from a `.mm` file.
///
/// Contains the parsed axioms and theorems, plus metadata about the database
/// such as its name and the list of axiom labels (for axiom profile tracking).
#[derive(Debug, Clone, Serialize, Deserialize)]
#[non_exhaustive]
pub struct MetamathDatabase {
    /// Database name (typically the filename without `.mm`).
    pub name: String,
    /// All statements in declaration order.
    pub statements: Vec<MetamathStatement>,
    /// Labels of logical axioms (used for axiom profile classification).
    pub axiom_labels: Vec<String>,
    /// Source file name, if known.
    pub source_file: Option<String>,
}

impl MetamathDatabase {
    /// Count of axiom statements.
    #[must_use]
    pub fn axiom_count(&self) -> usize {
        self.statements.iter().filter(|s| s.is_axiom()).count()
    }

    /// Count of theorem statements.
    #[must_use]
    pub fn theorem_count(&self) -> usize {
        self.statements.iter().filter(|s| s.is_theorem()).count()
    }

    /// Total statement count.
    #[must_use]
    pub fn statement_count(&self) -> usize {
        self.statements.len()
    }
}

/// Result of importing a Metamath database.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[non_exhaustive]
pub struct MetamathImportResult {
    /// Database name.
    pub name: String,
    /// Total number of theorems (VCs).
    pub vc_count: usize,
    /// Number of theorems with verified proofs.
    pub verified_count: usize,
    /// Number of axioms in the database.
    pub axiom_count: usize,
    /// Axiom profile for the imported result.
    pub axiom_profile: AxiomProfile,
    /// Trust level assigned to the imported result.
    pub trust_level: TrustLevel,
    /// Provenance record for the import.
    pub provenance: Provenance,
    /// Diagnostic messages from the import process.
    pub diagnostics: Vec<String>,
}

/// Classification of a Metamath database by its logical foundation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum DatabaseFoundation {
    /// Classical logic (set.mm and derivatives).
    Classical,
    /// Intuitionistic logic (iset.mm).
    Intuitionistic,
    /// Minimal/unknown foundation.
    Minimal,
}

// ============================================================================
// Importer
// ============================================================================

/// Imports Metamath databases into the Mathverse trust framework.
///
/// Parses Metamath database metadata and classifies the logical foundation
/// for axiom profile assignment. Metamath's simple proof format allows for
/// high-trust imports when proofs are verified.
pub struct MetamathImporter {
    _private: (),
}

impl Default for MetamathImporter {
    fn default() -> Self {
        Self::new()
    }
}

impl MetamathImporter {
    /// Create a new Metamath importer.
    #[must_use]
    pub fn new() -> Self {
        Self { _private: () }
    }

    /// Import a Metamath database from its textual representation.
    ///
    /// Performs a lightweight parse of the Metamath `.mm` format, extracting
    /// `$a` (axiom) and `$p` (theorem) statements. This parser handles the
    /// core statement syntax but does not perform full scope analysis or
    /// proof verification (that is done by the trust assignment phase).
    pub fn import_database(&self, db_text: &str) -> Result<MetamathDatabase, MetamathError> {
        let trimmed = db_text.trim();
        if trimmed.is_empty() {
            return Err(MetamathError::ParseError {
                reason: "empty database text".to_string(),
            });
        }

        // Extract database name from `$( Database: <name> $)` comment.
        let name =
            extract_mm_comment(trimmed, "Database:").unwrap_or_else(|| "unnamed".to_string());

        // Extract source file from `$( File: <path> $)` comment.
        let source_file = extract_mm_comment(trimmed, "File:");

        let mut statements = Vec::new();
        let mut axiom_labels = Vec::new();

        // Parse `$a` (axiom) statements: `<label> $a <tokens> $.`
        for (label, tokens) in iter_mm_statements(trimmed, "$a") {
            axiom_labels.push(label.clone());
            statements.push(MetamathStatement::Axiom {
                name: label,
                expression: tokens,
            });
        }

        // Parse `$p` (theorem) statements: `<label> $p <tokens> $= <proof> $.`
        for (label, tokens) in iter_mm_statements(trimmed, "$p") {
            // Split tokens at `$=` to separate expression from proof.
            let (expr_tokens, proof_steps) = split_at_proof_marker(&tokens);
            statements.push(MetamathStatement::Theorem {
                name: label,
                expression: expr_tokens,
                proof_steps,
            });
        }

        if statements.is_empty() {
            return Err(MetamathError::DatabaseError {
                reason: "no $a or $p statements found".to_string(),
            });
        }

        Ok(MetamathDatabase {
            name,
            statements,
            axiom_labels,
            source_file,
        })
    }

    /// Produce an import result from a parsed database (without proof verification).
    ///
    /// Checks for proof *presence* only. For actual RPN proof verification,
    /// use [`import_verified`] instead.
    #[must_use]
    pub fn import_result(&self, db: &MetamathDatabase) -> MetamathImportResult {
        let verified_count = db
            .statements
            .iter()
            .filter(|s| match s {
                MetamathStatement::Theorem { proof_steps, .. } => !proof_steps.is_empty(),
                MetamathStatement::Axiom { .. } => false,
            })
            .count();
        let all_verified = verified_count == db.theorem_count() && db.theorem_count() > 0;
        let foundation = classify_database_foundation(&db.axiom_labels);

        let (axiom_profile, trust_level) = match (all_verified, foundation) {
            (true, DatabaseFoundation::Classical) => {
                (AxiomProfile::CLASSICAL, TrustLevel::AxiomDependent)
            }
            (true, _) => (AxiomProfile::NONE, TrustLevel::KernelVerified),
            (false, _) => (AxiomProfile::SMT_ORACLE, TrustLevel::TrustedOracle),
        };

        let mut diagnostics = Vec::new();
        if !all_verified && db.theorem_count() > 0 {
            let missing = db.theorem_count() - verified_count;
            diagnostics.push(format!(
                "{missing}/{} theorems without proofs",
                db.theorem_count()
            ));
        }
        diagnostics.push(format!(
            "foundation: {foundation:?}, axioms: {}, theorems: {}",
            db.axiom_count(),
            db.theorem_count()
        ));

        build_import_result(db, verified_count, axiom_profile, trust_level, diagnostics)
    }

    /// Parse and verify a Metamath database, producing an import result with
    /// accurate trust levels based on RPN proof replay.
    ///
    /// Runs the full Metamath RPN stack machine on every theorem proof.
    /// Verified theorems are assigned `CertificateReplayed` trust level.
    pub fn import_verified(
        &self,
        db_text: &str,
    ) -> Result<(MetamathImportResult, verify::VerifyResult), MetamathError> {
        let db = self.import_database(db_text)?;
        let vr = verify::parse_and_verify(db_text)?;

        let foundation = classify_database_foundation(&db.axiom_labels);
        let all_verified = vr.failed == 0 && vr.compressed_skipped == 0 && vr.verified > 0;

        let (axiom_profile, trust_level) = match (all_verified, foundation) {
            (true, DatabaseFoundation::Classical) => {
                (AxiomProfile::CLASSICAL, TrustLevel::CertificateReplayed)
            }
            (true, _) => (AxiomProfile::NONE, TrustLevel::CertificateReplayed),
            (false, _) => (AxiomProfile::SMT_ORACLE, TrustLevel::TrustedOracle),
        };

        let mut diagnostics = Vec::new();
        diagnostics.push(format!(
            "RPN verified: {}, failed: {}, compressed_skipped: {}, axioms: {}",
            vr.verified, vr.failed, vr.compressed_skipped, vr.axioms
        ));
        for label in &vr.failed_labels {
            diagnostics.push(format!("  FAIL: {label}"));
        }
        diagnostics.push(format!(
            "foundation: {foundation:?}, axioms: {}, theorems: {}",
            db.axiom_count(),
            db.theorem_count()
        ));
        diagnostics.push(format!("total proof steps: {}", vr.total_steps));

        let result = build_import_result(&db, vr.verified, axiom_profile, trust_level, diagnostics);
        Ok((result, vr))
    }
}

/// Build a `MetamathImportResult` from pre-computed trust parameters.
fn build_import_result(
    db: &MetamathDatabase,
    verified_count: usize,
    axiom_profile: AxiomProfile,
    trust_level: TrustLevel,
    diagnostics: Vec<String>,
) -> MetamathImportResult {
    MetamathImportResult {
        name: db.name.clone(),
        vc_count: db.theorem_count(),
        verified_count,
        axiom_count: db.axiom_count(),
        axiom_profile,
        trust_level,
        provenance: Provenance {
            source: SourceSystem::Metamath,
            original_name: db.name.clone(),
            source_file: db.source_file.clone(),
            axiom_profile,
        },
        diagnostics,
    }
}

// ============================================================================
// Database classification
// ============================================================================

/// Classify a database's logical foundation by its axiom labels.
///
/// set.mm uses classical axioms with names like `ax-mp`, `ax-1`, `ax-2`,
/// `ax-3` (propositional) and `ax-gen`, `ax-4`, `ax-5` (predicate logic).
/// The presence of `ax-3` (double negation / excluded middle) marks
/// classical logic.
pub(crate) fn classify_database_foundation(axiom_labels: &[String]) -> DatabaseFoundation {
    let has_classical = axiom_labels.iter().any(|l| {
        let lower = l.to_ascii_lowercase();
        // set.mm classical axioms
        lower == "ax-3"
            || lower.contains("excluded-middle")
            || lower.contains("double-negation")
            || lower.contains("ax-ext")
    });

    let has_intuitionistic = axiom_labels.iter().any(|l| {
        let lower = l.to_ascii_lowercase();
        lower.contains("ax-i") || lower.contains("intuitionistic")
    });

    if has_classical {
        DatabaseFoundation::Classical
    } else if has_intuitionistic {
        DatabaseFoundation::Intuitionistic
    } else {
        DatabaseFoundation::Minimal
    }
}

// ============================================================================
// Parsing helpers
// ============================================================================

/// Extract a value from a Metamath comment: `$( <prefix> <value> $)`.
fn extract_mm_comment(text: &str, prefix: &str) -> Option<String> {
    for line in text.lines() {
        let line = line.trim();
        if let Some(rest) = line.strip_prefix("$(") {
            let rest = rest.trim();
            if let Some(value) = rest.strip_prefix(prefix) {
                let value = value.trim();
                let value = value.strip_suffix("$)").unwrap_or(value).trim();
                if !value.is_empty() {
                    return Some(value.to_string());
                }
            }
        }
    }
    None
}

/// Extract statements of a given type (`$a` or `$p`) from Metamath text.
///
/// Returns `(label, tokens)` pairs. Tokens include everything after the
/// statement keyword up to `$.` (for `$a`) or through `$= <proof> $.`
/// (for `$p`).
fn iter_mm_statements(text: &str, stmt_type: &str) -> Vec<(String, Vec<String>)> {
    let mut results = Vec::new();
    let mut search_from = 0;

    while let Some(pos) = text[search_from..].find(stmt_type) {
        let abs_pos = search_from + pos;

        // The label is the last whitespace-delimited token before the keyword.
        let before = &text[..abs_pos];
        let label = before
            .split_whitespace()
            .next_back()
            .unwrap_or("?")
            .to_string();

        // Tokens are everything from after the keyword to `$.`.
        let after_keyword = &text[abs_pos + stmt_type.len()..];
        if let Some(end_pos) = after_keyword.find("$.") {
            let tokens_str = after_keyword[..end_pos].trim();
            let tokens: Vec<String> = tokens_str
                .split_whitespace()
                .map(ToString::to_string)
                .collect();
            results.push((label, tokens));
            search_from = abs_pos + stmt_type.len() + end_pos + 2;
        } else {
            break;
        }
    }

    results
}

/// Split token list at the `$=` proof marker.
///
/// In Metamath `$p` statements, the expression tokens are before `$=` and
/// the proof labels are after.
fn split_at_proof_marker(tokens: &[String]) -> (Vec<String>, Vec<String>) {
    if let Some(pos) = tokens.iter().position(|t| t == "$=") {
        let expr = tokens[..pos].to_vec();
        let proof = tokens[pos + 1..].to_vec();
        (expr, proof)
    } else {
        (tokens.to_vec(), Vec::new())
    }
}

#[cfg(test)]
mod tests;
