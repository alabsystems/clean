// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Batch TPTP importer: parses files, translates to kernel constants.
//!
//! [`TptpImporter`] is the high-level entry point for importing TPTP problem
//! files (`.p`) and axiom files (`.ax`). It wraps the parser and translator,
//! producing [`TptpImportedConstant`] records with axiom profiles and trust
//! metadata.

use super::parser::{parse_tptp_file, TptpParseError};
use super::translate::{
    translate_tptp_formula, TptpConstantKind, TptpImportedConstant, TptpTranslateError,
    TptpTranslationContext,
};
use super::types::TptpRole;
use std::path::Path;
use thiserror::Error;

// ════════════════════════════════════════════════════════════════════════════
// Error type
// ════════════════════════════════════════════════════════════════════════════

/// Errors that can occur during TPTP import.
#[derive(Debug, Error)]
#[non_exhaustive]
pub enum TptpImportError {
    /// TPTP file parsing failed.
    #[error("parse error: {0}")]
    ParseError(#[from] TptpParseError),
    /// Translation from TPTP to clean kernel failed.
    #[error("translation error: {0}")]
    TranslationError(#[from] TptpTranslateError),
    /// I/O error (e.g., reading files from disk).
    #[error("I/O error: {0}")]
    IoError(#[from] std::io::Error),
}

pub(crate) type TptpResult<T> = Result<T, TptpImportError>;

// ════════════════════════════════════════════════════════════════════════════
// Import result
// ════════════════════════════════════════════════════════════════════════════

/// Result of importing a single TPTP file.
#[derive(Clone, Debug, Default)]
pub struct TptpFileImportResult {
    /// Name derived from the file (stem of path).
    pub problem_name: String,
    /// All constants produced from this file.
    pub constants: Vec<TptpImportedConstant>,
    /// Number of axiom formulas imported.
    pub axiom_count: usize,
    /// Number of conjecture formulas imported.
    pub conjecture_count: usize,
    /// Number of theorem/lemma formulas imported.
    pub theorem_count: usize,
    /// Number of formulas that were skipped (type decls, etc.).
    pub skipped_count: usize,
    /// Number of formulas that produced translation errors.
    pub error_count: usize,
    /// Diagnostic messages collected during import.
    pub diagnostics: Vec<String>,
}

impl TptpFileImportResult {
    /// Total number of constants produced.
    #[must_use]
    pub fn total_constants(&self) -> usize {
        self.constants.len()
    }

    /// Whether the import produced any diagnostics.
    #[must_use]
    pub fn has_diagnostics(&self) -> bool {
        !self.diagnostics.is_empty()
    }

    /// Human-readable summary.
    #[must_use]
    pub fn summary(&self) -> String {
        format!(
            "{}: {} constants ({} axiom, {} conjecture, {} theorem), {} skipped, {} errors",
            self.problem_name,
            self.total_constants(),
            self.axiom_count,
            self.conjecture_count,
            self.theorem_count,
            self.skipped_count,
            self.error_count,
        )
    }
}

/// Result of importing an entire TPTP directory.
#[derive(Clone, Debug, Default)]
pub struct TptpImportResult {
    /// Per-file import results.
    pub files: Vec<TptpFileImportResult>,
    /// Files that failed to parse at all.
    pub failed_files: Vec<(String, String)>,
    /// Total constants produced across all files.
    pub total_constants: usize,
    /// Total axioms.
    pub total_axioms: usize,
    /// Total conjectures.
    pub total_conjectures: usize,
    /// Total errors across all files.
    pub total_errors: usize,
}

impl TptpImportResult {
    /// Number of files successfully imported (at least partially).
    #[must_use]
    pub fn files_imported(&self) -> usize {
        self.files.len()
    }

    /// Number of files that completely failed.
    #[must_use]
    pub fn files_failed(&self) -> usize {
        self.failed_files.len()
    }

    /// Whether all files were imported without any errors.
    #[must_use]
    pub fn is_clean(&self) -> bool {
        self.total_errors == 0 && self.failed_files.is_empty()
    }

    /// Human-readable summary.
    #[must_use]
    pub fn summary(&self) -> String {
        format!(
            "TPTP import: {} files ({} failed), {} constants, {} axioms, {} conjectures, {} errors",
            self.files.len(),
            self.failed_files.len(),
            self.total_constants,
            self.total_axioms,
            self.total_conjectures,
            self.total_errors,
        )
    }
}

// ════════════════════════════════════════════════════════════════════════════
// Importer
// ════════════════════════════════════════════════════════════════════════════

/// High-level TPTP importer.
///
/// Parses TPTP `.p` and `.ax` files, translates each annotated formula to a
/// Clean kernel constant, and collects trust/axiom metadata.
pub struct TptpImporter {
    /// Translation context (reused across formulas within a file).
    ctx: TptpTranslationContext,
}

impl Default for TptpImporter {
    fn default() -> Self {
        Self::new()
    }
}

impl TptpImporter {
    /// Create a new TPTP importer.
    #[must_use]
    pub fn new() -> Self {
        Self {
            ctx: TptpTranslationContext::new(),
        }
    }

    /// Import a single TPTP file.
    ///
    /// # Errors
    ///
    /// Returns `TptpImportError` if file reading or parsing fails.
    /// Individual formula translation errors are collected as diagnostics.
    pub fn import_file(&mut self, path: &Path) -> TptpResult<TptpFileImportResult> {
        let problem_name = path
            .file_stem()
            .and_then(|s| s.to_str())
            .unwrap_or("unknown")
            .to_owned();

        let source_file = path.to_string_lossy().to_string();
        let tptp_file = parse_tptp_file(path)?;

        let mut result = TptpFileImportResult {
            problem_name: problem_name.clone(),
            ..TptpFileImportResult::default()
        };

        for (idx, formula) in tptp_file.formulas.iter().enumerate() {
            match translate_tptp_formula(&mut self.ctx, formula, &problem_name, Some(&source_file))
            {
                Ok(Some(constant)) => {
                    match constant.kind {
                        TptpConstantKind::Axiom => result.axiom_count += 1,
                        TptpConstantKind::Conjecture => result.conjecture_count += 1,
                        TptpConstantKind::Theorem => result.theorem_count += 1,
                        _ => {}
                    }
                    result.constants.push(constant);
                }
                Ok(None) => {
                    result.skipped_count += 1;
                    result.diagnostics.push(format!(
                        "formula {idx} ({}): skipped (type decl)",
                        formula.name
                    ));
                }
                Err(e) => {
                    result.error_count += 1;
                    result.diagnostics.push(format!(
                        "formula {idx} ({}): translation error: {e}",
                        formula.name
                    ));
                }
            }
        }

        Ok(result)
    }

    /// Import all TPTP files from a directory (recursive).
    ///
    /// Processes all `.p` and `.ax` files found recursively under `dir`.
    ///
    /// # Errors
    ///
    /// Returns `TptpImportError` only for directory-level I/O failures.
    /// Per-file errors are collected in `TptpImportResult::failed_files`.
    pub fn import_dir(&mut self, dir: &Path) -> TptpResult<TptpImportResult> {
        let mut result = TptpImportResult::default();
        let mut paths = Vec::new();
        collect_tptp_files_recursive(dir, &mut paths);

        for path in &paths {
            let file_name = path
                .file_name()
                .and_then(|s| s.to_str())
                .unwrap_or("unknown")
                .to_owned();

            match self.import_file(path) {
                Ok(file_result) => {
                    result.total_constants += file_result.total_constants();
                    result.total_axioms += file_result.axiom_count;
                    result.total_conjectures += file_result.conjecture_count;
                    result.total_errors += file_result.error_count;
                    result.files.push(file_result);
                }
                Err(e) => {
                    result.failed_files.push((file_name, format!("{e}")));
                    result.total_errors += 1;
                }
            }
        }

        Ok(result)
    }
}

/// Recursively collect `.p` and `.ax` files from a directory.
fn collect_tptp_files_recursive(dir: &Path, out: &mut Vec<std::path::PathBuf>) {
    let entries = match std::fs::read_dir(dir) {
        Ok(entries) => entries,
        Err(_) => return,
    };

    for entry in entries.flatten() {
        let path = entry.path();
        if path.is_dir() {
            collect_tptp_files_recursive(&path, out);
        } else if let Some(ext) = path.extension().and_then(|e| e.to_str()) {
            if ext == "p" || ext == "ax" {
                out.push(path);
            }
        }
    }
}

// ════════════════════════════════════════════════════════════════════════════
// Tests
// ════════════════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_importer_creation() {
        let _importer = TptpImporter::new();
        // Importer starts with empty state.
    }

    #[test]
    fn test_importer_default() {
        let _importer = TptpImporter::default();
        // Default-constructed importer is valid.
    }

    #[test]
    fn test_file_import_result_summary() {
        let result = TptpFileImportResult {
            problem_name: "TEST".to_owned(),
            axiom_count: 5,
            conjecture_count: 1,
            theorem_count: 2,
            skipped_count: 1,
            error_count: 0,
            ..TptpFileImportResult::default()
        };
        let summary = result.summary();
        assert!(summary.contains("TEST"));
        assert!(summary.contains("5 axiom"));
        assert!(summary.contains("1 conjecture"));
    }

    #[test]
    fn test_import_result_summary() {
        let result = TptpImportResult {
            total_constants: 100,
            total_axioms: 80,
            total_conjectures: 20,
            ..TptpImportResult::default()
        };
        assert!(result.is_clean());
        let summary = result.summary();
        assert!(summary.contains("100 constants"));
    }

    #[test]
    fn test_import_nonexistent_file() {
        let mut importer = TptpImporter::new();
        let result = importer.import_file(Path::new("/nonexistent/path.p"));
        assert!(result.is_err());
    }

    #[test]
    fn test_import_nonexistent_dir() {
        let mut importer = TptpImporter::new();
        let result = importer.import_dir(Path::new("/nonexistent/dir"));
        assert!(result.is_ok()); // Empty result, no crash.
        let import = result.expect("should succeed");
        assert_eq!(import.files_imported(), 0);
    }

    #[test]
    fn test_collect_tptp_files_empty() {
        let mut paths = Vec::new();
        collect_tptp_files_recursive(Path::new("/nonexistent"), &mut paths);
        assert!(paths.is_empty());
    }
}
