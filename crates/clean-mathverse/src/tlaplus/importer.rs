// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Batch TLA+ importer: parses `.tla` and `.qnt` files, translates to kernel constants.
//!
//! [`TlaPlusImporter`] is the high-level entry point for importing TLA+
//! specification files. It wraps the parser and translator, producing
//! [`TlaImportedConstant`] records with axiom profiles and trust metadata.

use super::parser::{parse_quint_file, parse_tlaplus_file, TlaParseError};
use super::translate::{
    translate_module, TlaConstantKind, TlaImportedConstant, TlaTranslateError,
    TlaTranslationContext,
};
use std::path::Path;
use thiserror::Error;

// ════════════════════════════════════════════════════════════════════════════
// Error type
// ════════════════════════════════════════════════════════════════════════════

/// Errors that can occur during TLA+ import.
#[derive(Debug, Error)]
#[non_exhaustive]
pub enum TlaPlusImportError {
    /// TLA+ file parsing failed.
    #[error("parse error: {0}")]
    ParseError(#[from] TlaParseError),
    /// Translation from TLA+ to clean kernel failed.
    #[error("translation error: {0}")]
    TranslationError(#[from] TlaTranslateError),
    /// I/O error.
    #[error("I/O error: {0}")]
    IoError(#[from] std::io::Error),
}

pub(crate) type TlaPlusResult<T> = Result<T, TlaPlusImportError>;

// ════════════════════════════════════════════════════════════════════════════
// Import result
// ════════════════════════════════════════════════════════════════════════════

/// Result of importing a single TLA+ file.
#[derive(Clone, Debug, Default)]
pub struct TlaPlusFileImportResult {
    /// Module name.
    pub module_name: String,
    /// All constants produced from this file.
    pub constants: Vec<TlaImportedConstant>,
    /// Number of constant declarations.
    pub constant_count: usize,
    /// Number of variable declarations.
    pub variable_count: usize,
    /// Number of operator definitions.
    pub operator_count: usize,
    /// Number of theorems.
    pub theorem_count: usize,
    /// Number of axioms/assumptions.
    pub axiom_count: usize,
    /// Number of errors.
    pub error_count: usize,
    /// Diagnostic messages.
    pub diagnostics: Vec<String>,
}

impl TlaPlusFileImportResult {
    /// Total number of constants produced.
    #[must_use]
    pub fn total_constants(&self) -> usize {
        self.constants.len()
    }

    /// Human-readable summary.
    #[must_use]
    pub fn summary(&self) -> String {
        format!(
            "{}: {} constants ({} const, {} var, {} op, {} thm, {} axiom), {} errors",
            self.module_name,
            self.total_constants(),
            self.constant_count,
            self.variable_count,
            self.operator_count,
            self.theorem_count,
            self.axiom_count,
            self.error_count,
        )
    }
}

/// Result of importing an entire directory of TLA+ files.
#[derive(Clone, Debug, Default)]
pub struct TlaPlusImportResult {
    /// Per-file import results.
    pub files: Vec<TlaPlusFileImportResult>,
    /// Files that failed to parse.
    pub failed_files: Vec<(String, String)>,
    /// Total constants.
    pub total_constants: usize,
    /// Total theorems.
    pub total_theorems: usize,
    /// Total operators.
    pub total_operators: usize,
    /// Total errors.
    pub total_errors: usize,
}

impl TlaPlusImportResult {
    /// Number of files successfully imported.
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
            "TLA+ import: {} files ({} failed), {} constants, {} thm, {} op, {} errors",
            self.files.len(),
            self.failed_files.len(),
            self.total_constants,
            self.total_theorems,
            self.total_operators,
            self.total_errors,
        )
    }
}

// ════════════════════════════════════════════════════════════════════════════
// Importer
// ════════════════════════════════════════════════════════════════════════════

/// High-level TLA+ importer.
pub struct TlaPlusImporter {
    ctx: TlaTranslationContext,
}

impl Default for TlaPlusImporter {
    fn default() -> Self {
        Self::new()
    }
}

impl TlaPlusImporter {
    /// Create a new TLA+ importer.
    #[must_use]
    pub fn new() -> Self {
        Self {
            ctx: TlaTranslationContext::new(),
        }
    }

    /// Import a single `.tla` file.
    ///
    /// # Errors
    ///
    /// Returns `TlaPlusImportError` if file reading or parsing fails.
    pub fn import_file(&mut self, path: &Path) -> TlaPlusResult<TlaPlusFileImportResult> {
        let source_file = path.to_string_lossy().to_string();

        let ext = path.extension().and_then(|e| e.to_str()).unwrap_or("");
        let module = if ext == "qnt" {
            parse_quint_file(path)?
        } else {
            parse_tlaplus_file(path)?
        };

        let mut result = TlaPlusFileImportResult {
            module_name: module.name.clone(),
            ..TlaPlusFileImportResult::default()
        };

        match translate_module(&mut self.ctx, &module, Some(&source_file)) {
            Ok(constants) => {
                for c in &constants {
                    match c.kind {
                        TlaConstantKind::Constant => result.constant_count += 1,
                        TlaConstantKind::Variable => result.variable_count += 1,
                        TlaConstantKind::Operator => result.operator_count += 1,
                        TlaConstantKind::Theorem => result.theorem_count += 1,
                        TlaConstantKind::Axiom => result.axiom_count += 1,
                        TlaConstantKind::Instance => {}
                    }
                }
                result.constants = constants;
            }
            Err(e) => {
                result.error_count += 1;
                result.diagnostics.push(format!("translation error: {e}"));
            }
        }

        Ok(result)
    }

    /// Import all `.tla` and `.qnt` files from a directory (recursive).
    ///
    /// # Errors
    ///
    /// Returns `TlaPlusImportError` only for directory-level I/O failures.
    pub fn import_dir(&mut self, dir: &Path) -> TlaPlusResult<TlaPlusImportResult> {
        let mut result = TlaPlusImportResult::default();
        let mut paths = Vec::new();
        collect_tla_files_recursive(dir, &mut paths);

        for path in &paths {
            let file_name = path
                .file_name()
                .and_then(|s| s.to_str())
                .unwrap_or("unknown")
                .to_owned();

            match self.import_file(path) {
                Ok(file_result) => {
                    result.total_constants += file_result.total_constants();
                    result.total_theorems += file_result.theorem_count;
                    result.total_operators += file_result.operator_count;
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

/// Recursively collect `.tla` and `.qnt` files from a directory.
fn collect_tla_files_recursive(dir: &Path, out: &mut Vec<std::path::PathBuf>) {
    let entries = match std::fs::read_dir(dir) {
        Ok(entries) => entries,
        Err(_) => return,
    };

    for entry in entries.flatten() {
        let path = entry.path();
        if path.is_dir() {
            collect_tla_files_recursive(&path, out);
        } else if let Some(ext) = path.extension().and_then(|e| e.to_str()) {
            if ext == "tla" || ext == "qnt" {
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
        let _importer = TlaPlusImporter::new();
    }

    #[test]
    fn test_importer_default() {
        let _importer = TlaPlusImporter::default();
    }

    #[test]
    fn test_file_import_result_summary() {
        let result = TlaPlusFileImportResult {
            module_name: "Test".to_owned(),
            constant_count: 2,
            variable_count: 3,
            operator_count: 5,
            theorem_count: 1,
            ..TlaPlusFileImportResult::default()
        };
        let summary = result.summary();
        assert!(summary.contains("Test"));
        assert!(summary.contains("2 const"));
        assert!(summary.contains("3 var"));
    }

    #[test]
    fn test_import_result_summary() {
        let result = TlaPlusImportResult {
            total_constants: 50,
            total_theorems: 5,
            total_operators: 20,
            ..TlaPlusImportResult::default()
        };
        assert!(result.is_clean());
        assert!(result.summary().contains("50 constants"));
    }

    #[test]
    fn test_import_nonexistent_file() {
        let mut importer = TlaPlusImporter::new();
        let result = importer.import_file(Path::new("/nonexistent/path.tla"));
        assert!(result.is_err());
    }

    #[test]
    fn test_import_nonexistent_dir() {
        let mut importer = TlaPlusImporter::new();
        let result = importer.import_dir(Path::new("/nonexistent/dir"));
        assert!(result.is_ok());
        let import = result.expect("should succeed");
        assert_eq!(import.files_imported(), 0);
    }

    #[test]
    fn test_collect_tla_files_empty() {
        let mut paths = Vec::new();
        collect_tla_files_recursive(Path::new("/nonexistent"), &mut paths);
        assert!(paths.is_empty());
    }
}
