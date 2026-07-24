// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Batch SMT-LIB2 importer: parses `.smt2` files, translates to kernel constants.
//!
//! [`SmtlibImporter`] is the high-level entry point for importing SMT-LIB2
//! benchmark and test files. It wraps the parser and translator, producing
//! [`SmtImportedConstant`] records with axiom profiles and trust metadata.

use super::parser::{parse_smtlib_file, SmtParseError};
use super::translate::{
    translate_script, SmtConstantKind, SmtImportedConstant, SmtTranslateError,
    SmtTranslationContext,
};
use std::path::Path;
use thiserror::Error;

// ════════════════════════════════════════════════════════════════════════════
// Error type
// ════════════════════════════════════════════════════════════════════════════

/// Errors that can occur during SMT-LIB2 import.
#[derive(Debug, Error)]
#[non_exhaustive]
pub enum SmtlibImportError {
    /// SMT-LIB2 file parsing failed.
    #[error("parse error: {0}")]
    ParseError(#[from] SmtParseError),
    /// Translation from SMT-LIB2 to clean kernel failed.
    #[error("translation error: {0}")]
    TranslationError(#[from] SmtTranslateError),
    /// I/O error.
    #[error("I/O error: {0}")]
    IoError(#[from] std::io::Error),
}

pub(crate) type SmtlibResult<T> = Result<T, SmtlibImportError>;

// ════════════════════════════════════════════════════════════════════════════
// Import result
// ════════════════════════════════════════════════════════════════════════════

/// Result of importing a single SMT-LIB2 file.
#[derive(Clone, Debug, Default)]
pub struct SmtlibFileImportResult {
    /// Name derived from the file (stem of path).
    pub problem_name: String,
    /// Logic declared in the file.
    pub logic: Option<String>,
    /// All constants produced from this file.
    pub constants: Vec<SmtImportedConstant>,
    /// Number of declarations imported.
    pub declaration_count: usize,
    /// Number of definitions imported.
    pub definition_count: usize,
    /// Number of assertions imported.
    pub assertion_count: usize,
    /// Number of commands that produced translation errors.
    pub error_count: usize,
    /// Diagnostic messages.
    pub diagnostics: Vec<String>,
}

impl SmtlibFileImportResult {
    /// Total number of constants produced.
    #[must_use]
    pub fn total_constants(&self) -> usize {
        self.constants.len()
    }

    /// Human-readable summary.
    #[must_use]
    pub fn summary(&self) -> String {
        format!(
            "{}: {} constants ({} decl, {} def, {} assert), {} errors",
            self.problem_name,
            self.total_constants(),
            self.declaration_count,
            self.definition_count,
            self.assertion_count,
            self.error_count,
        )
    }
}

/// Result of importing an entire directory of SMT-LIB2 files.
#[derive(Clone, Debug, Default)]
pub struct SmtlibImportResult {
    /// Per-file import results.
    pub files: Vec<SmtlibFileImportResult>,
    /// Files that failed to parse.
    pub failed_files: Vec<(String, String)>,
    /// Total constants.
    pub total_constants: usize,
    /// Total declarations.
    pub total_declarations: usize,
    /// Total assertions.
    pub total_assertions: usize,
    /// Total errors.
    pub total_errors: usize,
}

impl SmtlibImportResult {
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
            "SMT-LIB import: {} files ({} failed), {} constants, {} decl, {} assert, {} errors",
            self.files.len(),
            self.failed_files.len(),
            self.total_constants,
            self.total_declarations,
            self.total_assertions,
            self.total_errors,
        )
    }
}

// ════════════════════════════════════════════════════════════════════════════
// Importer
// ════════════════════════════════════════════════════════════════════════════

/// High-level SMT-LIB2 importer.
pub struct SmtlibImporter {
    ctx: SmtTranslationContext,
}

impl Default for SmtlibImporter {
    fn default() -> Self {
        Self::new()
    }
}

impl SmtlibImporter {
    /// Create a new SMT-LIB2 importer.
    #[must_use]
    pub fn new() -> Self {
        Self {
            ctx: SmtTranslationContext::new(),
        }
    }

    /// Import a single SMT-LIB2 file.
    ///
    /// # Errors
    ///
    /// Returns `SmtlibImportError` if file reading or parsing fails.
    pub fn import_file(&mut self, path: &Path) -> SmtlibResult<SmtlibFileImportResult> {
        let problem_name = path
            .file_stem()
            .and_then(|s| s.to_str())
            .unwrap_or("unknown")
            .to_owned();

        let source_file = path.to_string_lossy().to_string();
        let script = parse_smtlib_file(path)?;

        let mut result = SmtlibFileImportResult {
            problem_name: problem_name.clone(),
            logic: script.logic.clone(),
            ..SmtlibFileImportResult::default()
        };

        match translate_script(&mut self.ctx, &script, &problem_name, Some(&source_file)) {
            Ok(constants) => {
                for c in &constants {
                    match c.kind {
                        SmtConstantKind::Declaration | SmtConstantKind::Sort => {
                            result.declaration_count += 1;
                        }
                        SmtConstantKind::Definition => result.definition_count += 1,
                        SmtConstantKind::Assertion => result.assertion_count += 1,
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

    /// Import all `.smt2` files from a directory (recursive).
    ///
    /// # Errors
    ///
    /// Returns `SmtlibImportError` only for directory-level I/O failures.
    pub fn import_dir(&mut self, dir: &Path) -> SmtlibResult<SmtlibImportResult> {
        let mut result = SmtlibImportResult::default();
        let mut paths = Vec::new();
        collect_smt2_files_recursive(dir, &mut paths);

        for path in &paths {
            let file_name = path
                .file_name()
                .and_then(|s| s.to_str())
                .unwrap_or("unknown")
                .to_owned();

            match self.import_file(path) {
                Ok(file_result) => {
                    result.total_constants += file_result.total_constants();
                    result.total_declarations += file_result.declaration_count;
                    result.total_assertions += file_result.assertion_count;
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

/// Recursively collect `.smt2` files from a directory.
fn collect_smt2_files_recursive(dir: &Path, out: &mut Vec<std::path::PathBuf>) {
    let entries = match std::fs::read_dir(dir) {
        Ok(entries) => entries,
        Err(_) => return,
    };

    for entry in entries.flatten() {
        let path = entry.path();
        if path.is_dir() {
            collect_smt2_files_recursive(&path, out);
        } else if let Some(ext) = path.extension().and_then(|e| e.to_str()) {
            if ext == "smt2" {
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
        let _importer = SmtlibImporter::new();
    }

    #[test]
    fn test_importer_default() {
        let _importer = SmtlibImporter::default();
    }

    #[test]
    fn test_file_import_result_summary() {
        let result = SmtlibFileImportResult {
            problem_name: "test".to_owned(),
            declaration_count: 3,
            assertion_count: 5,
            ..SmtlibFileImportResult::default()
        };
        let summary = result.summary();
        assert!(summary.contains("test"));
        assert!(summary.contains("3 decl"));
        assert!(summary.contains("5 assert"));
    }

    #[test]
    fn test_import_result_summary() {
        let result = SmtlibImportResult {
            total_constants: 50,
            total_declarations: 20,
            total_assertions: 30,
            ..SmtlibImportResult::default()
        };
        assert!(result.is_clean());
        assert!(result.summary().contains("50 constants"));
    }

    #[test]
    fn test_import_nonexistent_file() {
        let mut importer = SmtlibImporter::new();
        let result = importer.import_file(Path::new("/nonexistent/path.smt2"));
        assert!(result.is_err());
    }

    #[test]
    fn test_import_nonexistent_dir() {
        let mut importer = SmtlibImporter::new();
        let result = importer.import_dir(Path::new("/nonexistent/dir"));
        assert!(result.is_ok());
        let import = result.expect("should succeed");
        assert_eq!(import.files_imported(), 0);
    }

    #[test]
    fn test_collect_smt2_files_empty() {
        let mut paths = Vec::new();
        collect_smt2_files_recursive(Path::new("/nonexistent"), &mut paths);
        assert!(paths.is_empty());
    }
}
