// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Import pipeline: wire SerAPI parsing -> CIC extraction -> shard writing.
//!
//! [`run_coq_import`] is the main entry point. It reads `.sexp` files from
//! the directory specified in [`CoqLibraryConfig`], parses them, extracts
//! declarations, filters by phase, and writes to `.mathverse` shards via the
//! existing [`crate::coq::shard`] infrastructure.

use std::path::Path;

use crate::error::{MathverseError, MathverseResult};
use crate::types::AxiomProfile;

use super::cic_extract::{extract_declarations_from_stream, CicDeclKind, CicDeclaration};
use super::library_config::{CoqLibraryConfig, ImportPhase};
use super::sexp_parser::{parse_sexp_stream, SexpParseError};

/// Result of a single-phase or full import run.
#[derive(Clone, Debug, Default)]
pub struct ImportResult {
    /// Total declarations extracted across all files.
    pub declarations_extracted: usize,
    /// Declarations included after phase filtering.
    pub declarations_included: usize,
    /// Declarations skipped by phase filter.
    pub declarations_skipped: usize,
    /// Declarations skipped due to axiomatizable features.
    pub declarations_axiomatized: usize,
    /// Files successfully parsed.
    pub files_parsed: usize,
    /// Files that failed to parse.
    pub files_failed: usize,
    /// Per-kind counts.
    pub kind_counts: KindCounts,
    /// Errors collected (non-fatal).
    pub errors: Vec<ImportError>,
}

/// Per-declaration-kind counts.
#[derive(Clone, Debug, Default)]
pub struct KindCounts {
    pub definitions: usize,
    pub theorems: usize,
    pub lemmas: usize,
    pub inductives: usize,
    pub coinductives: usize,
    pub records: usize,
    pub classes: usize,
    pub instances: usize,
    pub axioms: usize,
    pub canonical_structures: usize,
    pub modules: usize,
    pub module_functors: usize,
}

/// A non-fatal import error with context.
#[derive(Clone, Debug)]
pub struct ImportError {
    pub file: String,
    pub message: String,
}

impl ImportResult {
    /// Merge another result into this one (for aggregating across phases).
    pub fn merge(&mut self, other: &ImportResult) {
        self.declarations_extracted += other.declarations_extracted;
        self.declarations_included += other.declarations_included;
        self.declarations_skipped += other.declarations_skipped;
        self.declarations_axiomatized += other.declarations_axiomatized;
        self.files_parsed += other.files_parsed;
        self.files_failed += other.files_failed;
        self.kind_counts.definitions += other.kind_counts.definitions;
        self.kind_counts.theorems += other.kind_counts.theorems;
        self.kind_counts.lemmas += other.kind_counts.lemmas;
        self.kind_counts.inductives += other.kind_counts.inductives;
        self.kind_counts.coinductives += other.kind_counts.coinductives;
        self.kind_counts.records += other.kind_counts.records;
        self.kind_counts.classes += other.kind_counts.classes;
        self.kind_counts.instances += other.kind_counts.instances;
        self.kind_counts.axioms += other.kind_counts.axioms;
        self.kind_counts.canonical_structures += other.kind_counts.canonical_structures;
        self.kind_counts.modules += other.kind_counts.modules;
        self.kind_counts.module_functors += other.kind_counts.module_functors;
        self.errors.extend(other.errors.iter().cloned());
    }

    /// Summary line for progress reporting.
    #[must_use]
    pub fn summary(&self) -> String {
        format!(
            "extracted={}, included={}, skipped={}, axiomatized={}, \
             files_ok={}, files_err={}",
            self.declarations_extracted,
            self.declarations_included,
            self.declarations_skipped,
            self.declarations_axiomatized,
            self.files_parsed,
            self.files_failed,
        )
    }
}

/// Run the full import pipeline for a library configuration.
///
/// Reads all `.sexp` files from `config.sexp_dir`, parses and extracts
/// declarations, filters by `phase`, and returns the filtered declarations
/// along with import statistics.
///
/// The caller is responsible for feeding the returned declarations into
/// the shard writer (e.g., via [`crate::coq::shard::write_coq_decls_to_shard`]
/// after converting to kernel types).
pub fn run_coq_import(
    config: &CoqLibraryConfig,
    phase: ImportPhase,
) -> MathverseResult<(Vec<CicDeclaration>, ImportResult)> {
    let sexp_dir = &config.sexp_dir;
    if !sexp_dir.exists() {
        return Err(MathverseError::ImportFailed {
            system: config.name.clone(),
            reason: format!("sexp directory does not exist: {}", sexp_dir.display()),
        });
    }

    let mut result = ImportResult::default();
    let mut all_decls = Vec::new();

    // Collect .sexp files.
    let mut sexp_files = Vec::new();
    collect_sexp_files(sexp_dir, &mut sexp_files);
    sexp_files.sort();

    for file_path in &sexp_files {
        match process_sexp_file(file_path, config, phase, &mut result) {
            Ok(decls) => {
                all_decls.extend(decls);
            }
            Err(e) => {
                result.files_failed += 1;
                result.errors.push(ImportError {
                    file: file_path.display().to_string(),
                    message: e.to_string(),
                });
            }
        }
    }

    Ok((all_decls, result))
}

/// Run phased import: execute phases in order up to and including `up_to`.
pub fn run_phased_import(
    config: &CoqLibraryConfig,
    up_to: ImportPhase,
) -> MathverseResult<(Vec<CicDeclaration>, ImportResult)> {
    let mut combined_decls = Vec::new();
    let mut combined_result = ImportResult::default();

    for &phase in ImportPhase::ALL {
        if phase > up_to {
            break;
        }
        let (decls, result) = run_coq_import(config, phase)?;
        combined_result.merge(&result);
        combined_decls.extend(decls);
    }

    Ok((combined_decls, combined_result))
}

/// Process a single `.sexp` file: parse, extract, filter.
fn process_sexp_file(
    path: &Path,
    config: &CoqLibraryConfig,
    phase: ImportPhase,
    result: &mut ImportResult,
) -> MathverseResult<Vec<CicDeclaration>> {
    let text = std::fs::read_to_string(path).map_err(MathverseError::Io)?;

    let sexps = parse_sexp_stream(&text).map_err(|e| sexp_to_mathverse_error(e, path))?;
    result.files_parsed += 1;

    let raw_decls = extract_declarations_from_stream(&sexps);
    result.declarations_extracted += raw_decls.len();

    let mut included = Vec::new();
    for decl in raw_decls {
        // Apply phase filter based on module path.
        if !config.is_included(&decl.module_path, phase) && !config.is_included(&decl.name, phase) {
            result.declarations_skipped += 1;
            continue;
        }

        // Merge library default profile with per-declaration profile.
        let merged_profile = config.default_axiom_profile.union(decl.axiom_profile);

        // Track axiomatizable declarations.
        if merged_profile.has(AxiomProfile::COQ_MODULE_FUNCTOR)
            || merged_profile.has(AxiomProfile::COQ_SPROP)
            || merged_profile.has(AxiomProfile::COQ_COINDUCTIVE)
        {
            result.declarations_axiomatized += 1;
        }

        // Count by kind.
        count_kind(&decl.kind, &mut result.kind_counts);

        included.push(CicDeclaration {
            axiom_profile: merged_profile,
            ..decl
        });
    }

    result.declarations_included += included.len();
    Ok(included)
}

fn count_kind(kind: &CicDeclKind, counts: &mut KindCounts) {
    match kind {
        CicDeclKind::Definition => counts.definitions += 1,
        CicDeclKind::Theorem => counts.theorems += 1,
        CicDeclKind::Lemma => counts.lemmas += 1,
        CicDeclKind::Inductive => counts.inductives += 1,
        CicDeclKind::CoInductive => counts.coinductives += 1,
        CicDeclKind::Record => counts.records += 1,
        CicDeclKind::Class => counts.classes += 1,
        CicDeclKind::Instance => counts.instances += 1,
        CicDeclKind::Axiom => counts.axioms += 1,
        CicDeclKind::CanonicalStructure => counts.canonical_structures += 1,
        CicDeclKind::Module => counts.modules += 1,
        CicDeclKind::ModuleFunctor => counts.module_functors += 1,
    }
}

fn collect_sexp_files(dir: &Path, out: &mut Vec<std::path::PathBuf>) {
    if let Ok(rd) = std::fs::read_dir(dir) {
        for entry in rd.filter_map(|e| e.ok()) {
            let path = entry.path();
            if path.is_dir() {
                collect_sexp_files(&path, out);
            } else if path.extension().is_some_and(|e| e == "sexp") {
                out.push(path);
            }
        }
    }
}

fn sexp_to_mathverse_error(e: SexpParseError, path: &Path) -> MathverseError {
    MathverseError::ImportFailed {
        system: "coq-serapi".to_owned(),
        reason: format!("{}: {e}", path.display()),
    }
}

// ---- Tests -----------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::coq::extended::library_config::coq_stdlib_config;

    fn make_test_dir(files: &[(&str, &str)]) -> tempfile::TempDir {
        let dir = tempfile::tempdir().expect("create tempdir");
        for (name, content) in files {
            let path = dir.path().join(name);
            if let Some(parent) = path.parent() {
                std::fs::create_dir_all(parent).expect("create parents");
            }
            std::fs::write(&path, content).expect("write file");
        }
        dir
    }

    #[test]
    fn test_run_coq_import_single_file() {
        let dir = make_test_dir(&[(
            "init.sexp",
            "(Theorem Coq.Init.Logic.eq_refl (Prod A Type (Prod x A (App eq (A x x)))))",
        )]);
        let config = coq_stdlib_config(dir.path().to_path_buf());
        let (decls, result) =
            run_coq_import(&config, ImportPhase::Core).expect("import should succeed");

        assert_eq!(result.files_parsed, 1);
        assert_eq!(result.files_failed, 0);
        assert_eq!(result.declarations_extracted, 1);
        assert!(result.declarations_included >= 1);
        assert!(!decls.is_empty());
        assert_eq!(decls[0].name, "Coq.Init.Logic.eq_refl");
    }

    #[test]
    fn test_run_coq_import_multiple_decls() {
        let content = "(Theorem t1 (Prop)) (Definition d1 (Prop) (Rel 0)) (Axiom a1 (Prop))";
        let dir = make_test_dir(&[("test.sexp", content)]);
        let config = CoqLibraryConfig {
            name: "test".to_owned(),
            sexp_dir: dir.path().to_path_buf(),
            default_axiom_profile: AxiomProfile::NONE,
            expected_theorems: 10,
            phase_modules: vec![],
            exclude_prefixes: vec![],
        };
        let (decls, result) =
            run_coq_import(&config, ImportPhase::Full).expect("import should succeed");

        assert_eq!(result.declarations_extracted, 3);
        assert_eq!(result.declarations_included, 3);
        assert_eq!(decls.len(), 3);
        assert_eq!(result.kind_counts.theorems, 1);
        assert_eq!(result.kind_counts.definitions, 1);
        assert_eq!(result.kind_counts.axioms, 1);
    }

    #[test]
    fn test_run_coq_import_missing_dir() {
        let config = CoqLibraryConfig {
            name: "missing".to_owned(),
            sexp_dir: std::path::PathBuf::from("/nonexistent/path"),
            default_axiom_profile: AxiomProfile::NONE,
            expected_theorems: 0,
            phase_modules: vec![],
            exclude_prefixes: vec![],
        };
        let err = run_coq_import(&config, ImportPhase::Full).unwrap_err();
        assert!(err.to_string().contains("does not exist"));
    }

    #[test]
    fn test_run_coq_import_bad_sexp_file() {
        let dir = make_test_dir(&[("bad.sexp", "(unclosed list")]);
        let config = CoqLibraryConfig {
            name: "bad".to_owned(),
            sexp_dir: dir.path().to_path_buf(),
            default_axiom_profile: AxiomProfile::NONE,
            expected_theorems: 0,
            phase_modules: vec![],
            exclude_prefixes: vec![],
        };
        let (decls, result) =
            run_coq_import(&config, ImportPhase::Full).expect("should not hard-fail");

        assert_eq!(result.files_failed, 1);
        assert!(decls.is_empty());
        assert_eq!(result.errors.len(), 1);
    }

    #[test]
    fn test_phase_filtering() {
        let content = "(Theorem Coq.Init.Logic.foo (Prop)) (Theorem Coq.Reals.Rbase.bar (Prop))";
        let dir = make_test_dir(&[("mixed.sexp", content)]);
        let config = coq_stdlib_config(dir.path().to_path_buf());

        // Core phase: only Init should be included.
        let (decls, result) =
            run_coq_import(&config, ImportPhase::Core).expect("import should succeed");
        assert_eq!(result.declarations_extracted, 2);
        // One included (Init), one skipped (Reals).
        assert_eq!(decls.len(), 1);
        assert_eq!(decls[0].name, "Coq.Init.Logic.foo");
    }

    #[test]
    fn test_import_result_merge() {
        let mut a = ImportResult {
            declarations_extracted: 5,
            declarations_included: 3,
            files_parsed: 2,
            ..Default::default()
        };
        let b = ImportResult {
            declarations_extracted: 10,
            declarations_included: 7,
            files_parsed: 4,
            ..Default::default()
        };
        a.merge(&b);
        assert_eq!(a.declarations_extracted, 15);
        assert_eq!(a.declarations_included, 10);
        assert_eq!(a.files_parsed, 6);
    }

    #[test]
    fn test_import_result_summary() {
        let result = ImportResult {
            declarations_extracted: 100,
            declarations_included: 80,
            declarations_skipped: 15,
            declarations_axiomatized: 5,
            files_parsed: 10,
            files_failed: 1,
            ..Default::default()
        };
        let s = result.summary();
        assert!(s.contains("extracted=100"));
        assert!(s.contains("included=80"));
        assert!(s.contains("files_ok=10"));
    }

    #[test]
    fn test_default_profile_merged() {
        let content = "(Definition some_def (Prop) (Rel 0))";
        let dir = make_test_dir(&[("test.sexp", content)]);
        let config = CoqLibraryConfig {
            name: "test".to_owned(),
            sexp_dir: dir.path().to_path_buf(),
            default_axiom_profile: AxiomProfile::CLASSICAL,
            expected_theorems: 10,
            phase_modules: vec![],
            exclude_prefixes: vec![],
        };
        let (decls, _result) =
            run_coq_import(&config, ImportPhase::Full).expect("import should succeed");

        assert_eq!(decls.len(), 1);
        assert!(decls[0].axiom_profile.has(AxiomProfile::CLASSICAL));
    }

    #[test]
    fn test_empty_dir_produces_empty_result() {
        let dir = tempfile::tempdir().expect("create tempdir");
        let config = CoqLibraryConfig {
            name: "empty".to_owned(),
            sexp_dir: dir.path().to_path_buf(),
            default_axiom_profile: AxiomProfile::NONE,
            expected_theorems: 0,
            phase_modules: vec![],
            exclude_prefixes: vec![],
        };
        let (decls, result) =
            run_coq_import(&config, ImportPhase::Full).expect("import should succeed");
        assert!(decls.is_empty());
        assert_eq!(result.files_parsed, 0);
    }
}
