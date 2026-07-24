// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Coq / Gallina importer for the Mathverse Library.
//!
//! Parses `.v` source files, extracting theorem, lemma, definition, and
//! axiom declarations. Maps Coq's proof status and axiom usage to Mathverse
//! trust levels and axiom profiles.

use std::path::Path;

use crate::types::{AxiomProfile, Provenance, SourceSystem, TrustLevel};

use thiserror::Error;

// --- Consolidated coq_* submodules (flat moves from crate root) ---
// Each was previously a top-level `coq_X` module; re-exported under the
// original `crate::coq_X` path via aliases in lib.rs to preserve all
// existing caller paths.
pub mod advanced;
pub mod alpha;
pub(crate) mod axiom_map;
pub mod ecosystem;
pub mod extended;
pub mod module;
pub mod print_parser;
pub mod proof;
pub mod real_data;
pub mod shard;
pub mod stdlib;
pub mod typeclass;
pub mod universe;
pub mod universe_releveling;
pub mod v_import;
pub mod v_type_parser;
pub mod vo;

/// Errors from Coq import.
#[derive(Debug, Error)]
#[non_exhaustive]
pub enum CoqImportError {
    #[error("IO error: {0}")]
    Io(#[from] std::io::Error),
    #[error("parse error in {file}: {message}")]
    Parse { file: String, message: String },
}

/// A declaration extracted from a Coq `.v` file.
#[derive(Clone, Debug)]
pub struct CoqDeclaration {
    pub name: String,
    pub kind: CoqDeclKind,
    pub type_signature: Option<String>,
    pub source_file: String,
    pub line_number: usize,
    pub module_path: Option<String>,
    pub uses_axiom: bool,
}

/// Kind of Coq declaration.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum CoqDeclKind {
    Theorem,
    Lemma,
    Proposition,
    Corollary,
    Fact,
    Remark,
    Definition,
    Fixpoint,
    CoFixpoint,
    Inductive,
    CoInductive,
    Record,
    Class,
    Instance,
    Axiom,
    Parameter,
    Hypothesis,
    Variable,
    Program,
}

/// Result of importing a single Coq file.
#[derive(Clone, Debug)]
pub struct CoqFileResult {
    pub declarations: Vec<CoqDeclaration>,
    pub total_lines: usize,
    pub source_file: String,
}

/// Statistics for batch Coq import.
#[derive(Clone, Debug, Default)]
pub struct CoqImportStats {
    pub files_scanned: usize,
    pub files_failed: usize,
    pub theorems_found: usize,
    pub lemmas_found: usize,
    pub definitions_found: usize,
    pub axioms_found: usize,
    pub inductives_found: usize,
    pub total_lines: usize,
}

impl CoqImportStats {
    pub fn total_declarations(&self) -> usize {
        self.theorems_found
            + self.lemmas_found
            + self.definitions_found
            + self.axioms_found
            + self.inductives_found
    }
}

/// Import declarations from a single Coq `.v` file.
pub fn import_coq_file(path: &Path) -> Result<CoqFileResult, CoqImportError> {
    let text = std::fs::read_to_string(path)?;
    let filename = path.display().to_string();
    let mut declarations = Vec::new();
    let mut current_module: Option<String> = None;

    for (line_idx, line) in text.lines().enumerate() {
        let trimmed = line.trim();

        // Track modules
        if let Some(rest) = trimmed.strip_prefix("Module ") {
            let name = rest
                .split_whitespace()
                .next()
                .unwrap_or("")
                .trim_end_matches('.');
            if !name.is_empty() {
                current_module = Some(name.to_owned());
            }
            continue;
        }
        if trimmed.starts_with("End ") {
            current_module = None;
            continue;
        }

        // Skip comments
        if trimmed.starts_with("(*") {
            continue;
        }

        let (kind, rest) = if let Some(r) = trimmed.strip_prefix("Theorem ") {
            (CoqDeclKind::Theorem, r)
        } else if let Some(r) = trimmed.strip_prefix("Lemma ") {
            (CoqDeclKind::Lemma, r)
        } else if let Some(r) = trimmed.strip_prefix("Proposition ") {
            (CoqDeclKind::Proposition, r)
        } else if let Some(r) = trimmed.strip_prefix("Corollary ") {
            (CoqDeclKind::Corollary, r)
        } else if let Some(r) = trimmed.strip_prefix("Fact ") {
            (CoqDeclKind::Fact, r)
        } else if let Some(r) = trimmed.strip_prefix("Remark ") {
            (CoqDeclKind::Remark, r)
        } else if let Some(r) = trimmed.strip_prefix("Definition ") {
            (CoqDeclKind::Definition, r)
        } else if let Some(r) = trimmed.strip_prefix("Fixpoint ") {
            (CoqDeclKind::Fixpoint, r)
        } else if let Some(r) = trimmed.strip_prefix("CoFixpoint ") {
            (CoqDeclKind::CoFixpoint, r)
        } else if let Some(r) = trimmed.strip_prefix("Inductive ") {
            (CoqDeclKind::Inductive, r)
        } else if let Some(r) = trimmed.strip_prefix("CoInductive ") {
            (CoqDeclKind::CoInductive, r)
        } else if let Some(r) = trimmed.strip_prefix("Record ") {
            (CoqDeclKind::Record, r)
        } else if let Some(r) = trimmed.strip_prefix("Class ") {
            (CoqDeclKind::Class, r)
        } else if let Some(r) = trimmed.strip_prefix("Instance ") {
            (CoqDeclKind::Instance, r)
        } else if let Some(r) = trimmed.strip_prefix("Axiom ") {
            (CoqDeclKind::Axiom, r)
        } else if let Some(r) = trimmed.strip_prefix("Parameter ") {
            (CoqDeclKind::Parameter, r)
        } else if let Some(r) = trimmed.strip_prefix("Hypothesis ") {
            (CoqDeclKind::Hypothesis, r)
        } else if let Some(r) = trimmed.strip_prefix("Variable ") {
            (CoqDeclKind::Variable, r)
        } else if let Some(r) = trimmed.strip_prefix("Program Definition ") {
            (CoqDeclKind::Program, r)
        } else if let Some(r) = trimmed.strip_prefix("Program Lemma ") {
            (CoqDeclKind::Lemma, r)
        } else if let Some(r) = trimmed.strip_prefix("Program Theorem ") {
            (CoqDeclKind::Theorem, r)
        } else {
            continue;
        };

        let name = rest
            .split(|c: char| c.is_whitespace() || c == ':' || c == '(' || c == '{')
            .next()
            .unwrap_or("")
            .to_owned();

        if name.is_empty() {
            continue;
        }

        let type_sig = rest
            .find(':')
            .map(|i| {
                let after = &rest[i + 1..];
                after
                    .find(":=")
                    .or_else(|| after.find('.'))
                    .map_or(after, |j| &after[..j])
                    .trim()
                    .to_owned()
            })
            .filter(|s| !s.is_empty());

        let full_name = match &current_module {
            Some(m) => format!("{m}.{name}"),
            None => name,
        };

        declarations.push(CoqDeclaration {
            name: full_name,
            kind,
            type_signature: type_sig,
            source_file: filename.clone(),
            line_number: line_idx + 1,
            module_path: current_module.clone(),
            uses_axiom: matches!(
                kind,
                CoqDeclKind::Axiom | CoqDeclKind::Parameter | CoqDeclKind::Hypothesis
            ),
        });
    }

    Ok(CoqFileResult {
        declarations,
        total_lines: text.lines().count(),
        source_file: filename,
    })
}

/// Batch import all `.v` files under a directory.
pub fn import_coq_dir(dir: &Path) -> Result<(Vec<CoqDeclaration>, CoqImportStats), CoqImportError> {
    let mut all_decls = Vec::new();
    let mut stats = CoqImportStats::default();
    let mut files = Vec::new();
    collect_files(dir, "v", &mut files);
    files.sort();

    for path in &files {
        stats.files_scanned += 1;
        match import_coq_file(path) {
            Ok(result) => {
                stats.total_lines += result.total_lines;
                for decl in &result.declarations {
                    match decl.kind {
                        CoqDeclKind::Theorem
                        | CoqDeclKind::Proposition
                        | CoqDeclKind::Corollary
                        | CoqDeclKind::Fact => {
                            stats.theorems_found += 1;
                        }
                        CoqDeclKind::Lemma | CoqDeclKind::Remark => {
                            stats.lemmas_found += 1;
                        }
                        CoqDeclKind::Definition
                        | CoqDeclKind::Fixpoint
                        | CoqDeclKind::CoFixpoint
                        | CoqDeclKind::Program => {
                            stats.definitions_found += 1;
                        }
                        CoqDeclKind::Axiom
                        | CoqDeclKind::Parameter
                        | CoqDeclKind::Hypothesis
                        | CoqDeclKind::Variable => {
                            stats.axioms_found += 1;
                        }
                        CoqDeclKind::Inductive
                        | CoqDeclKind::CoInductive
                        | CoqDeclKind::Record
                        | CoqDeclKind::Class => {
                            stats.inductives_found += 1;
                        }
                        CoqDeclKind::Instance => {}
                    }
                }
                all_decls.extend(result.declarations);
            }
            Err(_) => {
                stats.files_failed += 1;
            }
        }
    }

    Ok((all_decls, stats))
}

/// Assign axiom profile for a Coq declaration.
#[must_use]
pub fn axiom_profile(decl: &CoqDeclaration) -> AxiomProfile {
    if decl.uses_axiom {
        AxiomProfile::CLASSICAL // Conservative: Coq axioms often use classical reasoning
    } else if matches!(
        decl.kind,
        CoqDeclKind::CoInductive | CoqDeclKind::CoFixpoint
    ) {
        AxiomProfile::COQ_COINDUCTIVE
    } else {
        AxiomProfile::NONE
    }
}

/// Assign trust level for a Coq declaration.
#[must_use]
pub fn trust_level(decl: &CoqDeclaration) -> TrustLevel {
    if decl.uses_axiom {
        TrustLevel::PartiallyAxiomatized
    } else {
        // Source-level extraction; full verification requires Coq kernel replay.
        TrustLevel::PartiallyAxiomatized
    }
}

/// Convert to Mathverse provenance.
#[must_use]
pub fn to_provenance(decl: &CoqDeclaration) -> Provenance {
    Provenance {
        source: SourceSystem::Coq,
        original_name: decl.name.clone(),
        source_file: Some(decl.source_file.clone()),
        axiom_profile: axiom_profile(decl),
    }
}

fn collect_files(dir: &Path, ext: &str, out: &mut Vec<std::path::PathBuf>) {
    if let Ok(rd) = std::fs::read_dir(dir) {
        for entry in rd.filter_map(|e| e.ok()) {
            let path = entry.path();
            if path.is_dir() {
                collect_files(&path, ext, out);
            } else if path.extension().is_some_and(|e| e == ext) {
                out.push(path);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_coq_theorem() {
        let src = "Theorem add_comm : forall n m : nat, n + m = m + n.\nProof. mathverse. Qed.\n";
        let dir = tempfile::tempdir().unwrap();
        let file = dir.path().join("test.v");
        std::fs::write(&file, src).unwrap();

        let result = import_coq_file(&file).unwrap();
        assert_eq!(result.declarations.len(), 1);
        assert_eq!(result.declarations[0].name, "add_comm");
        assert_eq!(result.declarations[0].kind, CoqDeclKind::Theorem);
    }

    #[test]
    fn test_parse_coq_multiple_kinds() {
        let src = "\
Theorem t1 : True. Proof. trivial. Qed.
Lemma l1 : True. Proof. trivial. Qed.
Definition d1 := 0.
Axiom a1 : True.
Inductive mytype := C1 | C2.
";
        let dir = tempfile::tempdir().unwrap();
        let file = dir.path().join("test.v");
        std::fs::write(&file, src).unwrap();

        let result = import_coq_file(&file).unwrap();
        assert_eq!(result.declarations.len(), 5);
        assert_eq!(result.declarations[0].kind, CoqDeclKind::Theorem);
        assert_eq!(result.declarations[1].kind, CoqDeclKind::Lemma);
        assert_eq!(result.declarations[2].kind, CoqDeclKind::Definition);
        assert_eq!(result.declarations[3].kind, CoqDeclKind::Axiom);
        assert_eq!(result.declarations[4].kind, CoqDeclKind::Inductive);
    }

    #[test]
    fn test_coq_axiom_profile() {
        let axiom_decl = CoqDeclaration {
            name: "ax".to_owned(),
            kind: CoqDeclKind::Axiom,
            type_signature: None,
            source_file: "test.v".to_owned(),
            line_number: 1,
            module_path: None,
            uses_axiom: true,
        };
        assert!(axiom_profile(&axiom_decl).contains(AxiomProfile::CLASSICAL));
    }

    #[test]
    fn test_coq_trust_level() {
        let thm = CoqDeclaration {
            name: "thm".to_owned(),
            kind: CoqDeclKind::Theorem,
            type_signature: None,
            source_file: "test.v".to_owned(),
            line_number: 1,
            module_path: None,
            uses_axiom: false,
        };
        assert_eq!(trust_level(&thm), TrustLevel::PartiallyAxiomatized);
    }

    #[test]
    fn test_coq_import_stats_total() {
        let stats = CoqImportStats {
            files_scanned: 10,
            files_failed: 0,
            theorems_found: 5,
            lemmas_found: 3,
            definitions_found: 2,
            axioms_found: 1,
            inductives_found: 4,
            total_lines: 500,
        };
        assert_eq!(stats.total_declarations(), 15);
    }

    #[test]
    fn test_parse_coq_with_module() {
        let src = "Module Foo.\nLemma bar : True. Proof. trivial. Qed.\nEnd Foo.\n";
        let dir = tempfile::tempdir().unwrap();
        let file = dir.path().join("test.v");
        std::fs::write(&file, src).unwrap();

        let result = import_coq_file(&file).unwrap();
        assert_eq!(result.declarations.len(), 1);
        assert_eq!(result.declarations[0].name, "Foo.bar");
    }
}
