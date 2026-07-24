// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Lean 4 / Mathlib importer for the Mathverse Library.
//!
//! Scans `.lean` source files and extracts theorem/lemma declarations,
//! converting them into Mathverse `ImportedConstant` records with appropriate
//! trust levels and axiom profiles.
//!
//! For `.olean` binary files, delegates to `clean_olean` crate (when available).

pub mod axiom_replacement;
pub mod env_import;
pub mod kernel_verify;
pub mod mathlib_import;
pub mod mathlib_kernel_verify;
pub mod olean;
pub mod shard_verify;

use std::path::Path;

use crate::types::{AxiomProfile, Provenance, SourceSystem, TrustLevel};

use thiserror::Error;

/// Errors from Lean 4 import.
#[derive(Debug, Error)]
#[non_exhaustive]
pub enum Lean4ImportError {
    #[error("IO error: {0}")]
    Io(#[from] std::io::Error),
    #[error("parse error in {file}: {message}")]
    Parse { file: String, message: String },
}

/// A theorem or definition extracted from Lean 4 source.
#[derive(Clone, Debug)]
pub struct Lean4Theorem {
    pub name: String,
    pub kind: Lean4DeclKind,
    pub type_signature: Option<String>,
    pub source_file: String,
    pub line_number: usize,
    pub is_noncomputable: bool,
    pub uses_sorry: bool,
    pub namespace: Option<String>,
}

/// Kind of Lean 4 declaration.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum Lean4DeclKind {
    Theorem,
    Lemma,
    Definition,
    Def,
    Axiom,
    Instance,
    Class,
    Structure,
    Inductive,
    Abbrev,
}

/// Result of importing a Lean 4 source file.
#[derive(Clone, Debug)]
pub struct Lean4ImportResult {
    pub theorems: Vec<Lean4Theorem>,
    pub total_lines: usize,
    pub source_file: String,
}

/// Statistics for a batch Lean 4 import.
#[derive(Clone, Debug, Default)]
pub struct Lean4ImportStats {
    pub files_scanned: usize,
    pub files_failed: usize,
    pub theorems_found: usize,
    pub lemmas_found: usize,
    pub definitions_found: usize,
    pub axioms_found: usize,
    pub sorry_count: usize,
    pub total_lines: usize,
}

impl Lean4ImportStats {
    pub fn total_declarations(&self) -> usize {
        self.theorems_found + self.lemmas_found + self.definitions_found + self.axioms_found
    }
}

/// Import Lean 4 theorems from a `.lean` source file.
pub fn import_lean4_file(path: &Path) -> Result<Lean4ImportResult, Lean4ImportError> {
    let text = std::fs::read_to_string(path)?;
    let filename = path.display().to_string();
    let mut theorems = Vec::new();
    let mut current_namespace: Option<String> = None;

    for (line_idx, line) in text.lines().enumerate() {
        let trimmed = line.trim();

        // Track namespace
        if let Some(ns) = trimmed.strip_prefix("namespace ") {
            current_namespace = Some(ns.trim().to_owned());
            continue;
        }
        if trimmed == "end" || trimmed.starts_with("end ") {
            current_namespace = None;
            continue;
        }

        // Extract declarations
        let (kind, rest) = if let Some(r) = trimmed.strip_prefix("theorem ") {
            (Lean4DeclKind::Theorem, r)
        } else if let Some(r) = trimmed.strip_prefix("lemma ") {
            (Lean4DeclKind::Lemma, r)
        } else if let Some(r) = trimmed.strip_prefix("def ") {
            (Lean4DeclKind::Def, r)
        } else if let Some(r) = trimmed.strip_prefix("noncomputable def ") {
            (Lean4DeclKind::Def, r)
        } else if let Some(r) = trimmed.strip_prefix("axiom ") {
            (Lean4DeclKind::Axiom, r)
        } else if let Some(r) = trimmed.strip_prefix("instance ") {
            (Lean4DeclKind::Instance, r)
        } else if let Some(r) = trimmed.strip_prefix("class ") {
            (Lean4DeclKind::Class, r)
        } else if let Some(r) = trimmed.strip_prefix("structure ") {
            (Lean4DeclKind::Structure, r)
        } else if let Some(r) = trimmed.strip_prefix("inductive ") {
            (Lean4DeclKind::Inductive, r)
        } else if let Some(r) = trimmed.strip_prefix("abbrev ") {
            (Lean4DeclKind::Abbrev, r)
        } else if let Some(r) = trimmed.strip_prefix("definition ") {
            (Lean4DeclKind::Definition, r)
        } else {
            continue;
        };

        // Extract name (first identifier)
        let name = rest
            .split(|c: char| c.is_whitespace() || c == ':' || c == '(' || c == '{' || c == '[')
            .next()
            .unwrap_or("")
            .to_owned();

        if name.is_empty() || name.starts_with('-') {
            continue;
        }

        // Extract type signature (after ':' before ':=')
        let type_sig = rest
            .find(':')
            .map(|i| {
                let after_colon = &rest[i + 1..];
                after_colon
                    .find(":=")
                    .map_or(after_colon, |j| &after_colon[..j])
                    .trim()
                    .to_owned()
            })
            .filter(|s| !s.is_empty());

        let is_noncomputable = trimmed.starts_with("noncomputable");
        let uses_sorry = text
            .lines()
            .skip(line_idx)
            .take(20)
            .any(|l| l.contains("sorry"));

        let full_name = match &current_namespace {
            Some(ns) => format!("{ns}.{name}"),
            None => name,
        };

        theorems.push(Lean4Theorem {
            name: full_name,
            kind,
            type_signature: type_sig,
            source_file: filename.clone(),
            line_number: line_idx + 1,
            is_noncomputable,
            uses_sorry,
            namespace: current_namespace.clone(),
        });
    }

    Ok(Lean4ImportResult {
        theorems,
        total_lines: text.lines().count(),
        source_file: filename,
    })
}

/// Batch import all `.lean` files under a directory.
pub fn import_lean4_dir(
    dir: &Path,
) -> Result<(Vec<Lean4Theorem>, Lean4ImportStats), Lean4ImportError> {
    let mut all_theorems = Vec::new();
    let mut stats = Lean4ImportStats::default();
    let mut files = Vec::new();
    collect_files(dir, "lean", &mut files);
    files.sort();

    for path in &files {
        stats.files_scanned += 1;
        match import_lean4_file(path) {
            Ok(result) => {
                stats.total_lines += result.total_lines;
                for thm in &result.theorems {
                    match thm.kind {
                        Lean4DeclKind::Theorem => stats.theorems_found += 1,
                        Lean4DeclKind::Lemma => stats.lemmas_found += 1,
                        Lean4DeclKind::Definition | Lean4DeclKind::Def => {
                            stats.definitions_found += 1
                        }
                        Lean4DeclKind::Axiom => stats.axioms_found += 1,
                        _ => {}
                    }
                    if thm.uses_sorry {
                        stats.sorry_count += 1;
                    }
                }
                all_theorems.extend(result.theorems);
            }
            Err(_) => {
                stats.files_failed += 1;
            }
        }
    }

    Ok((all_theorems, stats))
}

/// Convert a `Lean4Theorem` to an Mathverse `Provenance`.
#[must_use]
pub fn to_provenance(thm: &Lean4Theorem) -> Provenance {
    // sorry-bearing theorems are tracked via TrustLevel rather than the axiom
    // profile; AxiomProfile::NONE is correct in both branches today.
    let profile = AxiomProfile::NONE;

    Provenance {
        source: SourceSystem::Lean4,
        original_name: thm.name.clone(),
        source_file: Some(thm.source_file.clone()),
        axiom_profile: profile,
    }
}

/// Assign trust level based on declaration properties.
#[must_use]
pub fn trust_level(thm: &Lean4Theorem) -> TrustLevel {
    if thm.uses_sorry {
        TrustLevel::TrustedOracle
    } else if thm.kind == Lean4DeclKind::Axiom {
        TrustLevel::PartiallyAxiomatized
    } else {
        // Source-level extraction without type checking.
        TrustLevel::PartiallyAxiomatized
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
    fn test_parse_lean4_theorem() {
        let src = "theorem add_comm (a b : Nat) : a + b = b + a := by mathverse\n";
        let dir = tempfile::tempdir().unwrap();
        let file = dir.path().join("test.lean");
        std::fs::write(&file, src).unwrap();

        let result = import_lean4_file(&file).unwrap();
        assert_eq!(result.theorems.len(), 1);
        assert_eq!(result.theorems[0].name, "add_comm");
        assert_eq!(result.theorems[0].kind, Lean4DeclKind::Theorem);
    }

    #[test]
    fn test_parse_lean4_namespace() {
        let src = "namespace Nat\ntheorem zero_add (n : Nat) : 0 + n = n := by simp\nend Nat\n";
        let dir = tempfile::tempdir().unwrap();
        let file = dir.path().join("test.lean");
        std::fs::write(&file, src).unwrap();

        let result = import_lean4_file(&file).unwrap();
        assert_eq!(result.theorems.len(), 1);
        assert_eq!(result.theorems[0].name, "Nat.zero_add");
    }

    #[test]
    fn test_parse_lean4_multiple_kinds() {
        let src = "\
theorem t1 : True := trivial
lemma l1 : True := trivial
def d1 : Nat := 0
axiom a1 : True
";
        let dir = tempfile::tempdir().unwrap();
        let file = dir.path().join("test.lean");
        std::fs::write(&file, src).unwrap();

        let result = import_lean4_file(&file).unwrap();
        assert_eq!(result.theorems.len(), 4);
        assert_eq!(result.theorems[0].kind, Lean4DeclKind::Theorem);
        assert_eq!(result.theorems[1].kind, Lean4DeclKind::Lemma);
        assert_eq!(result.theorems[2].kind, Lean4DeclKind::Def);
        assert_eq!(result.theorems[3].kind, Lean4DeclKind::Axiom);
    }

    #[test]
    fn test_trust_level_sorry() {
        let thm = Lean4Theorem {
            name: "test".to_owned(),
            kind: Lean4DeclKind::Theorem,
            type_signature: None,
            source_file: "test.lean".to_owned(),
            line_number: 1,
            is_noncomputable: false,
            uses_sorry: true,
            namespace: None,
        };
        assert_eq!(trust_level(&thm), TrustLevel::TrustedOracle);
    }

    #[test]
    fn test_import_stats_total() {
        let stats = Lean4ImportStats {
            files_scanned: 10,
            files_failed: 0,
            theorems_found: 5,
            lemmas_found: 3,
            definitions_found: 2,
            axioms_found: 1,
            sorry_count: 0,
            total_lines: 100,
        };
        assert_eq!(stats.total_declarations(), 11);
    }
}
