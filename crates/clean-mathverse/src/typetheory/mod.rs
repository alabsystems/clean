// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Type-theory system importers.
//!
//! Parses source files from dependent type theory and logical framework
//! systems and extracts declarations (postulates, data types, records,
//! proofs) into Mathverse format.
//!
//! ## Supported systems
//!
//! - **Agda** (`.agda`) — core module
//! - **Idris 2** (`.idr`) — core module
//! - **Dedukti** (`.dk`) — also covers Krajono, dedukti-libs
//! - **Lambdapi** (`.lp`)
//! - **Cubical TT** (`.ctt`), **cooltt** (`.cooltt`), **redtt** (`.red`)
//! - **Abella** (`.thm`), **Beluga** (`.bel`), **Twelf** (`.elf`),
//!   **Naproche** (`.ftl`), **Minlog** (`.scm`)
//! - **Arend** (`.ard`), **Metamath Zero** (`.mm0`/`.mm1`),
//!   **Kind2** (`.kind2`/`.kind`), **Rzk** (`.rzk`)
//! - **Cedille** (`.ced`), **ATS2** (`.sats`/`.dats`), **LaTTe** (`.clj`)

use std::path::Path;

use crate::types::{AxiomProfile, Provenance, SourceSystem, TrustLevel};

use thiserror::Error;

pub mod cubical;
pub mod dedukti;
pub mod hott;
pub mod lambdapi;
pub mod logical_frameworks;
pub mod other;

/// Errors from type-theory imports.
#[derive(Debug, Error)]
#[non_exhaustive]
pub enum TypeTheoryError {
    #[error("IO error: {0}")]
    Io(#[from] std::io::Error),
    #[error("parse error in {file}: {message}")]
    Parse { file: String, message: String },
}

// ─── Agda ────────────────────────────────────────────────────────────────

/// A declaration extracted from an Agda `.agda` file.
#[derive(Clone, Debug)]
pub struct AgdaDeclaration {
    pub name: String,
    pub kind: AgdaDeclKind,
    pub type_signature: Option<String>,
    pub source_file: String,
    pub line_number: usize,
    pub module_name: Option<String>,
    pub is_postulate: bool,
}

/// Kind of Agda declaration.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum AgdaDeclKind {
    /// Type signature (name : Type).
    TypeSig,
    /// Data type definition.
    Data,
    /// Record type definition.
    Record,
    /// Postulate (axiom).
    Postulate,
    /// Module definition.
    Module,
    /// Pattern function clause.
    FunctionClause,
    /// Abstract declaration.
    Abstract,
    /// Mutual block.
    Mutual,
}

/// Import declarations from an Agda `.agda` file.
pub fn import_agda_file(path: &Path) -> Result<Vec<AgdaDeclaration>, TypeTheoryError> {
    let raw_text = std::fs::read_to_string(path)?;
    let text = if path.to_string_lossy().ends_with(".lagda.md") {
        extract_literate_agda(&raw_text)
    } else {
        raw_text
    };
    let filename = path.display().to_string();
    let mut decls = Vec::new();
    let mut current_module: Option<String> = None;
    let mut in_postulate_block = false;

    for (line_idx, line) in text.lines().enumerate() {
        let trimmed = line.trim();

        // Skip comments
        if trimmed.starts_with("--") || trimmed.starts_with("{-") {
            continue;
        }

        // Track modules
        if let Some(rest) = trimmed.strip_prefix("module ") {
            let name = rest.split_whitespace().next().unwrap_or("").to_owned();
            if !name.is_empty() && name != "where" {
                current_module = Some(name.clone());
                decls.push(AgdaDeclaration {
                    name,
                    kind: AgdaDeclKind::Module,
                    type_signature: None,
                    source_file: filename.clone(),
                    line_number: line_idx + 1,
                    module_name: current_module.clone(),
                    is_postulate: false,
                });
            }
            continue;
        }

        // Postulate block
        if trimmed == "postulate" {
            in_postulate_block = true;
            continue;
        }

        // Data type
        if let Some(rest) = trimmed.strip_prefix("data ") {
            in_postulate_block = false;
            let name = rest
                .split(|c: char| c.is_whitespace() || c == ':')
                .next()
                .unwrap_or("")
                .to_owned();
            if !name.is_empty() {
                let full_name = qualify(&current_module, &name);
                decls.push(AgdaDeclaration {
                    name: full_name,
                    kind: AgdaDeclKind::Data,
                    type_signature: rest.find(':').map(|i| rest[i + 1..].trim().to_owned()),
                    source_file: filename.clone(),
                    line_number: line_idx + 1,
                    module_name: current_module.clone(),
                    is_postulate: false,
                });
            }
            continue;
        }

        // Record type
        if let Some(rest) = trimmed.strip_prefix("record ") {
            in_postulate_block = false;
            let name = rest
                .split(|c: char| c.is_whitespace() || c == ':')
                .next()
                .unwrap_or("")
                .to_owned();
            if !name.is_empty() {
                let full_name = qualify(&current_module, &name);
                decls.push(AgdaDeclaration {
                    name: full_name,
                    kind: AgdaDeclKind::Record,
                    type_signature: rest.find(':').map(|i| rest[i + 1..].trim().to_owned()),
                    source_file: filename.clone(),
                    line_number: line_idx + 1,
                    module_name: current_module.clone(),
                    is_postulate: false,
                });
            }
            continue;
        }

        // Type signatures (name : Type) — indented under postulate or at top level
        if trimmed.contains(" : ") && !trimmed.starts_with('=') && !trimmed.starts_with('|') {
            let parts: Vec<&str> = trimmed.splitn(2, " : ").collect();
            if parts.len() == 2 {
                let name = parts[0].trim().to_owned();
                if !name.is_empty()
                    && !name.contains(' ')
                    && name
                        .chars()
                        .next()
                        .is_some_and(|c| c.is_alphabetic() || c == '_')
                {
                    let full_name = qualify(&current_module, &name);
                    let is_postulate = in_postulate_block || line.starts_with("  ");
                    decls.push(AgdaDeclaration {
                        name: full_name,
                        kind: if is_postulate && in_postulate_block {
                            AgdaDeclKind::Postulate
                        } else {
                            AgdaDeclKind::TypeSig
                        },
                        type_signature: Some(parts[1].trim().to_owned()),
                        source_file: filename.clone(),
                        line_number: line_idx + 1,
                        module_name: current_module.clone(),
                        is_postulate: in_postulate_block,
                    });
                }
            }
        }

        // Non-indented, non-keyword line → end postulate block
        if !line.starts_with(' ') && !line.starts_with('\t') && !trimmed.is_empty() {
            in_postulate_block = false;
        }
    }

    Ok(decls)
}

// ─── Idris 2 ─────────────────────────────────────────────────────────────

/// A declaration extracted from an Idris 2 `.idr` file.
#[derive(Clone, Debug)]
pub struct IdrisDeclaration {
    pub name: String,
    pub kind: IdrisDeclKind,
    pub type_signature: Option<String>,
    pub source_file: String,
    pub line_number: usize,
    pub module_name: Option<String>,
    pub is_total: bool,
    pub quantity: Option<String>,
}

/// Kind of Idris 2 declaration.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum IdrisDeclKind {
    /// Type signature.
    TypeSig,
    /// Data type.
    Data,
    /// Record.
    Record,
    /// Interface (typeclass).
    Interface,
    /// Implementation.
    Implementation,
    /// Function clause.
    FunctionClause,
    /// Postulate.
    Postulate,
    /// Namespace.
    Namespace,
}

/// Import declarations from an Idris 2 `.idr` file.
pub fn import_idris_file(path: &Path) -> Result<Vec<IdrisDeclaration>, TypeTheoryError> {
    let text = std::fs::read_to_string(path)?;
    let filename = path.display().to_string();
    let mut decls = Vec::new();
    let mut current_module: Option<String> = None;
    let mut is_total = false;

    for (line_idx, line) in text.lines().enumerate() {
        let trimmed = line.trim();

        // Skip comments
        if trimmed.starts_with("--") || trimmed.starts_with("{-") {
            continue;
        }

        // Module declaration
        if let Some(rest) = trimmed.strip_prefix("module ") {
            current_module = Some(rest.trim().to_owned());
            continue;
        }

        // Totality annotations
        if trimmed == "total" || trimmed == "%default total" {
            is_total = true;
            continue;
        }
        if trimmed == "partial" {
            is_total = false;
            continue;
        }

        // Namespace
        if let Some(rest) = trimmed.strip_prefix("namespace ") {
            let name = rest.trim().to_owned();
            decls.push(IdrisDeclaration {
                name: name.clone(),
                kind: IdrisDeclKind::Namespace,
                type_signature: None,
                source_file: filename.clone(),
                line_number: line_idx + 1,
                module_name: current_module.clone(),
                is_total: false,
                quantity: None,
            });
            continue;
        }

        // Data type
        if let Some(rest) = trimmed.strip_prefix("data ") {
            let name = rest
                .split(|c: char| c.is_whitespace() || c == ':' || c == '=')
                .next()
                .unwrap_or("")
                .to_owned();
            if !name.is_empty() {
                decls.push(IdrisDeclaration {
                    name: qualify(&current_module, &name),
                    kind: IdrisDeclKind::Data,
                    type_signature: rest.find(':').map(|i| rest[i + 1..].trim().to_owned()),
                    source_file: filename.clone(),
                    line_number: line_idx + 1,
                    module_name: current_module.clone(),
                    is_total,
                    quantity: None,
                });
            }
            continue;
        }

        // Record
        if let Some(rest) = trimmed.strip_prefix("record ") {
            let name = rest.split_whitespace().next().unwrap_or("").to_owned();
            if !name.is_empty() {
                decls.push(IdrisDeclaration {
                    name: qualify(&current_module, &name),
                    kind: IdrisDeclKind::Record,
                    type_signature: None,
                    source_file: filename.clone(),
                    line_number: line_idx + 1,
                    module_name: current_module.clone(),
                    is_total,
                    quantity: None,
                });
            }
            continue;
        }

        // Interface
        if let Some(rest) = trimmed.strip_prefix("interface ") {
            let name = rest.split_whitespace().next().unwrap_or("").to_owned();
            if !name.is_empty() {
                decls.push(IdrisDeclaration {
                    name: qualify(&current_module, &name),
                    kind: IdrisDeclKind::Interface,
                    type_signature: None,
                    source_file: filename.clone(),
                    line_number: line_idx + 1,
                    module_name: current_module.clone(),
                    is_total,
                    quantity: None,
                });
            }
            continue;
        }

        // Type signatures (name : Type)
        if trimmed.contains(" : ")
            && !trimmed.starts_with('=')
            && !trimmed.starts_with('|')
            && !trimmed.starts_with("import")
            && !trimmed.starts_with("let ")
        {
            let parts: Vec<&str> = trimmed.splitn(2, " : ").collect();
            if parts.len() == 2 {
                let name = parts[0].trim().to_owned();
                if !name.is_empty()
                    && !name.contains(' ')
                    && name
                        .chars()
                        .next()
                        .is_some_and(|c| c.is_alphabetic() || c == '_')
                {
                    // Check for quantity annotation
                    let quantity = if name.starts_with('0') || name.starts_with('1') {
                        Some(name[..1].to_owned())
                    } else {
                        None
                    };
                    decls.push(IdrisDeclaration {
                        name: qualify(&current_module, &name),
                        kind: IdrisDeclKind::TypeSig,
                        type_signature: Some(parts[1].trim().to_owned()),
                        source_file: filename.clone(),
                        line_number: line_idx + 1,
                        module_name: current_module.clone(),
                        is_total,
                        quantity,
                    });
                }
            }
        }
    }

    Ok(decls)
}

// ─── Batch import ────────────────────────────────────────────────────────

/// Statistics for type-theory batch imports.
#[derive(Clone, Debug, Default)]
pub struct TypeTheoryImportStats {
    pub files_scanned: usize,
    pub files_failed: usize,
    pub declarations_found: usize,
    pub postulates_found: usize,
    pub data_types_found: usize,
    pub type_sigs_found: usize,
    pub total_lines: usize,
}

impl TypeTheoryImportStats {
    pub fn total(&self) -> usize {
        self.declarations_found
    }
}

/// Batch import Agda files from a directory.
pub fn import_agda_dir(
    dir: &Path,
) -> Result<(Vec<AgdaDeclaration>, TypeTheoryImportStats), TypeTheoryError> {
    let mut all_decls = Vec::new();
    let mut stats = TypeTheoryImportStats::default();
    let mut files = Vec::new();
    collect_files(dir, "agda", &mut files);
    collect_lagda_md_files(dir, &mut files);
    files.sort();

    for path in &files {
        stats.files_scanned += 1;
        match import_agda_file(path) {
            Ok(decls) => {
                for d in &decls {
                    stats.declarations_found += 1;
                    match d.kind {
                        AgdaDeclKind::Postulate => stats.postulates_found += 1,
                        AgdaDeclKind::Data => stats.data_types_found += 1,
                        AgdaDeclKind::TypeSig => stats.type_sigs_found += 1,
                        _ => {}
                    }
                }
                all_decls.extend(decls);
            }
            Err(_) => stats.files_failed += 1,
        }
    }

    Ok((all_decls, stats))
}

/// Batch import Idris 2 files from a directory.
pub fn import_idris_dir(
    dir: &Path,
) -> Result<(Vec<IdrisDeclaration>, TypeTheoryImportStats), TypeTheoryError> {
    let mut all_decls = Vec::new();
    let mut stats = TypeTheoryImportStats::default();
    let mut files = Vec::new();
    collect_files(dir, "idr", &mut files);
    files.sort();

    for path in &files {
        stats.files_scanned += 1;
        match import_idris_file(path) {
            Ok(decls) => {
                for d in &decls {
                    stats.declarations_found += 1;
                    match d.kind {
                        IdrisDeclKind::Postulate => stats.postulates_found += 1,
                        IdrisDeclKind::Data => stats.data_types_found += 1,
                        IdrisDeclKind::TypeSig => stats.type_sigs_found += 1,
                        _ => {}
                    }
                }
                all_decls.extend(decls);
            }
            Err(_) => stats.files_failed += 1,
        }
    }

    Ok((all_decls, stats))
}

// ─── Batch imports for new type-theory submodules ────────────────────────

/// Batch import Dedukti files from a directory (covers `.dk` format).
pub fn import_dedukti_dir(
    dir: &Path,
) -> Result<(Vec<dedukti::DeduktiDeclaration>, TypeTheoryImportStats), TypeTheoryError> {
    let mut all_decls = Vec::new();
    let mut stats = TypeTheoryImportStats::default();
    let mut files = Vec::new();
    collect_files(dir, "dk", &mut files);
    files.sort();

    for path in &files {
        stats.files_scanned += 1;
        match dedukti::import_dedukti_file(path) {
            Ok(decls) => {
                stats.declarations_found += decls.len();
                all_decls.extend(decls);
            }
            Err(_) => stats.files_failed += 1,
        }
    }
    Ok((all_decls, stats))
}

/// Batch import Lambdapi files from a directory.
pub fn import_lambdapi_dir(
    dir: &Path,
) -> Result<(Vec<lambdapi::LambdapiDeclaration>, TypeTheoryImportStats), TypeTheoryError> {
    let mut all_decls = Vec::new();
    let mut stats = TypeTheoryImportStats::default();
    let mut files = Vec::new();
    collect_files(dir, "lp", &mut files);
    files.sort();

    for path in &files {
        stats.files_scanned += 1;
        match lambdapi::import_lambdapi_file(path) {
            Ok(decls) => {
                stats.declarations_found += decls.len();
                all_decls.extend(decls);
            }
            Err(_) => stats.files_failed += 1,
        }
    }
    Ok((all_decls, stats))
}

/// Batch import cubical type theory files from a directory.
///
/// Collects `.ctt`, `.cooltt`, and `.red` files.
pub fn import_cubical_dir(
    dir: &Path,
) -> Result<(Vec<cubical::CubicalDeclaration>, TypeTheoryImportStats), TypeTheoryError> {
    let mut all_decls = Vec::new();
    let mut stats = TypeTheoryImportStats::default();

    let importers: Vec<(
        &str,
        fn(&Path) -> Result<Vec<cubical::CubicalDeclaration>, TypeTheoryError>,
    )> = vec![
        ("ctt", cubical::import_cubicaltt_file),
        ("cooltt", cubical::import_cooltt_file),
        ("red", cubical::import_redtt_file),
    ];
    for (ext, import_fn) in importers {
        let mut files = Vec::new();
        collect_files(dir, ext, &mut files);
        files.sort();
        for path in &files {
            stats.files_scanned += 1;
            match import_fn(path) {
                Ok(decls) => {
                    stats.declarations_found += decls.len();
                    all_decls.extend(decls);
                }
                Err(_) => stats.files_failed += 1,
            }
        }
    }
    Ok((all_decls, stats))
}

/// Batch import logical framework files from a directory.
///
/// Collects `.thm` (Abella), `.bel` (Beluga), `.elf` (Twelf),
/// `.ftl` (Naproche), and `.scm` (Minlog) files.
pub fn import_lf_dir(
    dir: &Path,
) -> Result<
    (
        Vec<logical_frameworks::LfDeclaration>,
        TypeTheoryImportStats,
    ),
    TypeTheoryError,
> {
    let mut all_decls = Vec::new();
    let mut stats = TypeTheoryImportStats::default();

    let importers: Vec<(
        &str,
        fn(&Path) -> Result<Vec<logical_frameworks::LfDeclaration>, TypeTheoryError>,
    )> = vec![
        ("thm", logical_frameworks::import_abella_file),
        ("bel", logical_frameworks::import_beluga_file),
        ("elf", logical_frameworks::import_twelf_file),
        ("ftl", logical_frameworks::import_naproche_file),
        ("scm", logical_frameworks::import_minlog_file),
    ];
    for (ext, import_fn) in importers {
        let mut files = Vec::new();
        collect_files(dir, ext, &mut files);
        files.sort();
        for path in &files {
            stats.files_scanned += 1;
            match import_fn(path) {
                Ok(decls) => {
                    stats.declarations_found += decls.len();
                    all_decls.extend(decls);
                }
                Err(_) => stats.files_failed += 1,
            }
        }
    }
    Ok((all_decls, stats))
}

/// Batch import HoTT / dependent type system files from a directory.
///
/// Collects `.ard` (Arend), `.mm0`/`.mm1` (Metamath Zero),
/// `.kind2`/`.kind` (Kind2), and `.rzk` (Rzk) files.
pub fn import_hott_dir(
    dir: &Path,
) -> Result<(Vec<hott::HottDeclaration>, TypeTheoryImportStats), TypeTheoryError> {
    let mut all_decls = Vec::new();
    let mut stats = TypeTheoryImportStats::default();

    let importers: Vec<(
        &str,
        fn(&Path) -> Result<Vec<hott::HottDeclaration>, TypeTheoryError>,
    )> = vec![
        ("ard", hott::import_arend_file),
        ("mm0", hott::import_mm0_file),
        ("mm1", hott::import_mm0_file),
        ("kind2", hott::import_kind2_file),
        ("kind", hott::import_kind2_file),
        ("rzk", hott::import_rzk_file),
    ];
    for (ext, import_fn) in importers {
        let mut files = Vec::new();
        collect_files(dir, ext, &mut files);
        files.sort();
        for path in &files {
            stats.files_scanned += 1;
            match import_fn(path) {
                Ok(decls) => {
                    stats.declarations_found += decls.len();
                    all_decls.extend(decls);
                }
                Err(_) => stats.files_failed += 1,
            }
        }
    }
    Ok((all_decls, stats))
}

/// Batch import "other" type theory files from a directory.
///
/// Collects `.ced` (Cedille), `.sats`/`.dats` (ATS2), and `.clj` (LaTTe) files.
pub fn import_other_tt_dir(
    dir: &Path,
) -> Result<(Vec<other::OtherTTDeclaration>, TypeTheoryImportStats), TypeTheoryError> {
    let mut all_decls = Vec::new();
    let mut stats = TypeTheoryImportStats::default();

    let importers: Vec<(
        &str,
        fn(&Path) -> Result<Vec<other::OtherTTDeclaration>, TypeTheoryError>,
    )> = vec![
        ("ced", other::import_cedille_file),
        ("sats", other::import_ats2_file),
        ("dats", other::import_ats2_file),
        ("clj", other::import_latte_file),
    ];
    for (ext, import_fn) in importers {
        let mut files = Vec::new();
        collect_files(dir, ext, &mut files);
        files.sort();
        for path in &files {
            stats.files_scanned += 1;
            match import_fn(path) {
                Ok(decls) => {
                    stats.declarations_found += decls.len();
                    all_decls.extend(decls);
                }
                Err(_) => stats.files_failed += 1,
            }
        }
    }
    Ok((all_decls, stats))
}

/// Assign axiom profile for Agda.
#[must_use]
pub fn agda_axiom_profile(decl: &AgdaDeclaration) -> AxiomProfile {
    if decl.is_postulate {
        AxiomProfile::AGDA_CUBICAL
    } else {
        AxiomProfile::NONE
    }
}

/// Assign axiom profile for Idris 2.
#[must_use]
pub fn idris_axiom_profile(decl: &IdrisDeclaration) -> AxiomProfile {
    if matches!(decl.kind, IdrisDeclKind::Postulate) {
        AxiomProfile::IDRIS_QTT
    } else {
        AxiomProfile::NONE
    }
}

/// Assign trust level for Agda.
///
/// Both postulates and source-extracted definitions currently land at
/// `PartiallyAxiomatized` until kernel-replay support arrives; the
/// `decl` argument is kept for forward compatibility.
#[must_use]
pub fn agda_trust_level(_decl: &AgdaDeclaration) -> TrustLevel {
    TrustLevel::PartiallyAxiomatized
}

/// Assign trust level for Idris 2.
///
/// Postulates, total-function extractions, and partial extractions all
/// currently land at `PartiallyAxiomatized`; the `decl` argument is kept
/// for forward compatibility when these classes diverge.
#[must_use]
pub fn idris_trust_level(_decl: &IdrisDeclaration) -> TrustLevel {
    TrustLevel::PartiallyAxiomatized
}

/// Convert Agda declaration to Mathverse provenance.
#[must_use]
pub fn agda_provenance(decl: &AgdaDeclaration) -> Provenance {
    Provenance {
        source: SourceSystem::Agda,
        original_name: decl.name.clone(),
        source_file: Some(decl.source_file.clone()),
        axiom_profile: agda_axiom_profile(decl),
    }
}

/// Convert Idris 2 declaration to Mathverse provenance.
#[must_use]
pub fn idris_provenance(decl: &IdrisDeclaration) -> Provenance {
    Provenance {
        source: SourceSystem::Idris2,
        original_name: decl.name.clone(),
        source_file: Some(decl.source_file.clone()),
        axiom_profile: idris_axiom_profile(decl),
    }
}

fn qualify(module: &Option<String>, name: &str) -> String {
    match module {
        Some(m) => format!("{m}.{name}"),
        None => name.to_owned(),
    }
}

fn extract_literate_agda(text: &str) -> String {
    let mut code = String::new();
    let mut in_block = false;
    for line in text.lines() {
        if line.trim_start().starts_with("```agda") {
            in_block = true;
        } else if in_block && line.trim_start().starts_with("```") {
            in_block = false;
        } else if in_block {
            code.push_str(line);
            code.push('\n');
        }
    }
    code
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

fn collect_lagda_md_files(dir: &Path, out: &mut Vec<std::path::PathBuf>) {
    if let Ok(rd) = std::fs::read_dir(dir) {
        for entry in rd.filter_map(|e| e.ok()) {
            let path = entry.path();
            if path.is_dir() {
                collect_lagda_md_files(&path, out);
            } else if path.to_string_lossy().ends_with(".lagda.md") {
                out.push(path);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_agda_data() {
        let src = "module Test where\n\ndata Nat : Set where\n  zero : Nat\n  suc  : Nat → Nat\n";
        let dir = tempfile::tempdir().unwrap();
        let file = dir.path().join("Test.agda");
        std::fs::write(&file, src).unwrap();

        let decls = import_agda_file(&file).unwrap();
        assert!(decls.len() >= 2); // module + data
        let data_decl = decls.iter().find(|d| d.kind == AgdaDeclKind::Data);
        assert!(data_decl.is_some());
        assert!(data_decl.unwrap().name.contains("Nat"));
    }

    #[test]
    fn test_parse_agda_postulate() {
        let src = "postulate\n  trustMe : {A : Set} → A\n";
        let dir = tempfile::tempdir().unwrap();
        let file = dir.path().join("Test.agda");
        std::fs::write(&file, src).unwrap();

        let decls = import_agda_file(&file).unwrap();
        let post = decls.iter().find(|d| d.kind == AgdaDeclKind::Postulate);
        assert!(post.is_some());
        assert!(post.unwrap().is_postulate);
    }

    #[test]
    fn test_parse_idris_data() {
        let src = "module Test\n\ndata Nat = Z | S Nat\n";
        let dir = tempfile::tempdir().unwrap();
        let file = dir.path().join("Test.idr");
        std::fs::write(&file, src).unwrap();

        let decls = import_idris_file(&file).unwrap();
        let data_decl = decls.iter().find(|d| d.kind == IdrisDeclKind::Data);
        assert!(data_decl.is_some());
    }

    #[test]
    fn test_parse_idris_type_sig() {
        let src =
            "module Test\n\nadd : Nat -> Nat -> Nat\nadd Z y = y\nadd (S x) y = S (add x y)\n";
        let dir = tempfile::tempdir().unwrap();
        let file = dir.path().join("Test.idr");
        std::fs::write(&file, src).unwrap();

        let decls = import_idris_file(&file).unwrap();
        let sig = decls.iter().find(|d| d.kind == IdrisDeclKind::TypeSig);
        assert!(sig.is_some());
        assert!(sig.unwrap().name.contains("add"));
    }

    #[test]
    fn test_agda_postulate_trust_level() {
        let d = AgdaDeclaration {
            name: "trust".to_owned(),
            kind: AgdaDeclKind::Postulate,
            type_signature: None,
            source_file: "t.agda".to_owned(),
            line_number: 1,
            module_name: None,
            is_postulate: true,
        };
        assert_eq!(agda_trust_level(&d), TrustLevel::PartiallyAxiomatized);
        assert!(agda_axiom_profile(&d).contains(AxiomProfile::AGDA_CUBICAL));
    }

    #[test]
    fn test_import_stats_total() {
        let stats = TypeTheoryImportStats {
            files_scanned: 10,
            files_failed: 1,
            declarations_found: 50,
            postulates_found: 5,
            data_types_found: 10,
            type_sigs_found: 35,
            total_lines: 1000,
        };
        assert_eq!(stats.total(), 50);
    }
}
