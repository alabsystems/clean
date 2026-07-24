// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Reusable theorem-index service model built from factory declaration indexes.

use std::collections::BTreeMap;
use std::fs;
use std::io::{self, Write};
use std::path::{Path, PathBuf};

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

use super::decl_index::{
    self, DeclarationIndex, DeclarationKind, IndexDiagnostic, RecordSource, SourceSpan, TrustRecord,
};
use super::{FactoryOpsError, TheoremIndexArgs};

const THEOREM_INDEX_SCHEMA_VERSION: &str = "clean-theorem-index-v1";

/// Module/import metadata attached to every theorem candidate from a source file.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct TheoremSourceMetadata {
    pub(crate) module: String,
    pub(crate) imports: Vec<String>,
}

/// Searchable theorem candidate derived from a declaration-index record.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct TheoremCandidate {
    pub(crate) schema_version: String,
    pub(crate) name: String,
    pub(crate) kind: DeclarationKind,
    pub(crate) module: String,
    pub(crate) imports: Vec<String>,
    pub(crate) source_path: String,
    pub(crate) span: Option<SourceSpan>,
    pub(crate) source: RecordSource,
    pub(crate) statement_fingerprint: String,
    pub(crate) type_fingerprint: String,
    pub(crate) value_fingerprint: Option<String>,
    pub(crate) candidate_fingerprint: String,
    pub(crate) conclusion_head: Option<String>,
    pub(crate) symbol_refs: Vec<String>,
    pub(crate) trust: TrustRecord,
}

/// Agent-facing theorem index emitted by `clean factory theorem-index`.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct TheoremIndexReport {
    pub(crate) schema_version: String,
    pub(crate) root: String,
    pub(crate) profile: String,
    pub(crate) files_scanned: usize,
    pub(crate) candidates: Vec<TheoremCandidate>,
    pub(crate) diagnostics: Vec<IndexDiagnostic>,
}

impl TheoremIndexReport {
    pub(crate) fn has_errors(&self) -> bool {
        self.diagnostics
            .iter()
            .any(|diagnostic| diagnostic.severity == "error")
    }
}

#[derive(Debug, Serialize)]
struct CandidateFingerprintInput<'a> {
    schema_version: &'a str,
    name: &'a str,
    kind: DeclarationKind,
    module: &'a str,
    imports: &'a [String],
    source_path: &'a str,
    span: &'a Option<SourceSpan>,
    source: RecordSource,
    statement_fingerprint: &'a str,
    type_fingerprint: &'a str,
    value_fingerprint: &'a Option<String>,
    conclusion_head: &'a Option<String>,
    symbol_refs: &'a [String],
}

pub(crate) fn run_theorem_index(args: TheoremIndexArgs) -> Result<(), FactoryOpsError> {
    let report = build_theorem_index(&args.root, &args.profile, &args.paths)?;

    let stdout = io::stdout();
    let mut out = stdout.lock();
    if args.json {
        writeln!(out, "{}", serde_json::to_string_pretty(&report)?)?;
    } else {
        render_human_index(&mut out, &report)?;
    }

    Ok(())
}

/// Build the theorem-index report used by proof-factory agents.
pub(crate) fn build_theorem_index(
    root: &Path,
    profile: &str,
    requested_paths: &[PathBuf],
) -> Result<TheoremIndexReport, FactoryOpsError> {
    let declaration_index = decl_index::build_index(root, profile, requested_paths)?;
    let mut diagnostics = declaration_index.diagnostics.clone();
    let source_texts =
        source_texts_for_index(Path::new(&declaration_index.root), &declaration_index);
    let source_metadata = source_metadata_from_texts(&source_texts.texts);
    diagnostics.extend(source_texts.diagnostics);
    let candidates = theorem_candidates_from_index(&declaration_index, &source_metadata);

    Ok(TheoremIndexReport {
        schema_version: THEOREM_INDEX_SCHEMA_VERSION.to_owned(),
        root: declaration_index.root,
        profile: declaration_index.profile,
        files_scanned: declaration_index.files_scanned,
        candidates,
        diagnostics,
    })
}

/// Convert a declaration index into theorem candidates.
///
/// The function is pure: callers provide per-source metadata collected from
/// whichever file/import service they own. Missing metadata falls back to a
/// path-derived module and an empty import list.
pub(crate) fn theorem_candidates_from_index(
    index: &DeclarationIndex,
    source_metadata: &BTreeMap<String, TheoremSourceMetadata>,
) -> Vec<TheoremCandidate> {
    let mut candidates = index
        .records
        .iter()
        .filter(|record| record.kind.is_theorem_like())
        .map(|record| {
            let metadata = source_metadata
                .get(&record.source_path)
                .cloned()
                .unwrap_or_else(|| TheoremSourceMetadata {
                    module: module_name_from_source_path(&record.source_path),
                    imports: Vec::new(),
                });
            let mut imports = metadata.imports;
            imports.sort();
            imports.dedup();

            let mut symbol_refs = record.symbol_refs.clone();
            symbol_refs.sort();
            symbol_refs.dedup();

            let candidate_fingerprint = candidate_fingerprint(CandidateFingerprintInput {
                schema_version: THEOREM_INDEX_SCHEMA_VERSION,
                name: &record.name,
                kind: record.kind,
                module: &metadata.module,
                imports: &imports,
                source_path: &record.source_path,
                span: &record.span,
                source: record.source,
                statement_fingerprint: &record.statement_fingerprint,
                type_fingerprint: &record.type_fingerprint,
                value_fingerprint: &record.value_fingerprint,
                conclusion_head: &record.conclusion_head,
                symbol_refs: &symbol_refs,
            });

            TheoremCandidate {
                schema_version: THEOREM_INDEX_SCHEMA_VERSION.to_owned(),
                name: record.name.clone(),
                kind: record.kind,
                module: metadata.module,
                imports,
                source_path: record.source_path.clone(),
                span: record.span.clone(),
                source: record.source,
                statement_fingerprint: record.statement_fingerprint.clone(),
                type_fingerprint: record.type_fingerprint.clone(),
                value_fingerprint: record.value_fingerprint.clone(),
                candidate_fingerprint,
                conclusion_head: record.conclusion_head.clone(),
                symbol_refs,
                trust: record.trust.clone(),
            }
        })
        .collect::<Vec<_>>();

    candidates.sort_by(|left, right| {
        left.name
            .cmp(&right.name)
            .then_with(|| left.source_path.cmp(&right.source_path))
            .then_with(|| left.candidate_fingerprint.cmp(&right.candidate_fingerprint))
    });
    candidates
}

/// Build source metadata from in-memory file text, keyed by declaration-index source path.
pub(crate) fn source_metadata_from_texts(
    source_texts: &BTreeMap<String, String>,
) -> BTreeMap<String, TheoremSourceMetadata> {
    source_texts
        .iter()
        .map(|(path, text)| {
            (
                path.clone(),
                TheoremSourceMetadata {
                    module: module_name_from_source_path(path),
                    imports: import_modules(text),
                },
            )
        })
        .collect()
}

#[derive(Debug, Default)]
struct SourceTextSet {
    texts: BTreeMap<String, String>,
    diagnostics: Vec<IndexDiagnostic>,
}

fn source_texts_for_index(root: &Path, index: &DeclarationIndex) -> SourceTextSet {
    let mut set = SourceTextSet::default();
    for source_path in index.records.iter().map(|record| &record.source_path) {
        if set.texts.contains_key(source_path) {
            continue;
        }
        let path = root.join(source_path);
        match fs::read_to_string(&path) {
            Ok(text) => {
                set.texts.insert(source_path.clone(), text);
            }
            Err(source) => set.diagnostics.push(IndexDiagnostic {
                severity: "error".to_owned(),
                path: source_path.clone(),
                message: format!("failed to read source text for theorem index: {source}"),
            }),
        }
    }
    set
}

fn render_human_index(out: &mut impl Write, report: &TheoremIndexReport) -> io::Result<()> {
    writeln!(out, "root: {}", report.root)?;
    writeln!(out, "profile: {}", report.profile)?;
    writeln!(out, "files_scanned: {}", report.files_scanned)?;
    writeln!(out, "theorem_candidates: {}", report.candidates.len())?;
    writeln!(out, "diagnostics: {}", report.diagnostics.len())?;
    for candidate in &report.candidates {
        writeln!(
            out,
            "- {} ({:?}, module {}, source {}, fingerprint {})",
            candidate.name,
            candidate.kind,
            candidate.module,
            candidate.source_path,
            candidate.candidate_fingerprint
        )?;
    }
    Ok(())
}

fn candidate_fingerprint(input: CandidateFingerprintInput<'_>) -> String {
    let bytes = serde_json::to_vec(&input).unwrap_or_else(|_| format!("{input:?}").into_bytes());
    sha256_hex(&bytes)
}

fn import_modules(text: &str) -> Vec<String> {
    let mut imports = Vec::new();
    for line in text.lines() {
        let line = line.split("--").next().unwrap_or("").trim();
        let Some(rest) = line.strip_prefix("import ") else {
            if !line.is_empty() && !line.starts_with("@[") {
                break;
            }
            continue;
        };
        imports.extend(
            rest.split_whitespace()
                .map(|part| {
                    part.trim_matches(|ch: char| {
                        !(ch.is_ascii_alphanumeric() || ch == '_' || ch == '.')
                    })
                })
                .filter(|part| !part.is_empty())
                .map(ToOwned::to_owned),
        );
    }
    imports.sort();
    imports.dedup();
    imports
}

fn module_name_from_source_path(path: &str) -> String {
    path.strip_suffix(".lean")
        .unwrap_or(path)
        .replace(['/', '\\'], ".")
}

fn sha256_hex(bytes: &[u8]) -> String {
    let digest = Sha256::digest(bytes);
    let mut out = String::with_capacity(digest.len() * 2);
    for byte in digest {
        out.push_str(&format!("{byte:02x}"));
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::factory::decl_index::{DeclarationRecord, IndexDiagnostic};
    use clean_kernel::env::{ConstantKind, Reducibility};

    fn record(name: &str, kind: DeclarationKind, source_path: &str) -> DeclarationRecord {
        DeclarationRecord {
            name: name.to_owned(),
            kind,
            source_path: source_path.to_owned(),
            span: Some(SourceSpan {
                start: 8,
                end: 36,
                line: 2,
                column: 1,
            }),
            source: RecordSource::ParsedSurface,
            statement_fingerprint: format!("stmt:{name}"),
            type_fingerprint: format!("type:{name}"),
            value_fingerprint: None,
            conclusion_head: Some("Eq".to_owned()),
            symbol_refs: vec!["Nat".to_owned(), "Eq".to_owned(), "Nat".to_owned()],
            trust: TrustRecord::default(),
            type_expr: None,
            value_expr: None,
            level_params: Vec::new(),
            is_reducible: false,
            reducibility: Reducibility::Regular(0),
            constant_kind: ConstantKind::Theorem,
        }
    }

    #[test]
    fn theorem_candidates_preserve_metadata_and_stable_fingerprints() {
        let index = DeclarationIndex {
            schema_version: "clean-factory-decl-index-v1".to_owned(),
            root: "/repo".to_owned(),
            profile: "test".to_owned(),
            files_scanned: 1,
            records: vec![
                record("Demo.two", DeclarationKind::Definition, "Demo.lean"),
                record("Demo.one", DeclarationKind::Theorem, "Demo.lean"),
                record("Demo.ax", DeclarationKind::Axiom, "Demo.lean"),
            ],
            diagnostics: Vec::<IndexDiagnostic>::new(),
        };
        let source_texts = BTreeMap::from([(
            "Demo.lean".to_owned(),
            "import Init Mathlib.Data.Nat.Basic\n\ntheorem Demo.one : True := True.intro\n"
                .to_owned(),
        )]);
        let metadata = source_metadata_from_texts(&source_texts);

        let first = theorem_candidates_from_index(&index, &metadata);
        let second = theorem_candidates_from_index(&index, &metadata);

        assert_eq!(first, second);
        assert_eq!(
            first
                .iter()
                .map(|candidate| candidate.name.as_str())
                .collect::<Vec<_>>(),
            vec!["Demo.ax", "Demo.one"]
        );
        assert!(first
            .iter()
            .all(|candidate| candidate.module == "Demo" && candidate.source_path == "Demo.lean"));
        assert_eq!(
            first[0].imports,
            vec!["Init".to_owned(), "Mathlib.Data.Nat.Basic".to_owned()]
        );
        assert_eq!(first[0].span.as_ref().map(|span| span.line), Some(2));
        assert_eq!(
            first[0].symbol_refs,
            vec!["Eq".to_owned(), "Nat".to_owned()]
        );
        assert_eq!(first[0].candidate_fingerprint.len(), 64);
        assert_ne!(
            first[0].candidate_fingerprint,
            first[1].candidate_fingerprint
        );
    }

    #[test]
    fn build_theorem_index_emits_agent_json_shape_from_source() {
        let dir = tempfile::tempdir().expect("tempdir");
        let source = dir.path().join("Demo.lean");
        std::fs::write(
            &source,
            "import Init\n\nnamespace Demo\n theorem one : True := True.intro\nend Demo\n",
        )
        .expect("write source");

        let report =
            build_theorem_index(dir.path(), "proof-factory", &[PathBuf::from("Demo.lean")])
                .expect("theorem index");

        assert_eq!(report.schema_version, THEOREM_INDEX_SCHEMA_VERSION);
        assert_eq!(report.profile, "proof-factory");
        assert_eq!(report.files_scanned, 1);
        assert_eq!(report.candidates.len(), 1);

        let candidate = &report.candidates[0];
        assert_eq!(candidate.name, "Demo.one");
        assert_eq!(candidate.kind, DeclarationKind::Theorem);
        assert_eq!(candidate.module, "Demo");
        assert_eq!(candidate.imports, vec!["Init".to_owned()]);
        assert_eq!(candidate.source_path, "Demo.lean");
        assert_eq!(candidate.schema_version, THEOREM_INDEX_SCHEMA_VERSION);
        assert_eq!(candidate.candidate_fingerprint.len(), 64);

        let value = serde_json::to_value(report).expect("json");
        assert_eq!(value["schema_version"], THEOREM_INDEX_SCHEMA_VERSION);
        assert_eq!(value["candidates"][0]["name"], "Demo.one");
        assert_eq!(value["candidates"][0]["imports"][0], "Init");
    }
}
