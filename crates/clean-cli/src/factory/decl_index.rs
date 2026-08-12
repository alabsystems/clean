// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Lean declaration indexing for Rust-owned factory checks.

use std::collections::{BTreeMap, HashSet};
use std::fs;
use std::io::{self, Write};
use std::path::{Path, PathBuf};

use clean_elab::{
    elaborate_decl_and_register_with_context, preprocess_decl_with_context, FileContext,
};
use clean_kernel::env::{ConstantInfo, ConstantKind, DeclarationTrustSummary, Reducibility};
use clean_kernel::{Environment, Expr, ExprKind, Name};
use clean_parser::DeclModifiers;
use clean_parser::{parse_file_with_tactics, Span, SurfaceDecl};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

use super::module_scope;
use super::{DeclIndexArgs, FactoryOpsError};

const INDEX_SCHEMA_VERSION: &str = "clean-factory-decl-index-v1";

/// Declaration kind recorded by the factory declaration index.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub(crate) enum DeclarationKind {
    Definition,
    Theorem,
    Axiom,
    Opaque,
    Inductive,
    Structure,
    Class,
    Instance,
    Unknown,
}

impl DeclarationKind {
    pub(crate) fn is_theorem_like(self) -> bool {
        matches!(self, Self::Theorem | Self::Axiom)
    }
}

/// Source of a declaration record.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub(crate) enum RecordSource {
    Kernel,
    ParsedSurface,
    SourceScan,
}

/// Byte-level source span plus human line/column.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct SourceSpan {
    pub(crate) start: usize,
    pub(crate) end: usize,
    pub(crate) line: usize,
    pub(crate) column: usize,
}

/// Trust debt attached to an indexed declaration.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct TrustRecord {
    pub(crate) warning: Option<String>,
    pub(crate) explicit_sorry: bool,
    pub(crate) synthetic_sorry: bool,
    pub(crate) trusted_arith: usize,
    pub(crate) trusted_ay: usize,
    pub(crate) unsafe_declaration: bool,
    pub(crate) axiom_declaration: bool,
}

impl TrustRecord {
    fn from_summary(
        summary: DeclarationTrustSummary,
        unsafe_declaration: bool,
        axiom_declaration: bool,
    ) -> Self {
        let mut record = Self {
            warning: None,
            explicit_sorry: summary.has_explicit_sorry,
            synthetic_sorry: summary.has_synthetic_sorry,
            trusted_arith: summary.trusted_arith_count,
            trusted_ay: summary.trusted_ay_count,
            unsafe_declaration,
            axiom_declaration,
        };
        record.warning = record.warning_text();
        record
    }

    fn warning_text(&self) -> Option<String> {
        let mut parts = Vec::new();
        if self.synthetic_sorry {
            parts.push("synthetic sorry".to_owned());
        }
        if self.explicit_sorry {
            parts.push("explicit sorry".to_owned());
        }
        if self.trusted_arith > 0 {
            parts.push(format!("{} trustedArith reference(s)", self.trusted_arith));
        }
        if self.trusted_ay > 0 {
            parts.push(format!("{} trustedAy reference(s)", self.trusted_ay));
        }
        if self.unsafe_declaration {
            parts.push("unsafe declaration".to_owned());
        }
        if self.axiom_declaration {
            parts.push("axiom declaration".to_owned());
        }
        if parts.is_empty() {
            None
        } else {
            Some(parts.join(", "))
        }
    }

    pub(crate) fn has_debt(&self) -> bool {
        self.explicit_sorry
            || self.synthetic_sorry
            || self.trusted_arith > 0
            || self.trusted_ay > 0
            || self.unsafe_declaration
            || self.axiom_declaration
    }

    pub(crate) fn is_strictly_worse_than(&self, base: &Self) -> bool {
        (!base.explicit_sorry && self.explicit_sorry)
            || (!base.synthetic_sorry && self.synthetic_sorry)
            || self.trusted_arith > base.trusted_arith
            || self.trusted_ay > base.trusted_ay
            || (!base.unsafe_declaration && self.unsafe_declaration)
            || (!base.axiom_declaration && self.axiom_declaration)
    }

    pub(crate) fn debt_labels(&self) -> Vec<String> {
        let mut labels = Vec::new();
        if self.explicit_sorry {
            labels.push("explicit_sorry".to_owned());
        }
        if self.synthetic_sorry {
            labels.push("synthetic_sorry".to_owned());
        }
        if self.trusted_arith > 0 {
            labels.push(format!("trusted_arith:{}", self.trusted_arith));
        }
        if self.trusted_ay > 0 {
            labels.push(format!("trusted_ay:{}", self.trusted_ay));
        }
        if self.unsafe_declaration {
            labels.push("unsafe".to_owned());
        }
        if self.axiom_declaration {
            labels.push("axiom".to_owned());
        }
        labels
    }
}

/// One declaration indexed from Lean source or kernel elaboration.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct DeclarationRecord {
    pub(crate) name: String,
    pub(crate) kind: DeclarationKind,
    pub(crate) source_path: String,
    pub(crate) span: Option<SourceSpan>,
    pub(crate) source: RecordSource,
    pub(crate) statement_fingerprint: String,
    pub(crate) type_fingerprint: String,
    pub(crate) value_fingerprint: Option<String>,
    pub(crate) conclusion_head: Option<String>,
    pub(crate) symbol_refs: Vec<String>,
    pub(crate) trust: TrustRecord,
    #[serde(skip)]
    pub(crate) type_expr: Option<Expr>,
    #[serde(skip)]
    pub(crate) value_expr: Option<Expr>,
    #[serde(skip)]
    pub(crate) level_params: Vec<Name>,
    #[serde(skip)]
    pub(crate) is_reducible: bool,
    #[serde(skip)]
    pub(crate) reducibility: Reducibility,
    #[serde(skip)]
    pub(crate) constant_kind: ConstantKind,
}

impl DeclarationRecord {
    fn from_constant(
        env: &Environment,
        info: &ConstantInfo,
        source_path: String,
        span: Option<SourceSpan>,
    ) -> Self {
        let kind = kind_from_constant(info.kind);
        let type_fingerprint = expr_fingerprint(&info.type_);
        let value_fingerprint = info.value.as_ref().map(expr_fingerprint);
        let mut symbol_refs = info
            .type_
            .collect_constants()
            .into_iter()
            .map(|name| name.to_string())
            .collect::<Vec<_>>();
        symbol_refs.sort();
        symbol_refs.dedup();
        Self {
            name: info.name.to_string(),
            kind,
            source_path,
            span,
            source: RecordSource::Kernel,
            statement_fingerprint: type_fingerprint.clone(),
            type_fingerprint,
            value_fingerprint,
            conclusion_head: conclusion_head(&info.type_),
            symbol_refs,
            trust: TrustRecord::from_summary(
                info.trust_summary(),
                env.is_unsafe(&info.name),
                kind == DeclarationKind::Axiom,
            ),
            type_expr: Some(info.type_.clone()),
            value_expr: info.value.clone(),
            level_params: info.level_params.clone(),
            is_reducible: info.is_reducible,
            reducibility: info.reducibility,
            constant_kind: info.kind,
        }
    }

    fn source_only(
        name: String,
        kind: DeclarationKind,
        source_path: String,
        span: Option<SourceSpan>,
        statement: &str,
        source: RecordSource,
        trust: TrustRecord,
    ) -> Self {
        let fingerprint = text_fingerprint(&normalize_statement(statement));
        Self {
            name,
            kind,
            source_path,
            span,
            source,
            statement_fingerprint: fingerprint.clone(),
            type_fingerprint: fingerprint,
            value_fingerprint: None,
            conclusion_head: source_conclusion_head(statement),
            symbol_refs: Vec::new(),
            trust,
            type_expr: None,
            value_expr: None,
            level_params: Vec::new(),
            is_reducible: false,
            reducibility: Reducibility::Regular(0),
            constant_kind: constant_kind_from_decl_kind(kind),
        }
    }

    pub(crate) fn to_constant_info(&self) -> Option<ConstantInfo> {
        let type_ = self.type_expr.clone()?;
        Some(ConstantInfo {
            name: Name::from_string(&self.name),
            level_params: self.level_params.clone(),
            type_,
            value: self.value_expr.clone(),
            is_reducible: self.is_reducible,
            reducibility: self.reducibility,
            kind: self.constant_kind,
        })
    }
}

/// Diagnostic emitted while indexing a source tree.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct IndexDiagnostic {
    pub(crate) severity: String,
    pub(crate) path: String,
    pub(crate) message: String,
}

/// Declaration index emitted by `clean factory decl-index`.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct DeclarationIndex {
    pub(crate) schema_version: String,
    pub(crate) root: String,
    pub(crate) profile: String,
    pub(crate) files_scanned: usize,
    pub(crate) records: Vec<DeclarationRecord>,
    pub(crate) diagnostics: Vec<IndexDiagnostic>,
}

impl DeclarationIndex {
    pub(crate) fn empty(root: &Path, profile: &str) -> Self {
        Self {
            schema_version: INDEX_SCHEMA_VERSION.to_owned(),
            root: normalize_root(root).to_string_lossy().into_owned(),
            profile: profile.to_owned(),
            files_scanned: 0,
            records: Vec::new(),
            diagnostics: Vec::new(),
        }
    }

    pub(crate) fn has_errors(&self) -> bool {
        self.diagnostics
            .iter()
            .any(|diagnostic| diagnostic.severity == "error")
    }

    pub(crate) fn by_name(&self) -> BTreeMap<String, Vec<&DeclarationRecord>> {
        let mut by_name: BTreeMap<String, Vec<&DeclarationRecord>> = BTreeMap::new();
        for record in &self.records {
            by_name.entry(record.name.clone()).or_default().push(record);
        }
        by_name
    }
}

pub(crate) fn run_decl_index(args: DeclIndexArgs) -> Result<(), FactoryOpsError> {
    let index = build_index(&args.root, &args.profile, &args.paths)?;

    let stdout = io::stdout();
    let mut out = stdout.lock();
    if args.json {
        writeln!(out, "{}", serde_json::to_string_pretty(&index)?)?;
    } else {
        render_human_index(&mut out, &index)?;
    }

    if index.has_errors() {
        return Err(FactoryOpsError::LeanAnalysis {
            path: args.root,
            message: format!("{} indexing diagnostic(s)", index.diagnostics.len()),
        });
    }
    Ok(())
}

pub(crate) fn build_index(
    root: &Path,
    profile: &str,
    requested_paths: &[PathBuf],
) -> Result<DeclarationIndex, FactoryOpsError> {
    let root = normalize_root(root);
    let files = resolve_index_files(&root, requested_paths)?;
    let mut records = Vec::new();
    let mut diagnostics = Vec::new();

    for file in &files {
        index_file(&root, file, &mut records, &mut diagnostics);
    }

    records.sort_by(|left, right| {
        left.name
            .cmp(&right.name)
            .then_with(|| left.source_path.cmp(&right.source_path))
            .then_with(|| left.statement_fingerprint.cmp(&right.statement_fingerprint))
    });
    records.dedup();

    Ok(DeclarationIndex {
        schema_version: INDEX_SCHEMA_VERSION.to_owned(),
        root: root.to_string_lossy().into_owned(),
        profile: profile.to_owned(),
        files_scanned: files.len(),
        records,
        diagnostics,
    })
}

pub(crate) fn build_source_index(
    root: &Path,
    profile: &str,
) -> Result<DeclarationIndex, FactoryOpsError> {
    let root = normalize_root(root);
    let files = resolve_index_files(&root, &[])?;
    let mut records = Vec::new();
    let mut diagnostics = Vec::new();

    for file in &files {
        match fs::read_to_string(file) {
            Ok(text) => scan_source_file(&root, file, &text, &mut records),
            Err(source) => diagnostics.push(IndexDiagnostic {
                severity: "error".to_owned(),
                path: relative_path(&root, file),
                message: format!("failed to read file: {source}"),
            }),
        }
    }

    records.sort_by(|left, right| {
        left.name
            .cmp(&right.name)
            .then_with(|| left.source_path.cmp(&right.source_path))
    });

    Ok(DeclarationIndex {
        schema_version: INDEX_SCHEMA_VERSION.to_owned(),
        root: root.to_string_lossy().into_owned(),
        profile: profile.to_owned(),
        files_scanned: files.len(),
        records,
        diagnostics,
    })
}

fn index_file(
    root: &Path,
    file: &Path,
    records: &mut Vec<DeclarationRecord>,
    diagnostics: &mut Vec<IndexDiagnostic>,
) {
    let source_path = relative_path(root, file);
    let text = match fs::read_to_string(file) {
        Ok(text) => text,
        Err(source) => {
            diagnostics.push(IndexDiagnostic {
                severity: "error".to_owned(),
                path: source_path,
                message: format!("failed to read file: {source}"),
            });
            return;
        }
    };

    let patterns = clean_elab::tactic::builtins::builtin_tactic_patterns();
    let decls = match parse_file_with_tactics(&text, &patterns) {
        Ok(decls) => decls,
        Err(error) => {
            diagnostics.push(IndexDiagnostic {
                severity: "error".to_owned(),
                path: source_path.clone(),
                message: format!("parse failed: {error}"),
            });
            scan_source_file(root, file, &text, records);
            return;
        }
    };

    let surface_records = surface_records_for_file(root, file, &text, &decls);
    match kernel_records_for_file(root, file, &text, &decls) {
        Ok(mut outcome) if !outcome.records.is_empty() => {
            if let Some(message) = outcome.diagnostic {
                diagnostics.push(IndexDiagnostic {
                    severity: "error".to_owned(),
                    path: source_path,
                    message,
                });
                extend_missing_surface_records(records, surface_records, &outcome.records);
            }
            records.append(&mut outcome.records);
        }
        Ok(outcome) => {
            if let Some(message) = outcome.diagnostic {
                diagnostics.push(IndexDiagnostic {
                    severity: "error".to_owned(),
                    path: source_path,
                    message,
                });
            }
            records.extend(surface_records);
        }
        Err(message) => {
            diagnostics.push(IndexDiagnostic {
                severity: "error".to_owned(),
                path: source_path,
                message,
            });
            records.extend(surface_records);
        }
    }
}

struct KernelRecordsForFile {
    records: Vec<DeclarationRecord>,
    diagnostic: Option<String>,
}

fn kernel_records_for_file(
    root: &Path,
    file: &Path,
    text: &str,
    decls: &[SurfaceDecl],
) -> Result<KernelRecordsForFile, String> {
    let mut env = Environment::with_prelude();
    env.init_pprod()
        .map_err(|error| format!("prelude support initialization failed: {error}"))?;
    env.init_exists()
        .map_err(|error| format!("prelude support initialization failed: {error}"))?;
    let mut file_ctx = FileContext::new();
    // Declaration/theorem indexing only needs the file's own declarations, not
    // the recursively loaded external `.olean` module graph. Keep imports on the
    // lightweight Clean-native path; import decls are still elaborated below for
    // local context side effects, then excluded from this file's record set.
    file_ctx.disable_external_import_search();
    let source_path = relative_path(root, file);
    let mut records = Vec::new();

    for decl in decls {
        // `import` directives populate the environment so later declarations in
        // this file can resolve symbols from imported modules, but the constants
        // they bring in belong to the imported module -- they are NOT
        // declarations of this file. Elaborate them for that side effect only
        // (tolerating failures such as an unavailable `.olean`) and never
        // attribute the imported constants to this source file. Without this,
        // indexing a file that `import`s a large module reports the entire
        // imported environment as the file's own declarations.
        if matches!(decl, SurfaceDecl::Import { .. }) {
            let processed = preprocess_decl_with_context(decl, &mut file_ctx);
            let _ = elaborate_decl_and_register_with_context(&mut env, &processed, &mut file_ctx);
            continue;
        }
        let before = env
            .constants()
            .map(|info| info.name.to_string())
            .collect::<HashSet<_>>();
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        if let Err(error) =
            elaborate_decl_and_register_with_context(&mut env, &processed, &mut file_ctx)
        {
            let mut added = records_added_since(&env, &before, &source_path, text, decl);
            records.append(&mut added);
            return Ok(KernelRecordsForFile {
                records,
                diagnostic: Some(format!("elaboration failed: {error}")),
            });
        }
        let mut added = env
            .constants()
            .filter(|info| !before.contains(&info.name.to_string()))
            .map(|info| {
                DeclarationRecord::from_constant(
                    &env,
                    info,
                    source_path.clone(),
                    span_for_surface_decl(text, decl),
                )
            })
            .collect::<Vec<_>>();
        added.sort_by(|left, right| left.name.cmp(&right.name));
        records.extend(added);
    }

    Ok(KernelRecordsForFile {
        records,
        diagnostic: None,
    })
}

fn records_added_since(
    env: &Environment,
    before: &HashSet<String>,
    source_path: &str,
    text: &str,
    decl: &SurfaceDecl,
) -> Vec<DeclarationRecord> {
    let mut records = env
        .constants()
        .filter(|info| !before.contains(&info.name.to_string()))
        .map(|info| {
            DeclarationRecord::from_constant(
                env,
                info,
                source_path.to_owned(),
                span_for_surface_decl(text, decl),
            )
        })
        .collect::<Vec<_>>();
    records.sort_by(|left, right| left.name.cmp(&right.name));
    records
}

fn extend_missing_surface_records(
    records: &mut Vec<DeclarationRecord>,
    surface_records: Vec<DeclarationRecord>,
    kernel_records: &[DeclarationRecord],
) {
    let kernel_names = kernel_records
        .iter()
        .map(|record| record.name.as_str())
        .collect::<HashSet<_>>();
    records.extend(
        surface_records
            .into_iter()
            .filter(|record| !kernel_names.contains(record.name.as_str())),
    );
}

fn surface_records_for_file(
    root: &Path,
    file: &Path,
    text: &str,
    decls: &[SurfaceDecl],
) -> Vec<DeclarationRecord> {
    let mut records = Vec::new();
    let source_path = relative_path(root, file);
    let mut namespace = Vec::new();
    for decl in decls {
        push_surface_records(decl, text, &source_path, &mut namespace, &mut records);
    }
    records
}

fn push_surface_records(
    decl: &SurfaceDecl,
    text: &str,
    source_path: &str,
    namespace: &mut Vec<String>,
    records: &mut Vec<DeclarationRecord>,
) {
    match decl {
        SurfaceDecl::Def {
            name,
            span,
            modifiers,
            ..
        } => push_surface_record(
            name,
            DeclarationKind::Definition,
            *modifiers,
            *span,
            text,
            source_path,
            namespace,
            records,
        ),
        SurfaceDecl::Theorem {
            name,
            span,
            modifiers,
            ..
        } => push_surface_record(
            name,
            DeclarationKind::Theorem,
            *modifiers,
            *span,
            text,
            source_path,
            namespace,
            records,
        ),
        SurfaceDecl::Axiom {
            name,
            span,
            modifiers,
            ..
        } => push_surface_record(
            name,
            DeclarationKind::Axiom,
            *modifiers,
            *span,
            text,
            source_path,
            namespace,
            records,
        ),
        SurfaceDecl::Opaque {
            name,
            span,
            modifiers,
            ..
        } => push_surface_record(
            name,
            DeclarationKind::Opaque,
            *modifiers,
            *span,
            text,
            source_path,
            namespace,
            records,
        ),
        SurfaceDecl::Inductive {
            name,
            span,
            modifiers,
            ..
        }
        | SurfaceDecl::Coinductive {
            name,
            span,
            modifiers,
            ..
        } => push_surface_record(
            name,
            DeclarationKind::Inductive,
            *modifiers,
            *span,
            text,
            source_path,
            namespace,
            records,
        ),
        SurfaceDecl::Structure {
            name,
            span,
            modifiers,
            ..
        } => push_surface_record(
            name,
            DeclarationKind::Structure,
            *modifiers,
            *span,
            text,
            source_path,
            namespace,
            records,
        ),
        SurfaceDecl::Class {
            name,
            span,
            modifiers,
            ..
        } => push_surface_record(
            name,
            DeclarationKind::Class,
            *modifiers,
            *span,
            text,
            source_path,
            namespace,
            records,
        ),
        SurfaceDecl::Instance {
            name: Some(name),
            span,
            modifiers,
            ..
        } => push_surface_record(
            name,
            DeclarationKind::Instance,
            *modifiers,
            *span,
            text,
            source_path,
            namespace,
            records,
        ),
        SurfaceDecl::Namespace { name, decls, .. } => {
            namespace.push(name.clone());
            for inner in decls {
                push_surface_records(inner, text, source_path, namespace, records);
            }
            namespace.pop();
        }
        SurfaceDecl::Section { decls, .. } | SurfaceDecl::Mutual { decls, .. } => {
            for inner in decls {
                push_surface_records(inner, text, source_path, namespace, records);
            }
        }
        SurfaceDecl::Open {
            body: Some(body), ..
        }
        | SurfaceDecl::SetOption {
            body: Some(body), ..
        } => push_surface_records(body, text, source_path, namespace, records),
        _ => {}
    }
}

fn push_surface_record(
    name: &str,
    kind: DeclarationKind,
    modifiers: DeclModifiers,
    span: Span,
    text: &str,
    source_path: &str,
    namespace: &[String],
    records: &mut Vec<DeclarationRecord>,
) {
    let full_name = qualify_name(namespace, name);
    let snippet = text.get(span.start..span.end).unwrap_or_default();
    let statement = normalize_decl_statement(snippet, kind, name);
    records.push(DeclarationRecord::source_only(
        full_name,
        kind,
        source_path.to_owned(),
        Some(source_span(text, span)),
        &statement,
        RecordSource::ParsedSurface,
        trust_for_surface_text(kind, modifiers.is_unsafe, snippet),
    ));
}

fn scan_source_file(root: &Path, file: &Path, text: &str, records: &mut Vec<DeclarationRecord>) {
    let source_path = relative_path(root, file);
    let mut namespace = Vec::new();
    let mut byte_offset = 0usize;
    let lines = text.lines().collect::<Vec<_>>();

    for (line_index, line) in lines.iter().enumerate() {
        let stripped = strip_line_comment(line).trim().to_owned();
        if stripped.is_empty() || stripped.starts_with("@[") {
            byte_offset += line.len() + 1;
            continue;
        }

        if let Some(name) = stripped.strip_prefix("namespace ").map(str::trim) {
            if !name.is_empty() {
                namespace.push(name.to_owned());
            }
        } else if stripped == "end" || stripped.starts_with("end ") {
            namespace.pop();
        } else if let Some(header) = parse_decl_header(&stripped) {
            let statement = collect_source_statement(&lines, line_index, header.kind, header.name);
            let decl_text = collect_source_decl_text(&lines, line_index);
            let line_prefix = &line[..line.len().saturating_sub(line.trim_start().len())];
            let span = SourceSpan {
                start: byte_offset + header.keyword_start + line_prefix.len(),
                end: byte_offset + line.len(),
                line: line_index + 1,
                column: header.keyword_start + line_prefix.len() + 1,
            };
            records.push(DeclarationRecord::source_only(
                qualify_name(&namespace, header.name),
                header.kind,
                source_path.clone(),
                Some(span),
                &statement,
                RecordSource::SourceScan,
                trust_for_surface_text(header.kind, header.unsafe_declaration, &decl_text),
            ));
        }

        byte_offset += line.len() + 1;
    }
}

#[derive(Debug, Clone, Copy)]
struct ParsedHeader<'a> {
    kind: DeclarationKind,
    name: &'a str,
    keyword_start: usize,
    unsafe_declaration: bool,
}

fn parse_decl_header(line: &str) -> Option<ParsedHeader<'_>> {
    let mut offset = 0usize;
    let mut rest = line.trim_start();
    offset += line.len() - rest.len();
    let mut unsafe_declaration = false;

    loop {
        let next = if let Some(next) = rest.strip_prefix("unsafe ") {
            unsafe_declaration = true;
            Some(next)
        } else {
            rest.strip_prefix("private ")
                .or_else(|| rest.strip_prefix("protected "))
                .or_else(|| rest.strip_prefix("noncomputable "))
                .or_else(|| rest.strip_prefix("partial "))
        };
        match next {
            Some(next) => {
                offset += rest.len() - next.len();
                rest = next.trim_start();
                offset += next.len() - rest.len();
            }
            None => break,
        }
    }

    for (keyword, kind) in [
        ("theorem", DeclarationKind::Theorem),
        ("lemma", DeclarationKind::Theorem),
        ("axiom", DeclarationKind::Axiom),
        ("def", DeclarationKind::Definition),
        ("opaque", DeclarationKind::Opaque),
        ("inductive", DeclarationKind::Inductive),
        ("coinductive", DeclarationKind::Inductive),
        ("structure", DeclarationKind::Structure),
        ("class", DeclarationKind::Class),
        ("instance", DeclarationKind::Instance),
    ] {
        if let Some(after_keyword) = rest.strip_prefix(keyword) {
            if !after_keyword
                .chars()
                .next()
                .is_some_and(char::is_whitespace)
            {
                continue;
            }
            let name_rest = after_keyword.trim_start();
            let name = take_decl_name(name_rest);
            if name.is_empty() {
                return None;
            }
            return Some(ParsedHeader {
                kind,
                name,
                keyword_start: offset,
                unsafe_declaration,
            });
        }
    }
    None
}

fn trust_for_surface_text(
    kind: DeclarationKind,
    unsafe_declaration: bool,
    declaration_text: &str,
) -> TrustRecord {
    let clean_text = declaration_text
        .lines()
        .map(strip_line_comment)
        .collect::<Vec<_>>()
        .join(" ");
    TrustRecord::from_summary(
        DeclarationTrustSummary {
            has_explicit_sorry: contains_token(&clean_text, "sorry"),
            has_synthetic_sorry: false,
            trusted_arith_count: count_token(&clean_text, "trustedArith"),
            trusted_ay_count: count_token(&clean_text, "trustedAy"),
        },
        unsafe_declaration,
        kind == DeclarationKind::Axiom,
    )
}

fn contains_token(text: &str, needle: &str) -> bool {
    count_token(text, needle) > 0
}

fn count_token(text: &str, needle: &str) -> usize {
    text.match_indices(needle)
        .filter(|(idx, _)| {
            let before = text[..*idx].chars().next_back();
            let after = text[*idx + needle.len()..].chars().next();
            !before.is_some_and(is_identifier_char) && !after.is_some_and(is_identifier_char)
        })
        .count()
}

fn is_identifier_char(ch: char) -> bool {
    ch.is_ascii_alphanumeric() || ch == '_' || ch == '\''
}

fn take_decl_name(text: &str) -> &str {
    let end = text
        .char_indices()
        .find_map(|(idx, ch)| {
            if ch.is_whitespace() || matches!(ch, ':' | '(' | '{' | '[' | '|' | '=') {
                Some(idx)
            } else {
                None
            }
        })
        .unwrap_or(text.len());
    &text[..end]
}

fn collect_source_statement(
    lines: &[&str],
    start: usize,
    kind: DeclarationKind,
    name: &str,
) -> String {
    let mut statement = String::new();
    for (idx, line) in lines.iter().enumerate().skip(start).take(32) {
        let mut text = strip_line_comment(line);
        if let Some(proof_start) = text.find(":=") {
            text = &text[..proof_start];
            statement.push(' ');
            statement.push_str(text);
            break;
        }
        if idx > start && parse_decl_header(text.trim()).is_some() {
            break;
        }
        statement.push(' ');
        statement.push_str(text);
    }
    normalize_decl_statement(&statement, kind, name)
}

fn collect_source_decl_text(lines: &[&str], start: usize) -> String {
    let mut declaration = String::new();
    for (idx, line) in lines.iter().enumerate().skip(start).take(128) {
        let text = strip_line_comment(line);
        if idx > start && parse_decl_header(text.trim()).is_some() {
            break;
        }
        declaration.push(' ');
        declaration.push_str(text);
    }
    declaration
}

fn normalize_decl_statement(snippet: &str, kind: DeclarationKind, name: &str) -> String {
    let without_comments = snippet
        .lines()
        .map(strip_line_comment)
        .collect::<Vec<_>>()
        .join(" ");
    let before_proof = without_comments
        .split(":=")
        .next()
        .unwrap_or(without_comments.as_str());
    let marker = match kind {
        DeclarationKind::Theorem => ["theorem ", "lemma "].as_slice(),
        DeclarationKind::Axiom => ["axiom "].as_slice(),
        DeclarationKind::Definition => ["def "].as_slice(),
        DeclarationKind::Opaque => ["opaque "].as_slice(),
        DeclarationKind::Inductive => ["inductive ", "coinductive "].as_slice(),
        DeclarationKind::Structure => ["structure "].as_slice(),
        DeclarationKind::Class => ["class "].as_slice(),
        DeclarationKind::Instance => ["instance "].as_slice(),
        _ => [].as_slice(),
    };
    let mut body = before_proof;
    for keyword in marker {
        if let Some(pos) = before_proof.find(keyword) {
            body = &before_proof[pos + keyword.len()..];
            break;
        }
    }
    let body = body.strip_prefix(name).unwrap_or(body);
    normalize_statement(body)
}

fn normalize_statement(statement: &str) -> String {
    statement.split_whitespace().collect::<Vec<_>>().join(" ")
}

fn source_conclusion_head(statement: &str) -> Option<String> {
    let normalized = normalize_statement(statement);
    let after_colon = normalized.rsplit_once(':').map(|(_, rhs)| rhs.trim())?;
    after_colon
        .split_whitespace()
        .next()
        .map(|token| token.trim_matches(|ch: char| !ch.is_alphanumeric() && ch != '_' && ch != '.'))
        .filter(|token| !token.is_empty())
        .map(ToOwned::to_owned)
}

fn strip_line_comment(line: &str) -> &str {
    line.split("--").next().unwrap_or(line)
}

fn qualify_name(namespace: &[String], name: &str) -> String {
    if namespace.is_empty() || name.contains('.') {
        name.to_owned()
    } else {
        format!("{}.{}", namespace.join("."), name)
    }
}

fn span_for_surface_decl(text: &str, decl: &SurfaceDecl) -> Option<SourceSpan> {
    surface_decl_span(decl).map(|span| source_span(text, span))
}

fn surface_decl_span(decl: &SurfaceDecl) -> Option<Span> {
    match decl {
        SurfaceDecl::Def { span, .. }
        | SurfaceDecl::Theorem { span, .. }
        | SurfaceDecl::Axiom { span, .. }
        | SurfaceDecl::Opaque { span, .. }
        | SurfaceDecl::Inductive { span, .. }
        | SurfaceDecl::Coinductive { span, .. }
        | SurfaceDecl::Codata { span, .. }
        | SurfaceDecl::Codef { span, .. }
        | SurfaceDecl::Structure { span, .. }
        | SurfaceDecl::Class { span, .. }
        | SurfaceDecl::Instance { span, .. }
        | SurfaceDecl::Example { span, .. }
        | SurfaceDecl::Import { span, .. }
        | SurfaceDecl::Namespace { span, .. }
        | SurfaceDecl::Section { span, .. }
        | SurfaceDecl::UniverseDecl { span, .. }
        | SurfaceDecl::Variable { span, .. }
        | SurfaceDecl::Open { span, .. }
        | SurfaceDecl::Export { span, .. }
        | SurfaceDecl::DerivingInstance { span, .. }
        | SurfaceDecl::Check { span, .. }
        | SurfaceDecl::Eval { span, .. }
        | SurfaceDecl::Print { span, .. }
        | SurfaceDecl::Mutual { span, .. }
        | SurfaceDecl::Syntax { span, .. }
        | SurfaceDecl::DeclareSyntaxCat { span, .. }
        | SurfaceDecl::Macro { span, .. }
        | SurfaceDecl::MacroRules { span, .. }
        | SurfaceDecl::Notation { span, .. }
        | SurfaceDecl::Elab { span, .. }
        | SurfaceDecl::RawDecl { span, .. }
        | SurfaceDecl::Attribute { span, .. }
        | SurfaceDecl::SetOption { span, .. }
        | SurfaceDecl::DeclareAesopRuleSets { span, .. }
        | SurfaceDecl::LibraryNote { span, .. } => Some(*span),
    }
}

fn source_span(text: &str, span: Span) -> SourceSpan {
    let (line, column) = line_column_for_byte(text, span.start);
    SourceSpan {
        start: span.start,
        end: span.end,
        line,
        column,
    }
}

fn line_column_for_byte(text: &str, byte: usize) -> (usize, usize) {
    let mut line = 1usize;
    let mut column = 1usize;
    for (idx, ch) in text.char_indices() {
        if idx >= byte {
            break;
        }
        if ch == '\n' {
            line += 1;
            column = 1;
        } else {
            column += 1;
        }
    }
    (line, column)
}

fn conclusion_head(expr: &Expr) -> Option<String> {
    let mut current = expr.strip_mdata();
    while let ExprKind::Pi(_, _, body) = current.kind() {
        current = body.strip_mdata();
    }
    loop {
        match current.kind() {
            ExprKind::App(function, _) => current = function.strip_mdata(),
            ExprKind::Const(name, _) => return Some(name.to_string()),
            _ => return None,
        }
    }
}

fn expr_fingerprint(expr: &Expr) -> String {
    let bytes = serde_json::to_vec(expr).unwrap_or_else(|_| format!("{expr:?}").into_bytes());
    sha256_hex(&bytes)
}

fn text_fingerprint(text: &str) -> String {
    sha256_hex(text.as_bytes())
}

fn sha256_hex(bytes: &[u8]) -> String {
    let digest = Sha256::digest(bytes);
    let mut out = String::with_capacity(digest.len() * 2);
    for byte in digest {
        out.push_str(&format!("{byte:02x}"));
    }
    out
}

fn kind_from_constant(kind: ConstantKind) -> DeclarationKind {
    match kind {
        ConstantKind::Definition => DeclarationKind::Definition,
        ConstantKind::Theorem => DeclarationKind::Theorem,
        ConstantKind::Opaque => DeclarationKind::Opaque,
        ConstantKind::Axiom => DeclarationKind::Axiom,
    }
}

fn constant_kind_from_decl_kind(kind: DeclarationKind) -> ConstantKind {
    match kind {
        DeclarationKind::Theorem => ConstantKind::Theorem,
        DeclarationKind::Axiom => ConstantKind::Axiom,
        DeclarationKind::Opaque => ConstantKind::Opaque,
        _ => ConstantKind::Definition,
    }
}

fn resolve_index_files(
    root: &Path,
    requested_paths: &[PathBuf],
) -> Result<Vec<PathBuf>, FactoryOpsError> {
    let mut files = if requested_paths.is_empty() {
        module_scope::active_lean_files(root)?
    } else {
        requested_paths
            .iter()
            .map(|path| {
                if path.is_absolute() {
                    path.to_owned()
                } else {
                    root.join(path)
                }
            })
            .filter(|path| path.extension().is_some_and(|ext| ext == "lean") && path.is_file())
            .collect::<Vec<_>>()
    };
    files.sort();
    files.dedup();
    Ok(files)
}

fn normalize_root(root: &Path) -> PathBuf {
    let path = if root.is_absolute() {
        root.to_owned()
    } else {
        std::env::current_dir()
            .unwrap_or_else(|_| PathBuf::from("."))
            .join(root)
    };
    fs::canonicalize(&path).unwrap_or(path)
}

pub(crate) fn relative_path(root: &Path, path: &Path) -> String {
    path.strip_prefix(root)
        .unwrap_or(path)
        .to_string_lossy()
        .replace('\\', "/")
}

fn render_human_index(out: &mut impl Write, index: &DeclarationIndex) -> io::Result<()> {
    writeln!(out, "schema: {}", index.schema_version)?;
    writeln!(out, "root: {}", index.root)?;
    writeln!(out, "profile: {}", index.profile)?;
    writeln!(out, "files_scanned: {}", index.files_scanned)?;
    writeln!(out, "declarations: {}", index.records.len())?;
    let theorem_count = index
        .records
        .iter()
        .filter(|record| record.kind.is_theorem_like())
        .count();
    writeln!(out, "theorem_like: {theorem_count}")?;
    if !index.diagnostics.is_empty() {
        writeln!(out, "diagnostics:")?;
        for diagnostic in &index.diagnostics {
            writeln!(
                out,
                "  {} {}: {}",
                diagnostic.severity, diagnostic.path, diagnostic.message
            )?;
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn duplicate_theorem_source_fingerprint_ignores_theorem_name() {
        let left = normalize_decl_statement(
            "theorem first : True := True.intro",
            DeclarationKind::Theorem,
            "first",
        );
        let right = normalize_decl_statement(
            "theorem second : True := True.intro",
            DeclarationKind::Theorem,
            "second",
        );

        assert_eq!(left, right);
        assert_eq!(text_fingerprint(&left), text_fingerprint(&right));
    }

    #[test]
    fn source_scanner_qualifies_namespaces() {
        let dir = tempfile::tempdir().expect("tempdir");
        let file = dir.path().join("A.lean");
        let text = "namespace Foo\n theorem bar : True := True.intro\nend Foo\n";
        fs::write(&file, text).expect("write");
        let mut records = Vec::new();

        scan_source_file(dir.path(), &file, text, &mut records);

        assert_eq!(records.len(), 1);
        assert_eq!(records[0].name, "Foo.bar");
        assert_eq!(records[0].kind, DeclarationKind::Theorem);
    }

    #[test]
    fn source_scanner_records_trust_debt_tokens() {
        let dir = tempfile::tempdir().expect("tempdir");
        let file = dir.path().join("A.lean");
        let text = "unsafe def danger : Nat := trustedArith\naxiom risky : False\ntheorem unfinished : True := by\n  sorry\n";
        fs::write(&file, text).expect("write");
        let mut records = Vec::new();

        scan_source_file(dir.path(), &file, text, &mut records);

        let by_name = records
            .iter()
            .map(|record| (record.name.as_str(), &record.trust))
            .collect::<BTreeMap<_, _>>();
        assert!(by_name["danger"].unsafe_declaration);
        assert_eq!(by_name["danger"].trusted_arith, 1);
        assert!(by_name["risky"].axiom_declaration);
        assert!(by_name["unfinished"].explicit_sorry);
    }

    #[test]
    fn kernel_index_does_not_attribute_imports_to_source_file() {
        let dir = tempfile::tempdir().expect("tempdir");
        let file = dir.path().join("A.lean");
        let text = "import Init\n\ndef own : Nat := 1\n";
        fs::write(&file, text).expect("write");
        let patterns = clean_elab::tactic::builtins::builtin_tactic_patterns();
        let decls = parse_file_with_tactics(text, &patterns).expect("parse");

        let outcome = kernel_records_for_file(dir.path(), &file, text, &decls).expect("kernel");
        assert_eq!(outcome.diagnostic, None);
        let names = outcome
            .records
            .iter()
            .map(|record| record.name.as_str())
            .collect::<Vec<_>>();

        assert_eq!(
            names,
            vec!["own"],
            "imports should populate elaboration context without being attributed to A.lean"
        );
    }

    #[test]
    fn conclusion_head_reads_pi_result_head() {
        let ty = Expr::pi(
            clean_kernel::BinderInfo::Default,
            Expr::type_(),
            Expr::const_(Name::from_string("True"), vec![]),
        );

        assert_eq!(conclusion_head(&ty), Some("True".to_owned()));
    }
}
