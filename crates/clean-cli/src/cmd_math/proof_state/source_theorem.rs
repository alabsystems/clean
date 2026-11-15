// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Source-backed theorem snapshots for `clean math proof-state snapshot`: the
//! `math-theorem-v2` state handle, the declaration lookup in a parsed source
//! file, and the report rendered when no proof-state server is configured.

use std::fs;
use std::io::Write;
use std::path::{Path, PathBuf};

use clean_parser::{parse_file_with_tactics, Span, SurfaceDecl, SurfaceExpr, SurfaceName};
use serde::Serialize;

use super::super::args::SnapshotFormat;

#[derive(Debug)]
pub(super) struct SourceTheoremHandle {
    pub(super) project: String,
    pub(super) theorem: String,
    pub(super) file: PathBuf,
}

#[derive(Debug, Serialize)]
pub(super) struct SourceTheoremSnapshotReport {
    schema_version: &'static str,
    operation: &'static str,
    state: String,
    pub(super) status: &'static str,
    project: String,
    theorem: String,
    file: String,
    line: usize,
    column: usize,
    format: &'static str,
    pub(super) is_solved: bool,
    pub(super) proof_status: &'static str,
    binder_count: usize,
    pub(super) target_debug: String,
    pub(super) declaration_source: String,
    pub(super) goals: Vec<SourceTheoremGoal>,
    pub(super) feedback: Vec<String>,
}

#[derive(Debug, Serialize)]
pub(super) struct SourceTheoremGoal {
    goal_id: String,
    status: &'static str,
    target_debug: String,
    hypotheses: Vec<String>,
}

pub(super) fn source_theorem_state_id(project: &str, file: &Path, theorem: &str) -> String {
    // Length-prefix the actual names: replacing whitespace or splitting on a
    // colon changes legal quoted identifiers such as `«a b:c»`.
    format!(
        "math-theorem-v2:{}:{}{}:{}{}",
        project.len(),
        project,
        theorem.len(),
        theorem,
        file.display()
    )
}

pub(super) fn parse_source_theorem_state_id(state: &str) -> Option<SourceTheoremHandle> {
    if let Some(rest) = state.strip_prefix("math-theorem-v2:") {
        let (project, rest) = take_length_prefixed_field(rest)?;
        let (theorem, file) = take_length_prefixed_field(rest)?;
        return Some(SourceTheoremHandle {
            project: project.to_owned(),
            theorem: theorem.to_owned(),
            file: PathBuf::from(file),
        });
    }
    // Retain already-issued legacy handles, but never generate their lossy spelling.
    let mut parts = state.splitn(4, ':');
    if parts.next()? != "math-theorem" {
        return None;
    }
    Some(SourceTheoremHandle {
        project: parts.next()?.to_owned(),
        theorem: parts.next()?.to_owned(),
        file: PathBuf::from(parts.next()?),
    })
}

fn take_length_prefixed_field(text: &str) -> Option<(&str, &str)> {
    let (length, rest) = text.split_once(':')?;
    let length = length.parse::<usize>().ok()?;
    Some((rest.get(..length)?, rest.get(length..)?))
}

pub(super) fn source_theorem_snapshot(
    state: &str,
    format: SnapshotFormat,
    handle: SourceTheoremHandle,
) -> Result<SourceTheoremSnapshotReport, String> {
    let source = fs::read_to_string(&handle.file).map_err(|err| {
        format!(
            "source-backed theorem snapshot could not read `{}`: {err}",
            handle.file.display()
        )
    })?;
    let patterns = clean_elab::tactic::builtins::builtin_tactic_patterns();
    let decls = parse_file_with_tactics(&source, &patterns).map_err(|err| {
        format!(
            "source-backed theorem snapshot could not parse `{}`: {err}",
            handle.file.display()
        )
    })?;

    let Some((span, parsed_name, binders, target_debug)) =
        find_source_theorem_decl(&decls, &handle.theorem)
    else {
        return Err(format!(
            "source-backed theorem snapshot could not find theorem `{}` in `{}`",
            handle.theorem,
            handle.file.display()
        ));
    };

    let (line, column) = line_column_for_offset(&source, span.start);
    let declaration_source = source_declaration_slice(&source, span.start).unwrap_or_else(|| {
        source
            .get(span.start..span.end)
            .unwrap_or_default()
            .trim()
            .to_owned()
    });
    let proof_status =
        if declaration_source.contains("sorry") || declaration_source.contains("admit") {
            "closed-with-trust-debt"
        } else {
            "closed-source-theorem"
        };
    let mut feedback = vec![
        "source-backed theorem snapshot: the declaration is already closed in the source file"
            .to_owned(),
        "for live tactic application, use a persistent proof-state server".to_owned(),
    ];
    if proof_status == "closed-with-trust-debt" {
        feedback.push(
            "proof text contains `sorry` or `admit`; trust audit must reject this as proof debt"
                .to_owned(),
        );
    }

    let goal = SourceTheoremGoal {
        goal_id: format!("source:{}", parsed_name),
        status: proof_status,
        target_debug: target_debug.clone(),
        hypotheses: binders,
    };

    Ok(SourceTheoremSnapshotReport {
        schema_version: "clean-cli-source-theorem-snapshot-v1",
        operation: "snapshot",
        state: state.to_owned(),
        status: "source-backed-theorem-snapshot",
        project: handle.project,
        theorem: handle.theorem,
        file: handle.file.display().to_string(),
        line,
        column,
        format: match format {
            SnapshotFormat::Json => "json",
            SnapshotFormat::Llm => "llm",
        },
        is_solved: true,
        proof_status,
        binder_count: goal.hypotheses.len(),
        target_debug,
        declaration_source,
        goals: vec![goal],
        feedback,
    })
}

pub(super) fn find_source_theorem_decl(
    decls: &[SurfaceDecl],
    requested_name: &str,
) -> Option<(Span, String, Vec<String>, String)> {
    let requested = clean_parser::parse_name(requested_name).ok()?;
    if requested.is_relative_constructor() {
        return None;
    }
    let qualified = requested.qualify_under(&SurfaceName::default());
    let forced_root = qualified.name() != requested.name();
    let requested = qualified;
    let mut candidates = Vec::new();
    collect_source_theorem_decls(decls, &SurfaceName::default(), &mut candidates);
    let mut exact = candidates
        .iter()
        .filter(|candidate| candidate.1 == requested);
    let selected = if let Some(first) = exact.next() {
        // A duplicate identity is not a license to select an arbitrary source body.
        if exact.next().is_some() {
            return None;
        }
        first
    } else {
        // Preserve the short-name convenience only for a unique structural
        // final component. A qualified request must never borrow another scope.
        if forced_root {
            return None;
        }
        let requested_component = requested.component_text()?;
        let mut short = candidates.iter().filter(|candidate| {
            matches!(candidate.1.name().inner(), clean_kernel::name::NameInner::Str(_, text)
                if text.as_ref() == requested_component)
        });
        let first = short.next()?;
        if short.next().is_some() {
            return None;
        }
        first
    };
    Some((
        selected.0,
        selected.1.source_spelling()?,
        selected.2.clone(),
        selected.3.clone(),
    ))
}

type SourceTheoremDecl = (Span, SurfaceName, Vec<String>, String);

fn collect_source_theorem_decls(
    decls: &[SurfaceDecl],
    namespace: &SurfaceName,
    found: &mut Vec<SourceTheoremDecl>,
) {
    for decl in decls {
        match decl {
            SurfaceDecl::Namespace { name, decls, .. } => {
                let nested = name.qualify_under(namespace);
                collect_source_theorem_decls(decls, &nested, found);
            }
            SurfaceDecl::Section { decls, .. } | SurfaceDecl::Mutual { decls, .. } => {
                collect_source_theorem_decls(decls, namespace, found);
            }
            SurfaceDecl::Theorem {
                span,
                name,
                binders,
                ty,
                proof,
                ..
            } => {
                let full_name = name.qualify_under(namespace);
                let declaration_span = Span::new(span.start, proof.span().end);
                found.push((
                    declaration_span,
                    full_name,
                    binders.iter().map(|binder| format!("{binder:?}")).collect(),
                    surface_expr_debug(ty),
                ));
            }
            SurfaceDecl::SetOption {
                body: Some(body), ..
            }
            | SurfaceDecl::Open {
                body: Some(body), ..
            }
            | SurfaceDecl::GuardMsgs { cmd: body, .. } => {
                collect_source_theorem_decls(std::slice::from_ref(body.as_ref()), namespace, found);
            }
            _ => {}
        }
    }
}

fn surface_expr_debug(expr: &SurfaceExpr) -> String {
    format!("{expr:?}")
}

fn line_column_for_offset(source: &str, offset: usize) -> (usize, usize) {
    let mut line = 1;
    let mut line_start = 0;
    for (idx, ch) in source.char_indices() {
        if idx >= offset {
            break;
        }
        if ch == '\n' {
            line += 1;
            line_start = idx + 1;
        }
    }
    (line, offset.saturating_sub(line_start) + 1)
}

fn source_declaration_slice(source: &str, start: usize) -> Option<String> {
    if start >= source.len() {
        return None;
    }
    let line_start = source[..start].rfind('\n').map_or(0, |idx| idx + 1);
    let mut offset = line_start;
    let mut end = source.len();
    let mut seen_start_line = false;

    for line in source[line_start..].split_inclusive('\n') {
        if seen_start_line && is_unindented_declaration_boundary(line) {
            end = offset;
            break;
        }
        seen_start_line = true;
        offset += line.len();
    }

    let slice = source.get(line_start..end)?.trim();
    (!slice.is_empty()).then(|| slice.to_owned())
}

fn is_unindented_declaration_boundary(line: &str) -> bool {
    let Some(first) = line.chars().next() else {
        return false;
    };
    if first.is_whitespace() {
        return false;
    }

    let trimmed = line.trim_start();
    const BOUNDARIES: &[&str] = &[
        "@[",
        "/--",
        "/-!",
        "#",
        "abbrev ",
        "axiom ",
        "class ",
        "def ",
        "end ",
        "example ",
        "inductive ",
        "instance ",
        "lemma ",
        "namespace ",
        "noncomputable ",
        "opaque ",
        "private ",
        "protected ",
        "section ",
        "set_option ",
        "structure ",
        "theorem ",
    ];
    BOUNDARIES
        .iter()
        .any(|boundary| trimmed.starts_with(boundary))
}

pub(super) fn render_source_theorem_snapshot(
    out: &mut dyn Write,
    report: &SourceTheoremSnapshotReport,
) -> std::io::Result<()> {
    writeln!(out, "operation: {}", report.operation)?;
    writeln!(out, "status: {}", report.status)?;
    writeln!(out, "theorem: {}", report.theorem)?;
    writeln!(
        out,
        "file: {}:{}:{}",
        report.file, report.line, report.column
    )?;
    writeln!(out, "proof_status: {}", report.proof_status)?;
    writeln!(out, "target: {}", report.target_debug)?;
    for feedback in &report.feedback {
        writeln!(out, "- {feedback}")?;
    }
    Ok(())
}
