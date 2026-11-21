// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Naming and locating a surface declaration for a verdict, a report row or a
//! diagnostic. These were `clean check`'s private helpers; every frontend that
//! names a declaration in a verdict now names it the same way.

use crate::agent_diagnostics::AgentSourceSpan;
use crate::RegistrationWarningKind;
use clean_parser::{Span, SurfaceDecl, SurfaceName};

/// Human-facing spelling only; never use this label as a declaration/import key.
#[must_use]
pub fn surface_name_label(name: &SurfaceName) -> String {
    name.source_spelling()
        .unwrap_or_else(|| format!("{:?}", name.name()))
}

/// The written name of a declaration, looking through `open … in` /
/// `set_option … in` to the declaration they wrap. `None` for anonymous forms
/// (`example`, `import`, `open`, …).
#[must_use]
pub fn surface_decl_name(decl: &SurfaceDecl) -> Option<String> {
    match decl {
        SurfaceDecl::Def { name, .. }
        | SurfaceDecl::Theorem { name, .. }
        | SurfaceDecl::Axiom { name, .. }
        | SurfaceDecl::Opaque { name, .. }
        | SurfaceDecl::Inductive { name, .. }
        | SurfaceDecl::Coinductive { name, .. }
        | SurfaceDecl::Structure { name, .. }
        | SurfaceDecl::Class { name, .. }
        | SurfaceDecl::Namespace { name, .. } => Some(surface_name_label(name)),
        SurfaceDecl::Alias { names, .. } => names.first().map(|(name, _)| surface_name_label(name)),
        SurfaceDecl::Instance { name, .. } => name.as_ref().map(surface_name_label),
        SurfaceDecl::Section { name, .. } => name.as_ref().map(surface_name_label),
        SurfaceDecl::Print { name, .. }
        | SurfaceDecl::PrintAxioms { name, .. }
        | SurfaceDecl::PrintEquations { name, .. } => Some(surface_name_label(name)),
        SurfaceDecl::DeclareSyntaxCat { name, .. } => Some(surface_name_label(name)),
        SurfaceDecl::Syntax { name, .. } | SurfaceDecl::MacroRules { name, .. } => {
            name.as_ref().map(surface_name_label)
        }
        SurfaceDecl::SetOption {
            body: Some(body), ..
        }
        | SurfaceDecl::Open {
            body: Some(body), ..
        } => surface_decl_name(body),
        SurfaceDecl::GuardMsgs { cmd, .. } => surface_decl_name(cmd),
        _ => None,
    }
}

/// The source span of any surface declaration.
#[must_use]
pub fn surface_decl_span(decl: &SurfaceDecl) -> Option<Span> {
    match decl {
        SurfaceDecl::Def { span, .. }
        | SurfaceDecl::Alias { span, .. }
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
        | SurfaceDecl::IncludeVars { span, .. }
        | SurfaceDecl::OmitVars { span, .. }
        | SurfaceDecl::Open { span, .. }
        | SurfaceDecl::Export { span, .. }
        | SurfaceDecl::DerivingInstance { span, .. }
        | SurfaceDecl::Check { span, .. }
        | SurfaceDecl::Eval { span, .. }
        | SurfaceDecl::Reduce { span, .. }
        | SurfaceDecl::Print { span, .. }
        | SurfaceDecl::PrintAxioms { span, .. }
        | SurfaceDecl::PrintEquations { span, .. }
        | SurfaceDecl::Guard { span, .. }
        | SurfaceDecl::GuardMsgs { span, .. }
        | SurfaceDecl::Mutual { span, .. }
        | SurfaceDecl::Syntax { span, .. }
        | SurfaceDecl::DeclareSyntaxCat { span, .. }
        | SurfaceDecl::Macro { span, .. }
        | SurfaceDecl::MacroRules { span, .. }
        | SurfaceDecl::Notation { span, .. }
        | SurfaceDecl::Elab { span, .. }
        | SurfaceDecl::Prelude { span }
        | SurfaceDecl::RawDecl { span, .. }
        | SurfaceDecl::Attribute { span, .. }
        | SurfaceDecl::SetOption { span, .. }
        | SurfaceDecl::DeclareAesopRuleSets { span, .. }
        | SurfaceDecl::LibraryNote { span, .. } => Some(*span),
    }
}

/// `span` located in `source` (1-based line and column), or `None` when the
/// span does not lie inside `source`.
#[must_use]
pub fn source_span(source: &str, span: Span) -> Option<AgentSourceSpan> {
    if span.end < span.start || span.start > source.len() {
        return None;
    }
    let (line, column) = line_column_for_offset(source, span.start);
    Some(AgentSourceSpan {
        start: span.start,
        end: span.end.min(source.len()),
        line,
        column,
    })
}

/// The 1-based (line, column) of byte `offset` in `source`, counting columns
/// in characters.
#[must_use]
pub fn line_column_for_offset(source: &str, offset: usize) -> (u32, u32) {
    let mut line = 1u32;
    let mut column = 1u32;
    for (idx, ch) in source.char_indices() {
        if idx >= offset {
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

/// The words a report uses for a kind of trust debt.
#[must_use]
pub fn registration_warning_label(kind: &RegistrationWarningKind) -> &'static str {
    match kind {
        RegistrationWarningKind::ExplicitSorry => "explicit sorry",
        RegistrationWarningKind::SyntheticSorry => "synthetic sorry",
        RegistrationWarningKind::TrustedArith => "trustedArith",
        RegistrationWarningKind::TrustedAy => "trustedAy",
    }
}

/// The name a verdict carries for `decl`: its written name, or the kind of an
/// anonymous form so a failing `import` is not reported as `(anonymous)`.
pub(super) fn verdict_name(decl: &SurfaceDecl) -> String {
    surface_decl_name(decl).unwrap_or_else(|| {
        match decl {
            SurfaceDecl::Import { .. } => "import",
            SurfaceDecl::Example { .. } => "example",
            _ => "(anonymous)",
        }
        .to_owned()
    })
}

/// One module's source with its line starts indexed once, so locating a
/// declaration is a binary search instead of a walk from byte 0
/// ([`line_column_for_offset`]). The driver locates every verdict it records;
/// a walk per verdict would be quadratic in the module.
pub(super) struct SourceLines<'a> {
    source: &'a str,
    /// The byte offset of every `\n` in `source`, ascending.
    newlines: Vec<usize>,
}

impl<'a> SourceLines<'a> {
    pub(super) fn new(source: &'a str) -> Self {
        let newlines = source
            .bytes()
            .enumerate()
            .filter(|&(_, byte)| byte == b'\n')
            .map(|(at, _)| at)
            .collect();
        Self { source, newlines }
    }

    /// The 1-based line `decl` starts on, when it can be located: the line
    /// [`source_span`] reports for it. A `\n` byte is always a whole character
    /// in UTF-8, so counting newline bytes before the offset counts the lines
    /// `line_column_for_offset` walks past.
    pub(super) fn decl_line(&self, decl: &SurfaceDecl) -> Option<u32> {
        let span = surface_decl_span(decl)?;
        self.span_line(span)
    }

    pub(super) fn span_line(&self, span: Span) -> Option<u32> {
        if span.end < span.start || span.start > self.source.len() {
            return None;
        }
        let before = self.newlines.partition_point(|&at| at < span.start);
        Some(u32::try_from(before).map_or(u32::MAX, |lines| lines.saturating_add(1)))
    }
}
