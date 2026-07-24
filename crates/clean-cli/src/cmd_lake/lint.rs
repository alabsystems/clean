// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Source-level lint engine for `clean lake lint`.
//!
//! The engine analyses each module's surface syntax and reports issues that
//! are cheaply *and* soundly detectable without a full elaboration pass:
//!
//! - [`LintRule::ParseError`] — the module does not parse.
//! - [`LintRule::UnusedBinding`] — a `let`/`fun` binding whose name never
//!   appears in the binding's body.
//! - [`LintRule::ShadowedBinding`] — a `let`/`fun` binding whose name shadows
//!   an enclosing binder still in scope.
//! - [`LintRule::MissingDocs`] — a public top-level declaration with no
//!   doc-comment / leading `--` line comment.
//!
//! Soundness note: the "used" check is a *textual* over-approximation. We slice
//! the body's source text (`Span` carries byte offsets into the original
//! source) and look for the bound name as a whole identifier token. Because the
//! scan can only ever *over-count* uses, we never falsely flag a binding that is
//! genuinely used. This also keeps the analysis robust against future
//! `SurfaceExpr` variants — a hand-written AST walker would silently miss uses
//! if a variant were added.
//!
//! Deeper, elaboration-driven rules (unsolved-goal warnings, dead `simp` lemmas,
//! unused `import`s resolved against the real environment) are deferred; see the
//! module-level follow-ups in `clean lake lint`'s command handler.

use clean_parser::{
    parse_file_with_tactics_diagnostics, SurfaceBinder, SurfaceDecl, SurfaceExpr,
    SurfaceFieldAssign,
};
use std::fmt;

/// A lint rule category.
///
/// Stable identifiers are emitted in the textual report so downstream tooling
/// can grep for specific rules.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum LintRule {
    /// The module failed to parse.
    ParseError,
    /// A `let`/`fun` binding is never referenced in its body.
    UnusedBinding,
    /// A `let`/`fun` binding shadows an enclosing binder still in scope.
    ShadowedBinding,
    /// A public top-level declaration has no documentation comment.
    MissingDocs,
}

impl LintRule {
    /// Stable, machine-greppable identifier for the rule.
    pub(crate) fn id(self) -> &'static str {
        match self {
            LintRule::ParseError => "parse-error",
            LintRule::UnusedBinding => "unused-binding",
            LintRule::ShadowedBinding => "shadowed-binding",
            LintRule::MissingDocs => "missing-docs",
        }
    }

    /// Whether the rule represents an error (vs. a warning).
    pub(crate) fn is_error(self) -> bool {
        matches!(self, LintRule::ParseError)
    }
}

impl fmt::Display for LintRule {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.id())
    }
}

/// A single lint finding with a 1-based line/column location.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct LintIssue {
    /// The rule that produced the finding.
    pub(crate) rule: LintRule,
    /// 1-based line number in the source file.
    pub(crate) line: usize,
    /// 1-based column number in the source file.
    pub(crate) column: usize,
    /// Human-readable description of the issue.
    pub(crate) message: String,
}

impl LintIssue {
    fn new(rule: LintRule, line: usize, column: usize, message: impl Into<String>) -> Self {
        Self {
            rule,
            line,
            column,
            message: message.into(),
        }
    }
}

/// Counts of lint findings, partitioned by severity.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub(crate) struct LintSummary {
    /// Number of error-severity findings.
    pub(crate) errors: usize,
    /// Number of warning-severity findings.
    pub(crate) warnings: usize,
}

impl LintSummary {
    /// Total number of findings.
    pub(crate) fn total(self) -> usize {
        self.errors + self.warnings
    }
}

/// Result of linting a single module's source text.
#[derive(Debug, Clone, Default)]
pub(crate) struct ModuleLintReport {
    /// Findings sorted by source position.
    pub(crate) issues: Vec<LintIssue>,
}

impl ModuleLintReport {
    /// Aggregate severity counts.
    pub(crate) fn summary(&self) -> LintSummary {
        let mut summary = LintSummary::default();
        for issue in &self.issues {
            if issue.rule.is_error() {
                summary.errors += 1;
            } else {
                summary.warnings += 1;
            }
        }
        summary
    }
}

/// Lint the source text of a single module.
///
/// This is pure (no I/O) so it can be exercised directly in unit tests.
pub(crate) fn lint_source(source: &str) -> ModuleLintReport {
    let line_index = LineIndex::new(source);
    let patterns = clean_elab::tactic::builtins::builtin_tactic_patterns();

    // The recovery-aware parser turns malformed declarations into structured
    // diagnostics plus `RawDecl` placeholders, so we can surface a precise
    // `parse-error` finding *and* still lint the recoverable declarations.
    let report = match parse_file_with_tactics_diagnostics(source, &patterns) {
        Ok(report) => report,
        Err(err) => {
            // A hard parse error (no recovery) — point at end-of-input.
            let (line, column) = line_index.line_col(line_index.len());
            return ModuleLintReport {
                issues: vec![LintIssue::new(
                    LintRule::ParseError,
                    line,
                    column,
                    err.to_string(),
                )],
            };
        }
    };

    let mut issues = Vec::new();
    for diag in &report.diagnostics {
        // The parser reports a 1-based line and 0-based column; normalise the
        // column to 1-based for a consistent report.
        let line = diag.recovery_start.line.max(1);
        let column = diag.recovery_start.column.saturating_add(1);
        issues.push(LintIssue::new(
            LintRule::ParseError,
            line,
            column,
            diag.message.clone(),
        ));
    }

    for decl in &report.decls {
        lint_decl(decl, source, &line_index, &mut issues);
    }

    issues.sort_by(|a, b| (a.line, a.column, a.rule.id()).cmp(&(b.line, b.column, b.rule.id())));
    ModuleLintReport { issues }
}

/// Lint a single top-level (or nested) declaration.
fn lint_decl(decl: &SurfaceDecl, source: &str, index: &LineIndex, issues: &mut Vec<LintIssue>) {
    match decl {
        SurfaceDecl::Def {
            span,
            name,
            binders,
            val,
            modifiers,
            ..
        } => {
            check_missing_docs(*span, name, modifiers.visibility, source, index, issues);
            let scope: Vec<String> = binders.iter().map(|b| b.name.clone()).collect();
            check_binder_shadowing(binders, &[], *span, index, issues);
            lint_expr(val, source, index, &scope, issues);
        }
        SurfaceDecl::Theorem {
            span,
            name,
            binders,
            proof,
            modifiers,
            ..
        } => {
            check_missing_docs(*span, name, modifiers.visibility, source, index, issues);
            let scope: Vec<String> = binders.iter().map(|b| b.name.clone()).collect();
            check_binder_shadowing(binders, &[], *span, index, issues);
            lint_expr(proof, source, index, &scope, issues);
        }
        SurfaceDecl::Example {
            binders, val, span, ..
        } => {
            let scope: Vec<String> = binders.iter().map(|b| b.name.clone()).collect();
            check_binder_shadowing(binders, &[], *span, index, issues);
            lint_expr(val, source, index, &scope, issues);
        }
        SurfaceDecl::Opaque {
            span,
            name,
            val,
            modifiers,
            ..
        } => {
            check_missing_docs(*span, name, modifiers.visibility, source, index, issues);
            if let Some(val) = val {
                lint_expr(val, source, index, &[], issues);
            }
        }
        SurfaceDecl::Axiom {
            span,
            name,
            modifiers,
            ..
        } => {
            check_missing_docs(*span, name, modifiers.visibility, source, index, issues);
        }
        SurfaceDecl::Inductive {
            span,
            name,
            modifiers,
            ..
        }
        | SurfaceDecl::Coinductive {
            span,
            name,
            modifiers,
            ..
        }
        | SurfaceDecl::Structure {
            span,
            name,
            modifiers,
            ..
        }
        | SurfaceDecl::Class {
            span,
            name,
            modifiers,
            ..
        } => {
            check_missing_docs(*span, name, modifiers.visibility, source, index, issues);
        }
        SurfaceDecl::Namespace { decls, .. }
        | SurfaceDecl::Section { decls, .. }
        | SurfaceDecl::Mutual { decls, .. } => {
            for inner in decls {
                lint_decl(inner, source, index, issues);
            }
        }
        // Commands and metaprogramming forms carry no cheaply-lintable surface.
        _ => {}
    }
}

/// `missing-docs`: flag public top-level declarations with no preceding
/// documentation comment (`/-- ... -/`) or `--` line comment.
fn check_missing_docs(
    span: clean_parser::Span,
    name: &str,
    visibility: clean_parser::Visibility,
    source: &str,
    index: &LineIndex,
    issues: &mut Vec<LintIssue>,
) {
    if visibility != clean_parser::Visibility::Public {
        return;
    }
    if has_doc_comment_before(span.start, source) {
        return;
    }
    let (line, column) = index.line_col(span.start);
    issues.push(LintIssue::new(
        LintRule::MissingDocs,
        line,
        column,
        format!("public declaration `{name}` is missing documentation"),
    ));
}

/// Returns `true` if the non-blank line immediately preceding `offset` is a
/// documentation/line comment (`/-- ... -/`, `--`, or a closing `-/`).
fn has_doc_comment_before(offset: usize, source: &str) -> bool {
    let prefix = &source[..offset.min(source.len())];
    // Walk back over blank lines to the last non-empty preceding line.
    for line in prefix.lines().rev() {
        let trimmed = line.trim();
        if trimmed.is_empty() {
            continue;
        }
        return trimmed.starts_with("--")
            || trimmed.starts_with("/--")
            || trimmed.starts_with("/-")
            || trimmed.ends_with("-/");
    }
    false
}

/// Walk an expression, tracking the set of in-scope binder names so we can flag
/// shadowing, and the body text so we can flag unused bindings.
fn lint_expr(
    expr: &SurfaceExpr,
    source: &str,
    index: &LineIndex,
    scope: &[String],
    issues: &mut Vec<LintIssue>,
) {
    match expr {
        SurfaceExpr::Let(span, binder, value, body)
        | SurfaceExpr::LetRec(span, binder, value, body) => {
            // Value is elaborated in the outer scope.
            lint_expr(value, source, index, scope, issues);
            check_binder_shadowing(std::slice::from_ref(binder), scope, *span, index, issues);
            check_unused_binding(binder, body, *span, source, index, issues);
            let mut inner = scope.to_vec();
            inner.push(binder.name.clone());
            lint_expr(body, source, index, &inner, issues);
        }
        SurfaceExpr::Lambda(span, binders, body)
        | SurfaceExpr::PatternMatchLambda(span, binders, body)
        | SurfaceExpr::Pi(span, binders, body) => {
            check_binder_shadowing(binders, scope, *span, index, issues);
            for binder in binders {
                check_unused_binding(binder, body, *span, source, index, issues);
            }
            let mut inner = scope.to_vec();
            inner.extend(binders.iter().map(|b| b.name.clone()));
            lint_expr(body, source, index, &inner, issues);
        }
        SurfaceExpr::App(_, f, args) => {
            lint_expr(f, source, index, scope, issues);
            for arg in args {
                lint_expr(&arg.expr, source, index, scope, issues);
            }
        }
        SurfaceExpr::Arrow(_, a, b) | SurfaceExpr::Ascription(_, a, b) => {
            lint_expr(a, source, index, scope, issues);
            lint_expr(b, source, index, scope, issues);
        }
        SurfaceExpr::Paren(_, inner)
        | SurfaceExpr::OutParam(_, inner)
        | SurfaceExpr::SemiOutParam(_, inner)
        | SurfaceExpr::Explicit(_, inner)
        | SurfaceExpr::LiftMethod(_, inner)
        | SurfaceExpr::NamedArg(_, _, inner)
        | SurfaceExpr::UniverseInst(_, inner, _)
        | SurfaceExpr::Proj(_, inner, _) => {
            lint_expr(inner, source, index, scope, issues);
        }
        SurfaceExpr::If(_, c, t, e) | SurfaceExpr::IfDecidable(_, _, c, t, e) => {
            lint_expr(c, source, index, scope, issues);
            lint_expr(t, source, index, scope, issues);
            lint_expr(e, source, index, scope, issues);
        }
        SurfaceExpr::Match(_, _, scrut, arms) => {
            lint_expr(scrut, source, index, scope, issues);
            for arm in arms {
                lint_expr(&arm.body, source, index, scope, issues);
            }
        }
        SurfaceExpr::StructLit { fields, base, .. } => {
            if let Some(base) = base {
                lint_expr(base, source, index, scope, issues);
            }
            for field in fields {
                lint_field_assign(field, source, index, scope, issues);
            }
        }
        // Other forms (literals, holes, quotations, tactic/do blocks, …) carry
        // no cheaply-lintable binding structure for this pass.
        _ => {}
    }
}

/// Lint the value of a struct-literal field assignment.
fn lint_field_assign(
    field: &SurfaceFieldAssign,
    source: &str,
    index: &LineIndex,
    scope: &[String],
    issues: &mut Vec<LintIssue>,
) {
    lint_expr(&field.val, source, index, scope, issues);
}

/// `unused-binding`: flag a binding whose name never appears as an identifier
/// token in the body's source text.
fn check_unused_binding(
    binder: &SurfaceBinder,
    body: &SurfaceExpr,
    decl_span: clean_parser::Span,
    source: &str,
    index: &LineIndex,
    issues: &mut Vec<LintIssue>,
) {
    if is_anonymous(&binder.name) {
        return;
    }
    let body_span = body.span();
    let snippet = span_text(source, body_span);
    if !identifier_used(&binder.name, snippet) {
        let (line, column) = binder_location(binder, decl_span, index);
        issues.push(LintIssue::new(
            LintRule::UnusedBinding,
            line,
            column,
            format!("binding `{}` is never used", binder.name),
        ));
    }
}

/// `shadowed-binding`: flag any binder whose name is already present in `scope`.
fn check_binder_shadowing(
    binders: &[SurfaceBinder],
    scope: &[String],
    decl_span: clean_parser::Span,
    index: &LineIndex,
    issues: &mut Vec<LintIssue>,
) {
    // Track names introduced within this binder group too, so
    // `fun x x => ...` is flagged.
    let mut seen: Vec<&str> = scope.iter().map(String::as_str).collect();
    for binder in binders {
        if is_anonymous(&binder.name) {
            continue;
        }
        if seen.contains(&binder.name.as_str()) {
            let (line, column) = binder_location(binder, decl_span, index);
            issues.push(LintIssue::new(
                LintRule::ShadowedBinding,
                line,
                column,
                format!("binding `{}` shadows an existing binding", binder.name),
            ));
        }
        seen.push(binder.name.as_str());
    }
}

/// Best-effort 1-based location for a binder. Falls back to the enclosing
/// declaration's span when the binder span is a dummy `(0, 0)`.
fn binder_location(
    binder: &SurfaceBinder,
    decl_span: clean_parser::Span,
    index: &LineIndex,
) -> (usize, usize) {
    if binder.span.start == 0 && binder.span.end == 0 {
        index.line_col(decl_span.start)
    } else {
        index.line_col(binder.span.start)
    }
}

/// `true` for anonymous / wildcard binder names that should not be linted.
fn is_anonymous(name: &str) -> bool {
    name.is_empty() || name == "_" || name.starts_with('_')
}

/// Slice the source by a span, defensively clamping to the source length.
fn span_text(source: &str, span: clean_parser::Span) -> &str {
    let start = span.start.min(source.len());
    let end = span.end.min(source.len()).max(start);
    source.get(start..end).unwrap_or("")
}

/// Returns `true` if `name` appears as a whole identifier token in `text`.
///
/// A "whole identifier" is bounded by characters that cannot be part of a Lean
/// identifier (ASCII alphanumerics, `_`, `'`, `.`, and non-ASCII letters such
/// as Greek used in Mathlib). This over-approximates uses, so it never flags a
/// genuinely-used binding.
fn identifier_used(name: &str, text: &str) -> bool {
    if name.is_empty() {
        return true;
    }
    let bytes = text.as_bytes();
    let needle = name.as_bytes();
    let mut search_from = 0;
    while let Some(rel) = find_subslice(&bytes[search_from..], needle) {
        let start = search_from + rel;
        let end = start + needle.len();
        let before_ok = start == 0 || !is_ident_char(prev_char(text, start));
        let after_ok = end >= text.len() || !is_ident_char(next_char(text, end));
        if before_ok && after_ok {
            return true;
        }
        search_from = start + 1;
    }
    false
}

/// Find the first occurrence of `needle` in `haystack`, returning its index.
fn find_subslice(haystack: &[u8], needle: &[u8]) -> Option<usize> {
    if needle.is_empty() || needle.len() > haystack.len() {
        return None;
    }
    haystack
        .windows(needle.len())
        .position(|window| window == needle)
}

/// The character ending just before byte index `idx`.
fn prev_char(text: &str, idx: usize) -> char {
    text[..idx].chars().next_back().unwrap_or(' ')
}

/// The character starting at byte index `idx`.
fn next_char(text: &str, idx: usize) -> char {
    text[idx..].chars().next().unwrap_or(' ')
}

/// Whether `c` can be part of a Lean identifier token.
fn is_ident_char(c: char) -> bool {
    c == '_' || c == '\'' || c == '.' || c.is_alphanumeric()
}

/// Maps byte offsets to 1-based `(line, column)` positions.
struct LineIndex {
    /// Byte offset of the start of each line.
    line_starts: Vec<usize>,
    len: usize,
}

impl LineIndex {
    fn new(source: &str) -> Self {
        let mut line_starts = vec![0usize];
        for (idx, byte) in source.bytes().enumerate() {
            if byte == b'\n' {
                line_starts.push(idx + 1);
            }
        }
        Self {
            line_starts,
            len: source.len(),
        }
    }

    fn len(&self) -> usize {
        self.len
    }

    /// Convert a byte offset to a 1-based `(line, column)`.
    fn line_col(&self, offset: usize) -> (usize, usize) {
        let offset = offset.min(self.len);
        // Binary search for the last line start <= offset.
        let line = match self.line_starts.binary_search(&offset) {
            Ok(idx) => idx,
            Err(idx) => idx.saturating_sub(1),
        };
        let line_start = self.line_starts.get(line).copied().unwrap_or(0);
        let column = offset.saturating_sub(line_start) + 1;
        (line + 1, column)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_line_index_line_col_first_line() {
        let index = LineIndex::new("abc\ndef\n");
        assert_eq!(index.line_col(0), (1, 1));
        assert_eq!(index.line_col(2), (1, 3));
    }

    #[test]
    fn test_line_index_line_col_second_line() {
        let index = LineIndex::new("abc\ndef\n");
        assert_eq!(index.line_col(4), (2, 1));
        assert_eq!(index.line_col(6), (2, 3));
    }

    #[test]
    fn test_identifier_used_whole_token_matches() {
        assert!(identifier_used("x", "x + 1"));
        assert!(identifier_used("foo", "bar (foo y)"));
    }

    #[test]
    fn test_identifier_used_substring_does_not_match() {
        // `x` must not match inside `xs` or `max`.
        assert!(!identifier_used("x", "xs + max"));
    }

    #[test]
    fn test_identifier_used_qualified_prefix_does_not_match() {
        // `Nat` should not match the namespace segment of `Nat.add` as a use
        // of a local binding named `add`.
        assert!(!identifier_used("add", "Nat.add"));
    }

    #[test]
    fn test_lint_clean_def_reports_no_issues() {
        let report = lint_source("/-- Doc. -/\ndef f (x : Nat) : Nat := x\n");
        assert!(
            report.issues.is_empty(),
            "clean documented def should be issue-free, got {:?}",
            report.issues
        );
    }

    #[test]
    fn test_lint_unused_let_binding_is_flagged() {
        // Semicolon `let v := e; body` form parses to a `Let` node.
        let report = lint_source("/-- Doc. -/\ndef f : Nat := let y := 5; 3\n");
        let unused: Vec<_> = report
            .issues
            .iter()
            .filter(|i| i.rule == LintRule::UnusedBinding)
            .collect();
        assert_eq!(
            unused.len(),
            1,
            "expected one unused-binding finding, got {:?}",
            report.issues
        );
        assert!(unused[0].message.contains('y'));
        assert!(unused[0].line >= 1);
    }

    #[test]
    fn test_lint_used_let_binding_is_not_flagged() {
        let report = lint_source("/-- Doc. -/\ndef f : Nat := let y := 5; y\n");
        assert!(
            report
                .issues
                .iter()
                .all(|i| i.rule != LintRule::UnusedBinding),
            "used let binding must not be flagged: {:?}",
            report.issues
        );
    }

    #[test]
    fn test_lint_unused_lambda_binding_is_flagged() {
        let report = lint_source("/-- Doc. -/\ndef f : Nat -> Nat := fun y => 3\n");
        assert!(
            report
                .issues
                .iter()
                .any(|i| i.rule == LintRule::UnusedBinding && i.message.contains('y')),
            "unused lambda binding must be flagged: {:?}",
            report.issues
        );
    }

    #[test]
    fn test_lint_underscore_binding_is_ignored() {
        let report = lint_source("/-- Doc. -/\ndef f : Nat -> Nat := fun _ => 3\n");
        assert!(
            report
                .issues
                .iter()
                .all(|i| i.rule != LintRule::UnusedBinding),
            "underscore binding must be ignored: {:?}",
            report.issues
        );
    }

    #[test]
    fn test_lint_shadowed_binding_is_flagged() {
        // The lambda binder `x` shadows the def parameter `x`.
        let report = lint_source("/-- Doc. -/\ndef f (x : Nat) : Nat := fun x => x\n");
        let shadow: Vec<_> = report
            .issues
            .iter()
            .filter(|i| i.rule == LintRule::ShadowedBinding)
            .collect();
        assert_eq!(
            shadow.len(),
            1,
            "expected one shadowed-binding finding, got {:?}",
            report.issues
        );
        assert!(shadow[0].message.contains('x'));
    }

    #[test]
    fn test_lint_parse_error_is_reported() {
        // An unterminated parenthesized body is unambiguously malformed. The
        // former indentation fixture became valid when newline-let parsing was
        // fixed, so it no longer exercised the recovery lane.
        let report = lint_source("def f : Nat := (\n");
        assert!(
            report.issues.iter().any(|i| i.rule == LintRule::ParseError),
            "malformed module must produce a parse-error finding: {:?}",
            report.issues
        );
        assert!(report.summary().errors >= 1);
    }

    #[test]
    fn test_lint_missing_docs_flags_public_decl() {
        let report = lint_source("def f : Nat := 3\n");
        assert!(
            report
                .issues
                .iter()
                .any(|i| i.rule == LintRule::MissingDocs),
            "undocumented public def should be flagged: {:?}",
            report.issues
        );
    }

    #[test]
    fn test_lint_doc_comment_suppresses_missing_docs() {
        let report = lint_source("/-- Doc. -/\ndef f : Nat := 3\n");
        assert!(
            report
                .issues
                .iter()
                .all(|i| i.rule != LintRule::MissingDocs),
            "documented def must not be flagged: {:?}",
            report.issues
        );
    }

    #[test]
    fn test_lint_private_decl_not_flagged_for_docs() {
        let report = lint_source("private def f : Nat := 3\n");
        assert!(
            report
                .issues
                .iter()
                .all(|i| i.rule != LintRule::MissingDocs),
            "private def should not require docs: {:?}",
            report.issues
        );
    }

    #[test]
    fn test_summary_counts_errors_and_warnings() {
        // Documented def + unused let (semicolon form): warning-only report.
        let report = lint_source("/-- Doc. -/\ndef f : Nat := let y := 5; 3\n");
        let summary = report.summary();
        assert_eq!(summary.errors, 0);
        assert!(summary.warnings >= 1);
        assert_eq!(summary.total(), report.issues.len());
    }

    #[test]
    fn test_summary_counts_parse_error_as_error() {
        let report = lint_source("def f : Nat := (\n");
        let summary = report.summary();
        assert!(summary.errors >= 1);
    }
}
