// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended error recovery: multi-error collection, severity classification,
//! span tracking, recovery strategies, formatting, deduplication, error budget,
//! diagnostic hints, context propagation, and statistics.

use std::collections::HashMap;
use std::fmt;

use crate::error::ElabError;

/// Diagnostic severity levels matching LSP specification.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum DiagnosticSeverity {
    Error,
    Warning,
    Info,
    Hint,
}

impl fmt::Display for DiagnosticSeverity {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Error => f.write_str("error"),
            Self::Warning => f.write_str("warning"),
            Self::Info => f.write_str("info"),
            Self::Hint => f.write_str("hint"),
        }
    }
}

/// Precise source location for a diagnostic.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct SourceSpan {
    pub(crate) start: usize,
    pub(crate) end: usize,
    pub(crate) line: u32,
    pub(crate) column: u32,
}

impl fmt::Display for SourceSpan {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}:{} [{}-{})",
            self.line + 1,
            self.column + 1,
            self.start,
            self.end
        )
    }
}

/// How the elaborator should recover from an error.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub(crate) enum ExtRecoveryStrategy {
    InsertSorry,
    UseMetavariable,
    SkipDeclaration,
    FallbackType,
}

impl fmt::Display for ExtRecoveryStrategy {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InsertSorry => f.write_str("insert sorry"),
            Self::UseMetavariable => f.write_str("use metavariable"),
            Self::SkipDeclaration => f.write_str("skip declaration"),
            Self::FallbackType => f.write_str("fallback type"),
        }
    }
}

/// A suggested fix for a diagnostic.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct DiagnosticHint {
    pub(crate) message: String,
    pub(crate) replacement: Option<String>,
}

impl fmt::Display for DiagnosticHint {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.message)?;
        if let Some(ref repl) = self.replacement {
            write!(f, " (try: `{repl}`)")?;
        }
        Ok(())
    }
}

/// Generate hints for common error patterns.
#[must_use]
pub(crate) fn hint_for_error(error: &ElabError) -> Vec<DiagnosticHint> {
    match error {
        ElabError::UnknownIdent(name) => {
            let mut hints = vec![DiagnosticHint {
                message: format!("Did you mean to import a module containing `{name}`?"),
                replacement: None,
            }];
            if name.starts_with(|c: char| c.is_uppercase()) {
                hints.push(DiagnosticHint {
                    message: "Identifiers starting with uppercase are usually types or namespaces"
                        .into(),
                    replacement: None,
                });
            }
            hints
        }
        ElabError::UnknownIdentWithSuggestions { suggestions, .. } => suggestions
            .iter()
            .map(|name| DiagnosticHint {
                message: format!("Nearest theorem name: `{name}`"),
                replacement: Some(name.clone()),
            })
            .collect(),
        ElabError::UnknownProjectionField {
            field, suggestions, ..
        } => suggestions
            .iter()
            .map(|name| DiagnosticHint {
                message: format!("Replace unknown projection field `{field}` with `{name}`"),
                replacement: Some(name.clone()),
            })
            .collect(),
        ElabError::UnknownStructureField {
            field, suggestions, ..
        } => suggestions
            .iter()
            .map(|name| DiagnosticHint {
                message: format!("Replace unknown field `{field}` with `{name}`"),
                replacement: Some(name.clone()),
            })
            .collect(),
        ElabError::MissingStructureFields { fields, .. } => fields
            .iter()
            .map(|field| DiagnosticHint {
                message: format!("Provide required structure field `{field}`"),
                replacement: Some(format!("{field} := _")),
            })
            .collect(),
        ElabError::StructureFieldTypeMismatch {
            field,
            expected,
            actual,
            ..
        } => vec![DiagnosticHint {
            message: format!("Field `{field}` expected `{expected}` but got `{actual}`"),
            replacement: None,
        }],
        ElabError::TypeMismatch { expected, actual } => vec![DiagnosticHint {
            message: format!("Expected `{expected}` but got `{actual}`"),
            replacement: None,
        }],
        ElabError::CannotInfer => vec![DiagnosticHint {
            message: "Try adding a type annotation".into(),
            replacement: Some(": <type>".into()),
        }],
        ElabError::NotImplemented(feature) => vec![DiagnosticHint {
            message: format!("Feature `{feature}` is not yet implemented"),
            replacement: None,
        }],
        ElabError::TooManyArguments { .. } => vec![DiagnosticHint {
            message: "Remove extra arguments or check the function's type signature".into(),
            replacement: None,
        }],
        ElabError::AnonymousCtorNoExpectedType => vec![DiagnosticHint {
            message: "Provide an expected type for the anonymous constructor".into(),
            replacement: Some("(⟨...⟩ : T)".into()),
        }],
        _ => Vec::new(),
    }
}

/// Additional context pointing to a related source location.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct RelatedInfo {
    pub(crate) message: String,
    pub(crate) span: Option<SourceSpan>,
}

/// A fully structured diagnostic with context, hints, and related info.
#[derive(Debug, Clone)]
pub(crate) struct Diagnostic {
    pub(crate) error: ElabError,
    pub(crate) severity: DiagnosticSeverity,
    pub(crate) span: Option<SourceSpan>,
    pub(crate) context_path: Vec<String>,
    pub(crate) recovery: Option<ExtRecoveryStrategy>,
    pub(crate) hints: Vec<DiagnosticHint>,
    pub(crate) related: Vec<RelatedInfo>,
}

impl fmt::Display for Diagnostic {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.severity)?;
        if let Some(ref span) = self.span {
            write!(f, " at {span}")?;
        }
        write!(f, ": {}", self.error)?;
        if !self.context_path.is_empty() {
            write!(f, " (in {})", self.context_path.join(" > "))?;
        }
        if let Some(ref strat) = self.recovery {
            write!(f, " [recovered: {strat}]")?;
        }
        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct DedupKey {
    error_msg: String,
    span_start: Option<usize>,
    span_end: Option<usize>,
}

impl DedupKey {
    fn from_diagnostic(diag: &Diagnostic) -> Self {
        Self {
            error_msg: format!("{}", diag.error),
            span_start: diag.span.map(|s| s.start),
            span_end: diag.span.map(|s| s.end),
        }
    }
}

/// Aggregate statistics about collected diagnostics.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct DiagnosticStats {
    pub(crate) errors: usize,
    pub(crate) warnings: usize,
    pub(crate) infos: usize,
    pub(crate) hints: usize,
    pub(crate) recovered: usize,
    pub(crate) fatal: usize,
    pub(crate) deduplicated: usize,
}

impl DiagnosticStats {
    #[must_use]
    pub(crate) fn total(&self) -> usize {
        self.errors + self.warnings + self.infos + self.hints
    }
}

impl fmt::Display for DiagnosticStats {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} error(s), {} warning(s), {} info(s), {} hint(s) \
             | {} recovered, {} fatal, {} deduplicated",
            self.errors,
            self.warnings,
            self.infos,
            self.hints,
            self.recovered,
            self.fatal,
            self.deduplicated
        )
    }
}

/// Configuration for the diagnostic collector.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CollectorConfig {
    pub(crate) error_budget: usize,
    pub(crate) deduplicate: bool,
    pub(crate) default_strategy: ExtRecoveryStrategy,
}

impl Default for CollectorConfig {
    fn default() -> Self {
        Self {
            error_budget: 100,
            deduplicate: true,
            default_strategy: ExtRecoveryStrategy::InsertSorry,
        }
    }
}

impl CollectorConfig {
    #[must_use]
    pub(crate) fn with_error_budget(mut self, budget: usize) -> Self {
        self.error_budget = budget;
        self
    }
    #[must_use]
    pub(crate) fn with_deduplicate(mut self, dedup: bool) -> Self {
        self.deduplicate = dedup;
        self
    }
    #[must_use]
    pub(crate) fn with_default_strategy(mut self, strategy: ExtRecoveryStrategy) -> Self {
        self.default_strategy = strategy;
        self
    }
}

/// Context stack carried through nested elaboration for diagnostic context.
#[derive(Debug, Clone, Default)]
pub(crate) struct ErrorContext {
    stack: Vec<String>,
}

impl ErrorContext {
    #[must_use]
    pub(crate) fn new() -> Self {
        Self::default()
    }

    pub(crate) fn push(&mut self, frame: &str) {
        self.stack.push(frame.to_owned());
    }
    pub(crate) fn pop(&mut self) -> Option<String> {
        self.stack.pop()
    }

    #[must_use]
    pub(crate) fn path(&self) -> &[String] {
        &self.stack
    }
    #[must_use]
    pub(crate) fn depth(&self) -> usize {
        self.stack.len()
    }
}

/// Collects diagnostics during elaboration with dedup, budget, hints, and
/// context propagation.
pub(crate) struct DiagnosticCollector {
    diagnostics: Vec<Diagnostic>,
    seen: HashMap<DedupKey, usize>,
    config: CollectorConfig,
    context: ErrorContext,
    stats: DiagnosticStats,
    budget_exhausted: bool,
}

impl DiagnosticCollector {
    #[must_use]
    pub(crate) fn new(config: CollectorConfig) -> Self {
        Self {
            diagnostics: Vec::new(),
            seen: HashMap::new(),
            config,
            context: ErrorContext::new(),
            stats: DiagnosticStats::default(),
            budget_exhausted: false,
        }
    }

    pub(crate) fn push_context(&mut self, frame: &str) {
        self.context.push(frame);
    }
    pub(crate) fn pop_context(&mut self) -> Option<String> {
        self.context.pop()
    }
    #[must_use]
    pub(crate) fn context_depth(&self) -> usize {
        self.context.depth()
    }
    #[must_use]
    pub(crate) fn is_budget_exhausted(&self) -> bool {
        self.budget_exhausted
    }
    #[must_use]
    pub(crate) fn should_continue(&self) -> bool {
        !self.budget_exhausted
    }
    #[must_use]
    pub(crate) fn count(&self) -> usize {
        self.diagnostics.len()
    }

    /// Add a diagnostic. Returns `true` if added (not duplicate, within budget).
    pub(crate) fn add_diagnostic(
        &mut self,
        error: ElabError,
        severity: DiagnosticSeverity,
        span: Option<SourceSpan>,
        recovery: Option<ExtRecoveryStrategy>,
        related: Vec<RelatedInfo>,
    ) -> bool {
        if self.budget_exhausted {
            return false;
        }
        let hints = hint_for_error(&error);
        let context_path = self.context.path().to_vec();
        let diag = Diagnostic {
            error,
            severity,
            span,
            context_path,
            recovery,
            hints,
            related,
        };

        if self.config.deduplicate {
            let key = DedupKey::from_diagnostic(&diag);
            if let Some(&idx) = self.seen.get(&key) {
                self.stats.deduplicated += 1;
                if let Some(existing) = self.diagnostics.get_mut(idx) {
                    for r in diag.related {
                        existing.related.push(r);
                    }
                }
                return false;
            }
            let idx = self.diagnostics.len();
            self.seen.insert(key, idx);
        }

        match severity {
            DiagnosticSeverity::Error => self.stats.errors += 1,
            DiagnosticSeverity::Warning => self.stats.warnings += 1,
            DiagnosticSeverity::Info => self.stats.infos += 1,
            DiagnosticSeverity::Hint => self.stats.hints += 1,
        }
        if recovery.is_some() {
            self.stats.recovered += 1;
        } else if severity == DiagnosticSeverity::Error {
            self.stats.fatal += 1;
        }
        self.diagnostics.push(diag);
        if self.stats.errors >= self.config.error_budget {
            self.budget_exhausted = true;
        }
        true
    }

    pub(crate) fn add_error(&mut self, error: ElabError, span: Option<SourceSpan>) -> bool {
        let strat = self.config.default_strategy;
        self.add_diagnostic(
            error,
            DiagnosticSeverity::Error,
            span,
            Some(strat),
            Vec::new(),
        )
    }

    pub(crate) fn add_warning(&mut self, error: ElabError, span: Option<SourceSpan>) -> bool {
        self.add_diagnostic(error, DiagnosticSeverity::Warning, span, None, Vec::new())
    }

    pub(crate) fn add_info(&mut self, error: ElabError, span: Option<SourceSpan>) -> bool {
        self.add_diagnostic(error, DiagnosticSeverity::Info, span, None, Vec::new())
    }

    pub(crate) fn add_fatal(&mut self, error: ElabError, span: Option<SourceSpan>) -> bool {
        self.add_diagnostic(error, DiagnosticSeverity::Error, span, None, Vec::new())
    }

    pub(crate) fn into_report(self) -> DiagnosticReport {
        DiagnosticReport {
            diagnostics: self.diagnostics,
            stats: self.stats,
        }
    }

    #[must_use]
    pub(crate) fn stats(&self) -> &DiagnosticStats {
        &self.stats
    }
    #[must_use]
    pub(crate) fn diagnostics(&self) -> &[Diagnostic] {
        &self.diagnostics
    }
}

/// Final report produced by consuming a [`DiagnosticCollector`].
#[derive(Debug, Clone)]
pub(crate) struct DiagnosticReport {
    pub(crate) diagnostics: Vec<Diagnostic>,
    pub(crate) stats: DiagnosticStats,
}

impl DiagnosticReport {
    #[must_use]
    pub(crate) fn has_errors(&self) -> bool {
        self.stats.errors > 0
    }

    #[must_use]
    pub(crate) fn filter_severity(&self, severity: DiagnosticSeverity) -> Vec<&Diagnostic> {
        self.diagnostics
            .iter()
            .filter(|d| d.severity == severity)
            .collect()
    }
}

impl fmt::Display for DiagnosticReport {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.diagnostics.is_empty() {
            return f.write_str("no diagnostics");
        }
        writeln!(f, "{}", self.stats)?;
        for (i, diag) in self.diagnostics.iter().enumerate() {
            writeln!(f, "  {}. {}", i + 1, diag)?;
            for hint in &diag.hints {
                writeln!(f, "     hint: {hint}")?;
            }
            for rel in &diag.related {
                write!(f, "     related: {}", rel.message)?;
                if let Some(ref span) = rel.span {
                    write!(f, " at {span}")?;
                }
                writeln!(f)?;
            }
        }
        Ok(())
    }
}
