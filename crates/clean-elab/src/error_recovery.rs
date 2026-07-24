// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Elaboration error recovery.
//!
//! Provides multi-error accumulation and sorry-based recovery for the elaborator.
//! Lean 4 continues past errors in interactive/IDE mode by inserting `sorry` terms
//! for failed subexpressions and collecting all errors for batch reporting.
//!
//! # Architecture
//!
//! [`ErrorRecoveryCtx`] wraps an elaboration pass and accumulates errors
//! instead of failing on the first. When an expression fails to elaborate,
//! the context inserts a synthetic sorry term (via the kernel's sorry
//! infrastructure) and continues. At the end, [`RecoveredResult`] carries
//! the partially-elaborated term alongside all collected errors.
//!
//! # Recovery modes
//!
//! | Mode | Behaviour |
//! |------|-----------|
//! | [`RecoveryMode::Strict`] | Fail on first error (batch compilation) |
//! | [`RecoveryMode::Lenient`] | Insert sorry, continue, stop at `max_errors` |
//! | [`RecoveryMode::Ide`] | Collect all errors regardless of count |

use std::fmt;

use clean_kernel::sorry::create_sorry_term;
use clean_kernel::{Environment, Expr, Name};

use crate::error::ElabError;

// ---------------------------------------------------------------------------
// Recovery mode
// ---------------------------------------------------------------------------

/// Controls how aggressively the elaborator recovers from errors.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum RecoveryMode {
    /// Stop on first error (batch compilation).
    Strict,
    /// Insert sorry and continue; stop after `max_errors`.
    Lenient,
    /// Collect every error, insert sorry everywhere, report all at end.
    Ide,
}

// ---------------------------------------------------------------------------
// Accumulated error
// ---------------------------------------------------------------------------

/// Action taken to recover from an error.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum RecoveryAction {
    /// A sorry term was inserted in place of the failed expression.
    InsertedSorry,
    /// The declaration was skipped entirely.
    SkippedDeclaration,
    /// A fallback type (`Sort 0`) was used when the expected type was unknown.
    UsedFallbackType,
    /// No recovery was attempted (strict mode).
    None,
}

impl fmt::Display for RecoveryAction {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InsertedSorry => f.write_str("inserted sorry"),
            Self::SkippedDeclaration => f.write_str("skipped declaration"),
            Self::UsedFallbackType => f.write_str("used fallback type"),
            Self::None => f.write_str("none"),
        }
    }
}

/// An elaboration error together with its source location and the recovery
/// action that was taken.
#[derive(Debug, Clone)]
pub(crate) struct AccumulatedError {
    /// The original elaboration error.
    pub(crate) error: ElabError,
    /// Byte-offset span `(start, end)` in the source, if known.
    pub(crate) span: Option<(usize, usize)>,
    /// Human-readable description of where in the elaboration this occurred.
    pub(crate) context: String,
    /// What recovery action was taken after this error.
    pub(crate) recovery_action: RecoveryAction,
}

impl fmt::Display for AccumulatedError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some((start, end)) = self.span {
            write!(f, "[{start}..{end}] ")?;
        }
        if !self.context.is_empty() {
            write!(f, "({}) ", self.context)?;
        }
        write!(f, "{}", self.error)?;
        if self.recovery_action != RecoveryAction::None {
            write!(f, " [recovery: {}]", self.recovery_action)?;
        }
        Ok(())
    }
}

// ---------------------------------------------------------------------------
// Recovery context
// ---------------------------------------------------------------------------

/// Default maximum number of errors before we stop recovering (lenient mode).
const DEFAULT_MAX_ERRORS: usize = 50;

/// Accumulates errors during an elaboration pass and decides whether to
/// continue or bail.
pub(crate) struct ErrorRecoveryCtx {
    mode: RecoveryMode,
    errors: Vec<AccumulatedError>,
    sorry_count: usize,
    max_errors: usize,
}

impl ErrorRecoveryCtx {
    /// Create a new recovery context with the given mode.
    #[must_use]
    pub(crate) fn new(mode: RecoveryMode) -> Self {
        Self {
            mode,
            errors: Vec::new(),
            sorry_count: 0,
            max_errors: DEFAULT_MAX_ERRORS,
        }
    }

    /// Override the maximum number of errors for lenient mode.
    #[must_use]
    pub(crate) fn with_max_errors(mut self, max: usize) -> Self {
        self.max_errors = max;
        self
    }

    /// Record an error with optional source span and context description.
    ///
    /// In strict mode the error is still recorded (for reporting) but
    /// `should_continue()` will return false immediately.
    pub(crate) fn record_error(
        &mut self,
        error: ElabError,
        span: Option<(usize, usize)>,
        context: &str,
        action: RecoveryAction,
    ) {
        if action == RecoveryAction::InsertedSorry {
            self.sorry_count += 1;
        }
        self.errors.push(AccumulatedError {
            error,
            span,
            context: context.to_owned(),
            recovery_action: action,
        });
    }

    /// Returns `true` if the elaborator should continue past the last error.
    #[must_use]
    pub(crate) fn should_continue(&self) -> bool {
        match self.mode {
            RecoveryMode::Strict => self.errors.is_empty(),
            RecoveryMode::Lenient => self.errors.len() < self.max_errors,
            RecoveryMode::Ide => true,
        }
    }

    /// Create a sorry term for a failed expression whose expected type is known.
    ///
    /// This delegates to the kernel's `create_sorry_term` which handles the
    /// polymorphic `sorry` axiom and provenance accounting.
    pub(crate) fn make_sorry_term(&self, env: &Environment, expected_type: &Expr) -> Expr {
        create_sorry_term(env, expected_type)
    }

    /// Create a sorry term when the expected type is unknown.
    ///
    /// Uses `Prop` (Sort 0) as the sorry target since it is the safest
    /// fallback: a sorry in `Prop` does not introduce any computational
    /// content.
    pub(crate) fn make_sorry_type(&self, env: &Environment) -> Expr {
        create_sorry_term(env, &Expr::prop())
    }

    /// Number of errors accumulated so far.
    #[must_use]
    pub(crate) fn error_count(&self) -> usize {
        self.errors.len()
    }

    /// Whether any errors have been recorded.
    #[must_use]
    pub(crate) fn has_errors(&self) -> bool {
        !self.errors.is_empty()
    }

    /// Number of sorry terms that were inserted.
    #[must_use]
    pub(crate) fn sorry_count(&self) -> usize {
        self.sorry_count
    }

    /// Current recovery mode.
    #[must_use]
    pub(crate) fn mode(&self) -> RecoveryMode {
        self.mode
    }

    /// Consume the context and produce a [`RecoveredResult`].
    ///
    /// `value` is `Some(expr)` when the elaboration produced at least a
    /// partial result, or `None` when nothing was recoverable (e.g.
    /// strict mode hit the first error).
    pub(crate) fn into_result<T>(self, value: Option<T>) -> RecoveredResult<T> {
        let is_complete = !self.has_errors();
        RecoveredResult {
            value,
            errors: self.errors,
            sorry_count: self.sorry_count,
            is_complete,
        }
    }
}

// ---------------------------------------------------------------------------
// Recovered result
// ---------------------------------------------------------------------------

/// Outcome of an elaboration pass with error recovery.
#[derive(Debug, Clone)]
pub(crate) struct RecoveredResult<T> {
    /// The (possibly partial) elaboration result, or `None` if nothing could
    /// be produced.
    pub(crate) value: Option<T>,
    /// All accumulated errors.
    pub(crate) errors: Vec<AccumulatedError>,
    /// Number of sorry terms inserted.
    pub(crate) sorry_count: usize,
    /// `true` when the elaboration completed without errors.
    pub(crate) is_complete: bool,
}

impl<T> RecoveredResult<T> {
    /// Convert a successful (error-free) value into a `RecoveredResult`.
    #[must_use]
    pub(crate) fn ok(value: T) -> Self {
        Self {
            value: Some(value),
            errors: Vec::new(),
            sorry_count: 0,
            is_complete: true,
        }
    }

    /// Convert into a `Result`, returning `Ok` when the result is complete
    /// and `Err(first_error)` otherwise.
    pub(crate) fn into_result(self) -> Result<T, ElabError> {
        if self.is_complete {
            if let Some(v) = self.value {
                return Ok(v);
            }
        }
        Err(self
            .errors
            .into_iter()
            .next()
            .map(|ae| ae.error)
            .unwrap_or(ElabError::CannotInfer))
    }
}

// ---------------------------------------------------------------------------
// Standalone recovery helpers
// ---------------------------------------------------------------------------

/// Recover from an expression elaboration error by inserting a sorry.
///
/// If `expected_type` is `Some`, the sorry has that type. Otherwise falls
/// back to a sorry of type `Prop`.
///
/// Records the error and recovery action in `ctx`.
pub(crate) fn recover_expr(
    env: &Environment,
    error: ElabError,
    expected_type: Option<&Expr>,
    span: Option<(usize, usize)>,
    context: &str,
    ctx: &mut ErrorRecoveryCtx,
) -> Expr {
    let (sorry, action) = match expected_type {
        Some(ty) => (ctx.make_sorry_term(env, ty), RecoveryAction::InsertedSorry),
        None => (ctx.make_sorry_type(env), RecoveryAction::UsedFallbackType),
    };
    ctx.record_error(error, span, context, action);
    sorry
}

/// Recover from a declaration elaboration error.
///
/// Records the error in `ctx` and returns the recovery action taken.
pub(crate) fn recover_decl(
    error: ElabError,
    decl_name: &Name,
    ctx: &mut ErrorRecoveryCtx,
) -> RecoveryAction {
    let action = RecoveryAction::SkippedDeclaration;
    ctx.record_error(error, None, &format!("declaration `{decl_name}`"), action);
    action
}

// ---------------------------------------------------------------------------
// Error report formatting
// ---------------------------------------------------------------------------

/// Format all accumulated errors into a human-readable multi-error report.
///
/// The report groups errors by source span (if available) and numbers them
/// sequentially.
#[must_use]
pub(crate) fn format_error_report(errors: &[AccumulatedError]) -> String {
    if errors.is_empty() {
        return String::from("no errors");
    }

    let mut buf = String::with_capacity(errors.len() * 80);
    buf.push_str(&format!("{} error(s):\n", errors.len()));

    for (i, err) in errors.iter().enumerate() {
        buf.push_str(&format!("  {}. {}\n", i + 1, err));
    }

    buf
}
