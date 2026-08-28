// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Value types for elaboration error recovery.
//!
//! Split out of `error_recovery_ext.rs`: the plain data half — recovery
//! strategies, severities, located diagnostics, the recovery config builder,
//! the collected summary, and the per-attempt result. `error_recovery_ext.rs`
//! keeps `RecoveryContext` and the recovery driver that consume them, and
//! re-exports every name here so existing `crate::error_recovery_ext::…`
//! paths are unchanged.

use std::fmt;

use clean_kernel::Expr;

use crate::error::ElabError;

const DEFAULT_MAX_ERRORS: usize = 50;
const DEFAULT_RECOVERY_DEPTH_LIMIT: usize = 10;
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub(crate) enum RecoveryStrategy {
    InsertSorry,
    UseExpectedType,
    SkipToken,
    InsertPlaceholder,
    BestEffort,
}

impl fmt::Display for RecoveryStrategy {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let label = match self {
            Self::InsertSorry => "insert sorry",
            Self::UseExpectedType => "use expected type",
            Self::SkipToken => "skip token",
            Self::InsertPlaceholder => "insert placeholder",
            Self::BestEffort => "best effort",
        };
        f.write_str(label)
    }
}
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub(crate) enum ErrorSeverity {
    Error,
    Warning,
    Info,
    Hint,
}

impl fmt::Display for ErrorSeverity {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let label = match self {
            Self::Error => "error",
            Self::Warning => "warning",
            Self::Info => "info",
            Self::Hint => "hint",
        };
        f.write_str(label)
    }
}
#[derive(Debug, Clone)]
pub(crate) struct LocatedError {
    pub(crate) error: ElabError,
    pub(crate) span: Option<(usize, usize)>,
    pub(crate) context: String,
    pub(crate) severity: ErrorSeverity,
}

impl fmt::Display for LocatedError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}: ", self.severity)?;
        if let Some((start, end)) = self.span {
            write!(f, "[{start}..{end}] ")?;
        }
        if !self.context.is_empty() {
            write!(f, "({}) ", self.context)?;
        }
        write!(f, "{}", self.error)
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct LocatedWarning {
    pub(crate) message: String,
    pub(crate) span: Option<(usize, usize)>,
}

impl fmt::Display for LocatedWarning {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("warning")?;
        if let Some((start, end)) = self.span {
            write!(f, " [{start}..{end}]")?;
        }
        write!(f, ": {}", self.message)
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct RecoveryConfig {
    pub(crate) max_errors: usize,
    pub(crate) strategies: Vec<RecoveryStrategy>,
    pub(crate) report_all: bool,
    pub(crate) recovery_depth_limit: usize,
}

impl Default for RecoveryConfig {
    fn default() -> Self {
        Self {
            max_errors: DEFAULT_MAX_ERRORS,
            strategies: vec![
                RecoveryStrategy::UseExpectedType,
                RecoveryStrategy::InsertSorry,
                RecoveryStrategy::SkipToken,
                RecoveryStrategy::InsertPlaceholder,
                RecoveryStrategy::BestEffort,
            ],
            report_all: false,
            recovery_depth_limit: DEFAULT_RECOVERY_DEPTH_LIMIT,
        }
    }
}

impl RecoveryConfig {
    #[must_use]
    pub(crate) fn new() -> Self {
        Self::default()
    }

    #[must_use]
    pub(crate) fn with_max_errors(mut self, max_errors: usize) -> Self {
        self.max_errors = max_errors;
        self
    }

    #[must_use]
    pub(crate) fn with_strategies(mut self, strategies: Vec<RecoveryStrategy>) -> Self {
        self.strategies = strategies;
        self
    }

    #[must_use]
    pub(crate) fn with_report_all(mut self, report_all: bool) -> Self {
        self.report_all = report_all;
        self
    }

    #[must_use]
    pub(crate) fn with_recovery_depth_limit(mut self, limit: usize) -> Self {
        self.recovery_depth_limit = limit;
        self
    }
}

#[derive(Debug, Clone, Default)]
pub(crate) struct ErrorSummary {
    pub(crate) errors: Vec<LocatedError>,
    pub(crate) warnings: Vec<LocatedWarning>,
    pub(crate) sorry_count: usize,
    pub(crate) recovered_count: usize,
}

#[derive(Debug, Clone)]
#[non_exhaustive]
pub(crate) enum RecoveryResult {
    Recovered {
        synth_term: Expr,
        strategy_used: RecoveryStrategy,
    },
    // Staged Lean4-parity scaffold with no caller yet (tests included): kept per the
    // keep-and-annotate doctrine — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
    #[allow(dead_code)]
    Fatal(ElabError),
    TooManyErrors,
}
