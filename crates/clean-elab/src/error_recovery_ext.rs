// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use std::fmt;

use clean_kernel::sorry::create_sorry_term;
use clean_kernel::{Environment, Expr};

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

#[derive(Debug, Clone)]
pub(crate) struct RecoveryContext {
    pub(crate) errors: Vec<LocatedError>,
    pub(crate) checkpoints: Vec<usize>,
    pub(crate) sorry_terms: Vec<Expr>,
    pub(crate) config: RecoveryConfig,
    pub(crate) current_depth: usize,
    warnings: Vec<LocatedWarning>,
    recovered_count: usize,
    pending_recovery_term: Option<Expr>,
    pending_is_sorry: bool,
    warning_checkpoints: Vec<usize>,
    sorry_checkpoints: Vec<usize>,
}

impl RecoveryContext {
    #[must_use]
    pub(crate) fn new(config: RecoveryConfig) -> Self {
        Self {
            errors: Vec::new(),
            checkpoints: Vec::new(),
            sorry_terms: Vec::new(),
            config,
            current_depth: 0,
            warnings: Vec::new(),
            recovered_count: 0,
            pending_recovery_term: None,
            pending_is_sorry: false,
            warning_checkpoints: Vec::new(),
            sorry_checkpoints: Vec::new(),
        }
    }

    pub(crate) fn push_checkpoint(&mut self) {
        self.checkpoints.push(self.errors.len());
        self.warning_checkpoints.push(self.warnings.len());
        self.sorry_checkpoints.push(self.sorry_terms.len());
    }

    pub(crate) fn pop_checkpoint(&mut self) -> bool {
        let Some(error_len) = self.checkpoints.pop() else {
            return false;
        };
        let warning_len = self
            .warning_checkpoints
            .pop()
            .unwrap_or(self.warnings.len());
        let sorry_len = self
            .sorry_checkpoints
            .pop()
            .unwrap_or(self.sorry_terms.len());
        self.errors.truncate(error_len);
        self.warnings.truncate(warning_len);
        self.sorry_terms.truncate(sorry_len);
        self.pending_recovery_term = None;
        self.pending_is_sorry = false;
        true
    }

    pub(crate) fn commit_checkpoint(&mut self) -> bool {
        let committed = self.checkpoints.pop().is_some();
        if committed {
            let _ = self.warning_checkpoints.pop();
            let _ = self.sorry_checkpoints.pop();
        }
        committed
    }

    pub(crate) fn record_error(
        &mut self,
        error: ElabError,
        span: Option<(usize, usize)>,
        context: &str,
        severity: ErrorSeverity,
    ) {
        self.errors.push(LocatedError {
            error,
            span,
            context: context.to_owned(),
            severity,
        });
    }

    pub(crate) fn recover_with(
        &mut self,
        strategy: RecoveryStrategy,
        err: ElabError,
    ) -> RecoveryResult {
        if self.errors.len() >= self.config.max_errors {
            self.pending_recovery_term = None;
            self.pending_is_sorry = false;
            return RecoveryResult::TooManyErrors;
        }

        if self.current_depth > self.config.recovery_depth_limit {
            self.record_error(
                err.clone(),
                None,
                "recovery depth limit exceeded",
                ErrorSeverity::Error,
            );
            self.pending_recovery_term = None;
            self.pending_is_sorry = false;
            return RecoveryResult::Fatal(err);
        }

        let synth_term = match self.pending_recovery_term.take() {
            Some(term) => term,
            None => match strategy {
                RecoveryStrategy::SkipToken => Expr::prop(),
                RecoveryStrategy::InsertPlaceholder => Expr::type_(),
                RecoveryStrategy::BestEffort => Expr::prop(),
                RecoveryStrategy::InsertSorry | RecoveryStrategy::UseExpectedType => {
                    self.record_error(
                        err.clone(),
                        None,
                        "recovery strategy could not synthesize a term",
                        ErrorSeverity::Error,
                    );
                    self.pending_is_sorry = false;
                    return RecoveryResult::Fatal(err);
                }
            },
        };

        self.record_error(
            err,
            None,
            &format!("recovered with {strategy}"),
            ErrorSeverity::Error,
        );
        if self.pending_is_sorry {
            self.sorry_terms.push(synth_term.clone());
        }
        self.pending_is_sorry = false;
        self.recovered_count += 1;

        RecoveryResult::Recovered {
            synth_term,
            strategy_used: strategy,
        }
    }

    #[must_use]
    pub(crate) fn into_summary(self) -> ErrorSummary {
        ErrorSummary {
            errors: self.errors,
            warnings: self.warnings,
            sorry_count: self.sorry_terms.len(),
            recovered_count: self.recovered_count,
        }
    }

    fn prepare_strategy_term(
        &mut self,
        strategy: RecoveryStrategy,
        env: &Environment,
        expected_type: Option<&Expr>,
    ) {
        let prepared = match strategy {
            RecoveryStrategy::InsertSorry | RecoveryStrategy::UseExpectedType => {
                expected_type.map(|ty| (synthesize_sorry(env, ty), true))
            }
            RecoveryStrategy::SkipToken => Some(match expected_type {
                Some(ty) => (synthesize_sorry(env, ty), true),
                None => (Expr::prop(), false),
            }),
            RecoveryStrategy::InsertPlaceholder => Some((Expr::prop(), false)),
            RecoveryStrategy::BestEffort => Some(match expected_type {
                Some(ty) => (synthesize_sorry(env, ty), true),
                None => (Expr::prop(), false),
            }),
        };

        match prepared {
            Some((term, is_sorry)) => {
                self.pending_recovery_term = Some(term);
                self.pending_is_sorry = is_sorry;
            }
            None => {
                self.pending_recovery_term = None;
                self.pending_is_sorry = false;
            }
        }
    }

    fn rollback_attempt(&mut self, error_len: usize, warning_len: usize, sorry_len: usize) {
        self.errors.truncate(error_len);
        self.warnings.truncate(warning_len);
        self.sorry_terms.truncate(sorry_len);
        self.pending_recovery_term = None;
        self.pending_is_sorry = false;
    }

    fn errors_since(&self, checkpoint: usize) -> Vec<LocatedError> {
        let slice = &self.errors[checkpoint.min(self.errors.len())..];
        if self.config.report_all {
            return slice.to_vec();
        }
        slice.last().cloned().into_iter().collect()
    }
}

pub(crate) fn try_elaborate_with_recovery(
    ctx: &mut RecoveryContext,
    env: &Environment,
    f: impl FnOnce() -> Result<Expr, ElabError>,
    expected_type: Option<&Expr>,
) -> (Option<Expr>, Vec<LocatedError>) {
    let base_error_len = ctx.errors.len();

    ctx.push_checkpoint();
    match f() {
        Ok(expr) => {
            let _ = ctx.commit_checkpoint();
            (Some(expr), Vec::new())
        }
        Err(err) => {
            let _ = ctx.commit_checkpoint();

            if ctx.current_depth >= ctx.config.recovery_depth_limit {
                ctx.record_error(
                    err,
                    None,
                    "recovery depth limit reached",
                    ErrorSeverity::Error,
                );
                return (None, ctx.errors_since(base_error_len));
            }

            ctx.current_depth += 1;
            let mut recovered = None;

            for strategy in ctx.config.strategies.clone() {
                let attempt_error_len = ctx.errors.len();
                let attempt_warning_len = ctx.warnings.len();
                let attempt_sorry_len = ctx.sorry_terms.len();

                ctx.prepare_strategy_term(strategy, env, expected_type);
                match ctx.recover_with(strategy, err.clone()) {
                    RecoveryResult::Recovered {
                        synth_term,
                        strategy_used: _,
                    } => {
                        recovered = Some(synth_term);
                        break;
                    }
                    RecoveryResult::Fatal(_) => {
                        if !ctx.config.report_all {
                            ctx.rollback_attempt(
                                attempt_error_len,
                                attempt_warning_len,
                                attempt_sorry_len,
                            );
                        }
                    }
                    RecoveryResult::TooManyErrors => {
                        if !ctx.config.report_all {
                            ctx.rollback_attempt(
                                attempt_error_len,
                                attempt_warning_len,
                                attempt_sorry_len,
                            );
                        }
                        ctx.current_depth = ctx.current_depth.saturating_sub(1);
                        return (None, ctx.errors_since(base_error_len));
                    }
                }
            }

            ctx.current_depth = ctx.current_depth.saturating_sub(1);

            if recovered.is_none() && ctx.errors.len() == base_error_len {
                ctx.record_error(
                    err,
                    None,
                    "recovery exhausted without a viable strategy",
                    ErrorSeverity::Error,
                );
            }

            (recovered, ctx.errors_since(base_error_len))
        }
    }
}

pub(crate) fn synthesize_sorry(env: &Environment, expected_type: &Expr) -> Expr {
    create_sorry_term(env, expected_type)
}

#[must_use]
pub(crate) fn merge_error_summaries(summaries: &[ErrorSummary]) -> ErrorSummary {
    let mut merged = ErrorSummary::default();

    for summary in summaries {
        merged.errors.extend(summary.errors.iter().cloned());
        merged.warnings.extend(summary.warnings.iter().cloned());
        merged.sorry_count += summary.sorry_count;
        merged.recovered_count += summary.recovered_count;
    }

    merged
}

#[must_use]
pub(crate) fn format_error_report(summary: &ErrorSummary) -> String {
    if summary.errors.is_empty() && summary.warnings.is_empty() {
        return String::from("no diagnostics");
    }

    let mut out = String::new();
    out.push_str(&format!(
        "{} error(s), {} warning(s), {} sorry term(s), {} recovered\n",
        summary.errors.len(),
        summary.warnings.len(),
        summary.sorry_count,
        summary.recovered_count
    ));

    if !summary.errors.is_empty() {
        out.push_str("Errors:\n");
        for (idx, error) in summary.errors.iter().enumerate() {
            out.push_str(&format!("  {}. {}\n", idx + 1, error));
        }
    }

    if !summary.warnings.is_empty() {
        out.push_str("Warnings:\n");
        for (idx, warning) in summary.warnings.iter().enumerate() {
            out.push_str(&format!("  {}. {}\n", idx + 1, warning));
        }
    }

    out
}
