// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended `#eval` command: profiling, type-aware display, limits, and
//! result formatting.
//!
//! Builds on [`crate::eval_cmd`] by adding:
//! - **Evaluation profiling** — wall-clock time, reduction steps, allocation count
//! - **Result formatting** — type-annotated pretty printing
//! - **Type-aware display** — Nat/String/List/Bool/Option-specific formatting
//! - **Evaluation limits** — step, time, and depth bounds with clean errors
//!
//! Caching, history, partial evaluation, and the integrated entry point are
//! in [`crate::eval_cmd_ext2`].

use std::time::Duration;

use crate::eval_cmd::{self, EvalResult};
use clean_kernel::expr::{ExprKind, Literal};
use clean_kernel::Expr;

// =============================================================================
// Error types
// =============================================================================

/// Errors specific to extended evaluation operations.
#[derive(Debug, Clone, thiserror::Error)]
#[non_exhaustive]
pub(crate) enum EvalExtError {
    /// The evaluation exceeded the configured step limit.
    #[error("step limit exceeded: {limit} steps")]
    StepLimitExceeded { limit: u64 },
    /// The evaluation exceeded the configured time limit.
    #[error("time limit exceeded: {limit:?}")]
    TimeLimitExceeded { limit: Duration },
    /// The evaluation exceeded the configured depth limit.
    #[error("depth limit exceeded: {limit} levels")]
    DepthLimitExceeded { limit: u32 },
    /// An error from the base evaluation module.
    #[error("evaluation error: {0}")]
    BaseEvalError(String),
}

// =============================================================================
// Evaluation limits
// =============================================================================

/// Configurable limits for evaluation. All limits are optional; `None` means
/// unlimited.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct EvalLimits {
    /// Maximum number of reduction steps allowed.
    pub(crate) max_steps: Option<u64>,
    /// Maximum wall-clock time allowed for a single evaluation.
    pub(crate) max_time: Option<Duration>,
    /// Maximum reduction depth (nested applications).
    pub(crate) max_depth: Option<u32>,
}

impl Default for EvalLimits {
    fn default() -> Self {
        Self {
            max_steps: Some(100_000),
            max_time: Some(Duration::from_secs(5)),
            max_depth: Some(1_000),
        }
    }
}

impl EvalLimits {
    /// Create limits with no restrictions.
    #[must_use]
    pub(crate) fn unlimited() -> Self {
        Self {
            max_steps: None,
            max_time: None,
            max_depth: None,
        }
    }

    /// Set the maximum step count.
    #[must_use]
    pub(crate) fn with_max_steps(mut self, steps: u64) -> Self {
        self.max_steps = Some(steps);
        self
    }

    /// Set the maximum evaluation time.
    #[must_use]
    pub(crate) fn with_max_time(mut self, time: Duration) -> Self {
        self.max_time = Some(time);
        self
    }

    /// Set the maximum evaluation depth.
    #[must_use]
    pub(crate) fn with_max_depth(mut self, depth: u32) -> Self {
        self.max_depth = Some(depth);
        self
    }

    /// Check whether the step count exceeds the limit.
    pub(crate) fn check_steps(&self, steps: u64) -> Result<(), EvalExtError> {
        if let Some(limit) = self.max_steps {
            if steps > limit {
                return Err(EvalExtError::StepLimitExceeded { limit });
            }
        }
        Ok(())
    }

    /// Check whether the elapsed time exceeds the limit.
    pub(crate) fn check_time(&self, elapsed: Duration) -> Result<(), EvalExtError> {
        if let Some(limit) = self.max_time {
            if elapsed > limit {
                return Err(EvalExtError::TimeLimitExceeded { limit });
            }
        }
        Ok(())
    }

    /// Check whether the depth exceeds the limit.
    pub(crate) fn check_depth(&self, depth: u32) -> Result<(), EvalExtError> {
        if let Some(limit) = self.max_depth {
            if depth > limit {
                return Err(EvalExtError::DepthLimitExceeded { limit });
            }
        }
        Ok(())
    }
}

// =============================================================================
// Evaluation profiling
// =============================================================================

/// Profiling data collected during a single evaluation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct EvalProfile {
    /// Wall-clock time spent evaluating.
    pub(crate) elapsed: Duration,
    /// Number of WHNF reduction steps performed.
    pub(crate) reduction_steps: u64,
    /// Number of allocations observed (approximate, counted via expression depth).
    pub(crate) allocation_count: u64,
    /// Whether the result was served from cache.
    pub(crate) cached: bool,
}

impl EvalProfile {
    /// Create a new profile with the given measurements.
    #[must_use]
    pub(crate) fn new(
        elapsed: Duration,
        reduction_steps: u64,
        allocation_count: u64,
        cached: bool,
    ) -> Self {
        Self {
            elapsed,
            reduction_steps,
            allocation_count,
            cached,
        }
    }

    /// Format the profile as a human-readable summary line.
    #[must_use]
    pub(crate) fn summary(&self) -> String {
        if self.cached {
            format!(
                "[cached] steps={}, allocs={}, time={:?}",
                self.reduction_steps, self.allocation_count, self.elapsed
            )
        } else {
            format!(
                "steps={}, allocs={}, time={:?}",
                self.reduction_steps, self.allocation_count, self.elapsed
            )
        }
    }
}

// =============================================================================
// Profiled evaluation result
// =============================================================================

/// Evaluation result bundled with profiling data and type information.
#[derive(Debug, Clone)]
pub(crate) struct ProfiledEvalResult {
    /// The base evaluation result.
    pub(crate) result: EvalResult,
    /// Profiling data.
    pub(crate) profile: EvalProfile,
    /// The inferred type of the expression (as a display string), if available.
    pub(crate) type_info: Option<String>,
}

impl ProfiledEvalResult {
    /// Format the result with type annotation and profile summary.
    #[must_use]
    pub(crate) fn display_with_profile(&self) -> String {
        let base = format!("{}", self.result);
        let ty = self
            .type_info
            .as_deref()
            .map(|t| format!(" : {t}"))
            .unwrap_or_default();
        format!("{base}{ty}  // {}", self.profile.summary())
    }
}

// =============================================================================
// Type-aware display
// =============================================================================

/// The detected category of a reduced expression, used to select display logic.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub(crate) enum TypeCategory {
    Nat,
    String,
    Bool,
    Unit,
    List,
    Option,
    Sort,
    Other,
}

/// Classify an expression into a [`TypeCategory`] based on its reduced form.
pub(crate) fn classify_type(expr: &Expr) -> TypeCategory {
    match expr.kind() {
        ExprKind::Lit(Literal::Nat(_)) => TypeCategory::Nat,
        ExprKind::Lit(Literal::String(_)) => TypeCategory::String,
        ExprKind::Sort(_) => TypeCategory::Sort,
        ExprKind::Const(name, _) => {
            let s = name.to_string();
            match s.as_str() {
                "Bool.true" | "Bool.false" | "True" | "False" => TypeCategory::Bool,
                "Unit.unit" | "Unit.mk" | "PUnit.unit" => TypeCategory::Unit,
                "List.nil" => TypeCategory::List,
                "Option.none" => TypeCategory::Option,
                "Nat.zero" => TypeCategory::Nat,
                _ => TypeCategory::Other,
            }
        }
        _ => {
            let head = expr.get_app_fn();
            if let ExprKind::Const(name, _) = head.kind() {
                let s = name.to_string();
                match s.as_str() {
                    "Nat.succ" => TypeCategory::Nat,
                    "List.cons" => TypeCategory::List,
                    "Option.some" => TypeCategory::Option,
                    _ => TypeCategory::Other,
                }
            } else {
                TypeCategory::Other
            }
        }
    }
}

/// Format a reduced expression with type-aware logic.
///
/// Delegates to [`eval_cmd::try_display_literal`] and
/// [`eval_cmd::try_display_constructor`] for known types, then
/// falls back to `Display` for unknown types.
#[must_use]
pub(crate) fn type_aware_display(expr: &Expr) -> String {
    let category = classify_type(expr);
    match category {
        TypeCategory::Nat
        | TypeCategory::String
        | TypeCategory::Bool
        | TypeCategory::Unit
        | TypeCategory::List
        | TypeCategory::Option => eval_cmd::try_display_literal(expr)
            .or_else(|| eval_cmd::try_display_constructor(expr))
            .unwrap_or_else(|| format!("{expr}")),
        TypeCategory::Sort | TypeCategory::Other => format!("{expr}"),
    }
}

// =============================================================================
// Result formatting utilities
// =============================================================================

/// Format an `EvalResult` with rich annotations including the type category.
#[must_use]
pub(crate) fn format_result_annotated(result: &EvalResult, type_info: Option<&str>) -> String {
    let base = format!("{result}");
    match type_info {
        Some(ty) => format!("{base} : {ty}"),
        None => base,
    }
}
