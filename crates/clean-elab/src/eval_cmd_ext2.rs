// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended `#eval` command part 2: caching, history, partial evaluation,
//! and the integrated evaluation entry point.
//!
//! Builds on [`crate::eval_cmd_ext`] (limits, profiling, type-aware display).

use std::collections::HashMap;
use std::time::Instant;

use crate::eval_cmd::{self, EvalResult};
use crate::eval_cmd_ext::{EvalExtError, EvalLimits, EvalProfile, ProfiledEvalResult};
use clean_kernel::expr::ExprKind;
use clean_kernel::name::Name;
use clean_kernel::{Environment, Expr, TypeChecker};

// =============================================================================
// Expression-based cache key
// =============================================================================

/// A lightweight fingerprint for caching evaluation results.
///
/// Uses the `Debug` representation of the expression as the key. This is
/// conservative (two structurally equal expressions produce the same key).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct ExprKey(String);

impl ExprKey {
    fn from_expr(expr: &Expr) -> Self {
        Self(format!("{expr:?}"))
    }
}

// =============================================================================
// Evaluation cache
// =============================================================================

/// Simple in-memory cache mapping expression fingerprints to evaluation results.
#[derive(Debug, Clone)]
pub(crate) struct EvalCache {
    entries: HashMap<ExprKey, CachedEntry>,
    max_entries: usize,
}

#[derive(Debug, Clone)]
struct CachedEntry {
    result: EvalResult,
    type_info: Option<String>,
}

impl Default for EvalCache {
    fn default() -> Self {
        Self::new(1024)
    }
}

impl EvalCache {
    /// Create a cache with the given capacity.
    #[must_use]
    pub(crate) fn new(max_entries: usize) -> Self {
        Self {
            entries: HashMap::new(),
            max_entries,
        }
    }

    /// Look up a cached result for `expr`.
    pub(crate) fn get(&self, expr: &Expr) -> Option<(&EvalResult, Option<&str>)> {
        let key = ExprKey::from_expr(expr);
        self.entries
            .get(&key)
            .map(|e| (&e.result, e.type_info.as_deref()))
    }

    /// Insert a result into the cache. Evicts an arbitrary entry when capacity
    /// is exceeded.
    pub(crate) fn insert(&mut self, expr: &Expr, result: EvalResult, type_info: Option<String>) {
        if self.entries.len() >= self.max_entries {
            if let Some(key) = self.entries.keys().next().cloned() {
                self.entries.remove(&key);
            }
        }
        let key = ExprKey::from_expr(expr);
        self.entries.insert(key, CachedEntry { result, type_info });
    }

    /// Number of cached entries.
    #[must_use]
    pub(crate) fn len(&self) -> usize {
        self.entries.len()
    }

    /// Whether the cache is empty.
    #[must_use]
    pub(crate) fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// Clear all cached entries.
    pub(crate) fn clear(&mut self) {
        self.entries.clear();
    }
}

// =============================================================================
// Evaluation history
// =============================================================================

/// A single entry in the evaluation history.
#[derive(Debug, Clone)]
pub(crate) struct HistoryEntry {
    /// The expression that was evaluated (display form).
    pub(crate) expr_display: String,
    /// The evaluation result.
    pub(crate) result: EvalResult,
    /// Profiling data for this evaluation.
    pub(crate) profile: EvalProfile,
    /// The inferred type, if available.
    pub(crate) type_info: Option<String>,
}

/// Maintains an ordered log of evaluations for replay and comparison.
#[derive(Debug, Clone, Default)]
pub(crate) struct EvalHistory {
    entries: Vec<HistoryEntry>,
    max_entries: usize,
}

impl EvalHistory {
    /// Create a new history with the given capacity.
    #[must_use]
    pub(crate) fn new(max_entries: usize) -> Self {
        Self {
            entries: Vec::new(),
            max_entries,
        }
    }

    /// Record an evaluation.
    pub(crate) fn record(
        &mut self,
        expr_display: String,
        result: EvalResult,
        profile: EvalProfile,
        type_info: Option<String>,
    ) {
        if self.entries.len() >= self.max_entries && self.max_entries > 0 {
            self.entries.remove(0);
        }
        self.entries.push(HistoryEntry {
            expr_display,
            result,
            profile,
            type_info,
        });
    }

    /// Return a reference to all history entries.
    #[must_use]
    pub(crate) fn entries(&self) -> &[HistoryEntry] {
        &self.entries
    }

    /// Number of recorded evaluations.
    #[must_use]
    pub(crate) fn len(&self) -> usize {
        self.entries.len()
    }

    /// Whether the history is empty.
    #[must_use]
    pub(crate) fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// Clear the history.
    pub(crate) fn clear(&mut self) {
        self.entries.clear();
    }

    /// Get the most recent entry, if any.
    #[must_use]
    pub(crate) fn last(&self) -> Option<&HistoryEntry> {
        self.entries.last()
    }

    /// Compare the last two evaluations. Returns the two entries if at least
    /// two exist.
    #[must_use]
    pub(crate) fn compare_last_two(&self) -> Option<(&HistoryEntry, &HistoryEntry)> {
        if self.entries.len() < 2 {
            return None;
        }
        let n = self.entries.len();
        Some((&self.entries[n - 2], &self.entries[n - 1]))
    }
}

// =============================================================================
// Partial evaluation
// =============================================================================

/// Marker prefix for symbolic (unknown) sub-expressions.
const SYMBOLIC_PREFIX: &str = "__symbolic_";

/// Check whether an expression is a symbolic placeholder.
#[must_use]
pub(crate) fn is_symbolic(expr: &Expr) -> bool {
    if let ExprKind::Const(name, _) = expr.kind() {
        name.to_string().starts_with(SYMBOLIC_PREFIX)
    } else {
        false
    }
}

/// Create a symbolic placeholder with the given index.
pub(crate) fn make_symbolic(index: u32) -> Expr {
    Expr::const_(
        Name::from_string(&format!("{SYMBOLIC_PREFIX}{index}")),
        vec![],
    )
}

/// Attempt partial evaluation: reduce what can be reduced, leaving symbolic
/// sub-expressions in place. Returns the partially reduced expression as a
/// display string and the count of symbolic sub-expressions encountered.
pub(crate) fn partial_eval(expr: &Expr, env: &Environment) -> (String, u32) {
    let tc = TypeChecker::new(env);
    let mut symbolic_count = 0u32;
    let display = partial_eval_inner(expr, &tc, &mut symbolic_count, 0);
    (display, symbolic_count)
}

fn partial_eval_inner(
    expr: &Expr,
    tc: &TypeChecker<'_>,
    symbolic_count: &mut u32,
    depth: u32,
) -> String {
    if depth > 200 {
        return format!("{expr}");
    }
    if is_symbolic(expr) {
        *symbolic_count += 1;
        return format!("{expr}");
    }
    let reduced = tc.whnf(expr);
    if let Some(display) = eval_cmd::try_display_literal(&reduced) {
        return display;
    }
    if let Some(display) = eval_cmd::try_display_constructor(&reduced) {
        return display;
    }
    let head = reduced.get_app_fn();
    let args = reduced.get_app_args();
    if !args.is_empty() {
        let head_str = partial_eval_inner(head, tc, symbolic_count, depth + 1);
        let arg_strs: Vec<String> = args
            .iter()
            .map(|a| partial_eval_inner(a, tc, symbolic_count, depth + 1))
            .collect();
        return format!("({} {})", head_str, arg_strs.join(" "));
    }
    format!("{reduced}")
}

// =============================================================================
// Expression sub-expression counting
// =============================================================================

/// Count the approximate number of sub-expressions (proxy for allocation count).
pub(crate) fn count_sub_exprs(expr: &Expr) -> u64 {
    count_sub_exprs_inner(expr, 0)
}

fn count_sub_exprs_inner(expr: &Expr, depth: u32) -> u64 {
    if depth > 200 {
        return 1;
    }
    match expr.kind() {
        ExprKind::App(f, a) => {
            1 + count_sub_exprs_inner(f, depth + 1) + count_sub_exprs_inner(a, depth + 1)
        }
        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
            1 + count_sub_exprs_inner(ty, depth + 1) + count_sub_exprs_inner(body, depth + 1)
        }
        ExprKind::Let(_, ty, val, body, _) => {
            1 + count_sub_exprs_inner(ty, depth + 1)
                + count_sub_exprs_inner(val, depth + 1)
                + count_sub_exprs_inner(body, depth + 1)
        }
        _ => 1,
    }
}

// =============================================================================
// Extended evaluation entry point
// =============================================================================

/// Evaluate an expression with profiling, caching, and limit enforcement.
///
/// 1. Checks the cache for a previous result
/// 2. Enforces configured limits
/// 3. Delegates to [`eval_cmd::eval_expression`]
/// 4. Profiles the evaluation and records it in history
///
/// # Errors
///
/// Returns [`EvalExtError`] if any limit is exceeded or the base evaluator
/// fails.
pub(crate) fn eval_expression_ext(
    expr: &Expr,
    env: &Environment,
    limits: &EvalLimits,
    cache: &mut EvalCache,
    history: &mut EvalHistory,
) -> Result<ProfiledEvalResult, EvalExtError> {
    let start = Instant::now();

    // Check cache first.
    if let Some((cached_result, cached_type)) = cache.get(expr) {
        let profile = EvalProfile::new(start.elapsed(), 0, 0, true);
        let profiled = ProfiledEvalResult {
            result: cached_result.clone(),
            profile: profile.clone(),
            type_info: cached_type.map(str::to_owned),
        };
        history.record(
            format!("{expr}"),
            cached_result.clone(),
            profile,
            cached_type.map(str::to_owned),
        );
        return Ok(profiled);
    }

    // Pre-flight depth check.
    let expr_depth = approximate_depth(expr, 0);
    limits.check_depth(expr_depth)?;

    // Step check based on sub-expression count.
    let sub_expr_count = count_sub_exprs(expr);
    limits.check_steps(sub_expr_count)?;

    // Evaluate.
    let result = eval_cmd::eval_expression(expr, env)
        .map_err(|e| EvalExtError::BaseEvalError(e.to_string()))?;

    let elapsed = start.elapsed();
    limits.check_time(elapsed)?;

    let type_info = infer_type_display(expr, env);
    let profile = EvalProfile::new(elapsed, sub_expr_count, sub_expr_count, false);

    cache.insert(expr, result.clone(), type_info.clone());
    history.record(
        format!("{expr}"),
        result.clone(),
        profile.clone(),
        type_info.clone(),
    );

    Ok(ProfiledEvalResult {
        result,
        profile,
        type_info,
    })
}

/// Approximate the depth of an expression tree.
fn approximate_depth(expr: &Expr, current: u32) -> u32 {
    if current > 200 {
        return current;
    }
    match expr.kind() {
        ExprKind::App(f, a) => {
            approximate_depth(f, current + 1).max(approximate_depth(a, current + 1))
        }
        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
            approximate_depth(ty, current + 1).max(approximate_depth(body, current + 1))
        }
        ExprKind::Let(_, ty, val, body, _) => approximate_depth(ty, current + 1)
            .max(approximate_depth(val, current + 1))
            .max(approximate_depth(body, current + 1)),
        _ => current,
    }
}

/// Try to infer the type of an expression and return its display string.
fn infer_type_display(expr: &Expr, env: &Environment) -> Option<String> {
    let tc = TypeChecker::new(env);
    tc.infer_type(expr).ok().map(|ty| format!("{ty}"))
}

// =============================================================================
// History formatting
// =============================================================================

/// Format the evaluation history as a multi-line summary suitable for display.
#[must_use]
pub(crate) fn format_history(history: &EvalHistory) -> String {
    if history.is_empty() {
        return "(no evaluations recorded)".to_owned();
    }
    history
        .entries()
        .iter()
        .enumerate()
        .map(|(i, entry)| {
            let ty = entry
                .type_info
                .as_deref()
                .map(|t| format!(" : {t}"))
                .unwrap_or_default();
            format!(
                "[{}] {} => {}{ty}  // {}",
                i,
                entry.expr_display,
                entry.result,
                entry.profile.summary()
            )
        })
        .collect::<Vec<_>>()
        .join("\n")
}
