// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Positivity tactics
//!
//! Provides tactics for analyzing expressions to determine if they are positive,
//! non-negative, or nonzero.

use clean_kernel::expr::ExprKind;
use clean_kernel::Expr;

use super::arithmetic::expr_is_nat_lit;
use super::tc_app;
use super::{have_, ProofState, TacticError, TacticResult};
use crate::stack_safe;

/// Tactic: positivity_at
///
/// Analyzes a hypothesis to add information about whether expressions are positive,
/// non-negative, or nonzero using positivity analysis.
///
/// This is useful when you need to establish positivity facts about
/// values in hypotheses for use in subsequent reasoning.
///
/// # Example
/// ```text
/// -- h : x^2 + 1 > y
/// positivity_at h
/// -- First prove h_pos : x^2 + 1 > 0; the continuation receives h_pos
/// ```
///
/// REQUIRES: `state.goals` is non-empty.
/// REQUIRES: `hyp_name` identifies a hypothesis in the current goal's local context.
/// ENSURES: On `Ok(())`, the original goal is replaced by two goals: first a
///   proof obligation establishing positivity/non-negativity of the comparison
///   LHS in the original context, then the original target with that proved fact
///   available as `{hyp_name}_pos`.
/// ENSURES: No positivity proof is assumed or fabricated.
/// ENSURES: Returns `Err(NoGoals)` when no goals remain; `Err(HypothesisNotFound)`
///   when the named hypothesis does not exist.
pub fn positivity_at(state: &mut ProofState, hyp_name: &str) -> TacticResult {
    positivity_at_with_config(state, hyp_name, PositivityAtConfig::new())
}

/// Configuration for positivity_at
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct PositivityAtConfig {
    /// Name for the generated positivity hypothesis
    pub result_name: Option<String>,
    /// Whether to try stronger claims (positive vs non-negative)
    pub try_stronger: bool,
}

impl Default for PositivityAtConfig {
    fn default() -> Self {
        PositivityAtConfig {
            result_name: None,
            try_stronger: true,
        }
    }
}

impl PositivityAtConfig {
    pub fn new() -> Self {
        Self::default()
    }

    #[must_use]
    pub fn with_name(mut self, name: &str) -> Self {
        self.result_name = Some(name.to_string());
        self
    }
}

/// positivity_at with configuration
///
/// REQUIRES: `state.goals` is non-empty.
/// REQUIRES: `hyp_name` identifies a hypothesis whose type is a recognized comparison.
/// ENSURES: On `Ok(())`, the original goal is replaced by two goals: first a
///   proof obligation for the inferred positivity/non-negativity fact in the
///   original context, then the original target with that proved fact available
///   under `config.result_name` or `{hyp_name}_pos`.
/// ENSURES: No positivity proof is assumed or fabricated.
pub fn positivity_at_with_config(
    state: &mut ProofState,
    hyp_name: &str,
    config: PositivityAtConfig,
) -> TacticResult {
    if state.goals.is_empty() {
        return Err(TacticError::NoGoals);
    }

    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();

    // Find the hypothesis
    let hyp = goal
        .local_ctx
        .iter()
        .find(|d| d.name == hyp_name)
        .ok_or_else(|| TacticError::HypothesisNotFound(hyp_name.to_string()))?;

    let hyp_ty = hyp.ty.clone();

    // Extract the expression to analyze for positivity
    // We look for patterns like: x > y, x ≥ y, x = y, etc.
    let (expr_to_analyze, comparison_kind) = extract_comparison_expr(&hyp_ty)?;

    // Perform positivity analysis on the expression
    let positivity_result = analyze_positivity(&expr_to_analyze)?;

    // Generate the result name
    let result_name = config
        .result_name
        .unwrap_or_else(|| format!("{hyp_name}_pos"));

    // Create the positivity proposition based on analysis
    let pos_prop = make_positivity_prop(&expr_to_analyze, positivity_result, config.try_stronger);

    // Introduce the result through a proof-carrying continuation.  The first
    // generated goal proves `pos_prop` in the original context; only the
    // continuation may use the corresponding local declaration.
    have_(state, &result_name, pos_prop, None)?;

    let _ = comparison_kind; // Mark as used
    Ok(())
}

/// Kind of comparison in an expression
#[derive(Debug, Clone, Copy)]
pub(crate) enum ComparisonKind {
    Gt, // >
    Ge, // ≥
    Lt, // <
    Le, // ≤
    Eq, // =
    Ne, // ≠
}

/// Extract the main expression from a comparison
///
/// REQUIRES: `ty` is a well-formed expression tree.
/// ENSURES: Returns `Ok((lhs, kind))` only when `ty` is a fully-applied comparison
///   (GT.gt, GE.ge, LT.lt, LE.le, Eq, Ne) — `lhs` is a clone of the left operand.
/// ENSURES: Returns `Err(GoalMismatch)` for non-comparison expressions.
pub(crate) fn extract_comparison_expr(ty: &Expr) -> Result<(Expr, ComparisonKind), TacticError> {
    // Look for patterns like GT.gt x y, GE.ge x y, etc.
    let args = ty.get_app_args();
    if args.len() >= 2 {
        if let ExprKind::Const(name, _) = ty.get_app_fn().kind() {
            let kind = match name.to_string().as_str() {
                "GT.gt" | "gt" => Some(ComparisonKind::Gt),
                "GE.ge" | "ge" => Some(ComparisonKind::Ge),
                "LT.lt" | "lt" => Some(ComparisonKind::Lt),
                "LE.le" | "le" => Some(ComparisonKind::Le),
                "Eq" | "eq" => Some(ComparisonKind::Eq),
                "Ne" | "ne" => Some(ComparisonKind::Ne),
                _ => None,
            };
            if let Some(k) = kind {
                return Ok((args[args.len() - 2].clone(), k));
            }
        }
    }

    match ty.kind() {
        ExprKind::App(_, _) => Err(TacticError::GoalMismatch(
            "positivity_at: could not extract comparison from hypothesis".to_string(),
        )),
        _ => Err(TacticError::GoalMismatch(
            "positivity_at: hypothesis is not a comparison".to_string(),
        )),
    }
}

/// Result of positivity analysis
#[derive(Debug, Clone, Copy)]
pub(crate) enum PositivityResult {
    /// Definitely positive (> 0)
    Positive,
    /// Definitely non-negative (≥ 0)
    NonNegative,
    /// Unknown
    Unknown,
}

/// Analyze an expression for positivity
///
/// REQUIRES: `expr` is a well-formed expression tree.
/// ENSURES: Returns `Positive` for expressions structurally known > 0 (e.g., literal 1,
///   sum/product with a positive sub-expression).
/// ENSURES: Returns `NonNegative` for expressions structurally known ≥ 0 (e.g., squares,
///   absolute values, natural number literals, sums of non-negatives).
/// ENSURES: Returns `Unknown` when no structural positivity can be determined.
pub(crate) fn analyze_positivity(expr: &Expr) -> Result<PositivityResult, TacticError> {
    // Simple pattern matching for common cases
    stack_safe(|| match expr.kind() {
        // Constants
        ExprKind::Const(name, _) => {
            let s = name.to_string();
            if s.ends_with(".one") || s == "1" {
                return Ok(PositivityResult::Positive);
            }
            if s.ends_with(".zero") || s == "0" {
                return Ok(PositivityResult::NonNegative);
            }
            Ok(PositivityResult::Unknown)
        }

        // Literal natural numbers are non-negative
        ExprKind::Lit(clean_kernel::Literal::Nat(_)) => Ok(PositivityResult::NonNegative),

        // Application patterns
        ExprKind::App(f, arg) => {
            // Check for squared terms: x^2, x * x
            // A square of a positive is positive; otherwise non-negative.
            if let Some(base) = get_square_base(expr) {
                let base_pos = analyze_positivity(&base)?;
                return Ok(if matches!(base_pos, PositivityResult::Positive) {
                    PositivityResult::Positive
                } else {
                    PositivityResult::NonNegative
                });
            }

            // Check for absolute value
            if is_abs_pattern(expr) {
                return Ok(PositivityResult::NonNegative);
            }

            // Check for sum of non-negatives
            if let Some((a, b)) = is_add_pattern(expr) {
                let a_pos = analyze_positivity(&a)?;
                let b_pos = analyze_positivity(&b)?;
                match (a_pos, b_pos) {
                    (PositivityResult::Positive, PositivityResult::Positive)
                    | (PositivityResult::Positive, PositivityResult::NonNegative)
                    | (PositivityResult::NonNegative, PositivityResult::Positive) => {
                        return Ok(PositivityResult::Positive);
                    }
                    (PositivityResult::NonNegative, PositivityResult::NonNegative) => {
                        return Ok(PositivityResult::NonNegative);
                    }
                    _ => {}
                }
            }

            // Check for product of positives/non-negatives
            if let Some((a, b)) = is_mul_pattern(expr) {
                let a_pos = analyze_positivity(&a)?;
                let b_pos = analyze_positivity(&b)?;
                match (a_pos, b_pos) {
                    (PositivityResult::Positive, PositivityResult::Positive) => {
                        return Ok(PositivityResult::Positive);
                    }
                    (PositivityResult::Positive, PositivityResult::NonNegative)
                    | (PositivityResult::NonNegative, PositivityResult::Positive)
                    | (PositivityResult::NonNegative, PositivityResult::NonNegative) => {
                        return Ok(PositivityResult::NonNegative);
                    }
                    _ => {}
                }
            }

            let _ = (f, arg); // Mark as used
            Ok(PositivityResult::Unknown)
        }

        _ => Ok(PositivityResult::Unknown),
    })
}

/// Extract the base of a square pattern (x^2 or x*x)
///
/// REQUIRES: `expr` is a well-formed expression tree.
/// ENSURES: Returns `Some(base)` only for `pow` applications with exponent `2`
///   or multiplication spines whose final explicit operands are syntactically equal.
pub(crate) fn get_square_base(expr: &Expr) -> Option<Expr> {
    match expr.kind() {
        ExprKind::App(_, _) => {
            let args = expr.get_app_args();
            if args.len() < 2 {
                return None;
            }

            if let ExprKind::Const(name, _) = expr.get_app_fn().kind() {
                let s = name.to_string();
                let lhs = args[args.len() - 2];
                let rhs = args[args.len() - 1];

                if (s.contains("HPow") || s.contains("pow")) && expr_is_nat_lit(rhs, 2) {
                    return Some(lhs.clone());
                }
                if (s.contains("HMul") || s.contains("mul")) && lhs == rhs {
                    return Some(lhs.clone());
                }
            }
            None
        }
        _ => None,
    }
}

/// Check if expression is an absolute value pattern
///
/// REQUIRES: `expr` is a well-formed expression tree.
/// ENSURES: Returns `true` only when the head constant name contains "abs" or "Abs".
pub(crate) fn is_abs_pattern(expr: &Expr) -> bool {
    match expr.kind() {
        ExprKind::App(_, _) => {
            if let ExprKind::Const(name, _) = expr.get_app_fn().kind() {
                let s = name.to_string();
                return s.contains("abs") || s.contains("Abs");
            }
            false
        }
        _ => false,
    }
}

/// Check if expression is an addition pattern
///
/// REQUIRES: `expr` is a well-formed expression tree.
/// ENSURES: Returns `Some((a, b))` only for fully-applied HAdd/Add.add spines.
/// ENSURES: Returned expressions are clones of the matched operands.
pub(crate) fn is_add_pattern(expr: &Expr) -> Option<(Expr, Expr)> {
    match expr.kind() {
        ExprKind::App(_, _) => {
            let args = expr.get_app_args();
            if args.len() < 2 {
                return None;
            }
            let is_add = match expr.get_app_fn().kind() {
                ExprKind::Const(name, _) => {
                    let s = name.to_string();
                    s.contains("HAdd") || s.contains("Add.add") || s.contains("add")
                }
                _ => false,
            };
            if is_add {
                return Some((args[args.len() - 2].clone(), args[args.len() - 1].clone()));
            }
            None
        }
        _ => None,
    }
}

/// Check if expression is a multiplication pattern
///
/// REQUIRES: `expr` is a well-formed expression tree.
/// ENSURES: Returns `Some((a, b))` only for fully-applied HMul/Mul.mul spines.
/// ENSURES: Returned expressions are clones of the matched operands.
pub(crate) fn is_mul_pattern(expr: &Expr) -> Option<(Expr, Expr)> {
    match expr.kind() {
        ExprKind::App(_, _) => {
            let args = expr.get_app_args();
            if args.len() < 2 {
                return None;
            }
            let is_mul = match expr.get_app_fn().kind() {
                ExprKind::Const(name, _) => {
                    let s = name.to_string();
                    s.contains("HMul") || s.contains("Mul.mul") || s.contains("mul")
                }
                _ => false,
            };
            if is_mul {
                return Some((args[args.len() - 2].clone(), args[args.len() - 1].clone()));
            }
            None
        }
        _ => None,
    }
}

/// Make a positivity proposition from analysis result.
///
/// Builds `@Rel.{u} ty inst expr zero` — the fully-applied form.
/// Part of #2078: previously only produced `Rel expr zero` (missing type + instance).
///
/// REQUIRES: `expr` is a well-formed expression; `result` is a valid positivity classification.
/// ENSURES: Returns a fully-applied comparison proposition: `GT.gt Nat inst expr 0`
///   for `Positive` (when `try_stronger`), `GE.ge Nat inst expr 0` otherwise.
/// ENSURES: Type and instance arguments are always present (no missing implicit args).
pub(crate) fn make_positivity_prop(
    expr: &Expr,
    result: PositivityResult,
    try_stronger: bool,
) -> Expr {
    let zero = Expr::nat_lit(0);

    match result {
        PositivityResult::Positive if try_stronger => {
            // expr > 0: GT.gt uses LT instance.  The Nat wrapper fixes the
            // relation universe at zero rather than minting an unsolved level.
            tc_app::nat_gt_tc(expr.clone(), zero)
        }
        PositivityResult::NonNegative | PositivityResult::Positive => {
            // expr ≥ 0: GE.ge uses LE instance
            tc_app::nat_ge_tc(expr.clone(), zero)
        }
        PositivityResult::Unknown => {
            // Default to ≥ 0 as a guess
            tc_app::nat_ge_tc(expr.clone(), zero)
        }
    }
}
