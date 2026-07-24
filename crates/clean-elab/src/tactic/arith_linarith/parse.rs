// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Linear constraint extraction and expression parsing.
//!
//! Extracts linear constraints from proof state hypotheses and goals,
//! and parses kernel expressions into linear arithmetic representations.

use clean_kernel::{Expr, ExprKind, FVarId};

use super::super::arithmetic::{big_nat_to_i64, LinearConstraint, LinearExpr};
use super::super::{match_equality, Goal, ProofState};
use super::certificate::CertifiedConstraint;
use crate::stack_safe;

/// Result type for extracted certified linear constraints.
pub(crate) type ExtractedConstraints = (
    Vec<CertifiedConstraint>,
    std::collections::HashMap<FVarId, usize>,
    Vec<FVarId>,
);

/// Extract certified linear constraints from the proof state.
///
/// Returns the constraints, variable mapping, and the original hypothesis FVarIds.
///
/// REQUIRES: `state` is a valid `ProofState`
/// REQUIRES: `goal` is a valid goal from `state`
/// ENSURES: On `Some(...)`, at least one constraint was extracted
/// ENSURES: Each `CertifiedConstraint` has a certificate with correct dimension
/// ENSURES: `hypothesis_fvars` maps 1:1 to parseable hypotheses in `goal.local_ctx`
/// ENSURES: On `None`, no hypotheses or goal could be parsed as linear constraints
pub(crate) fn extract_certified_linear_constraints(
    state: &ProofState,
    goal: &Goal,
) -> Option<ExtractedConstraints> {
    let mut var_map: std::collections::HashMap<FVarId, usize> = std::collections::HashMap::new();
    let mut next_var = 0;
    let mut hypothesis_fvars: Vec<FVarId> = Vec::new();
    let whnf_fn: &dyn Fn(&Expr) -> Expr = &|e| state.whnf(goal, e);

    // First pass: extract raw constraints and hypothesis fvars to determine dimension
    let mut raw_constraints: Vec<(LinearConstraint, usize)> = Vec::new();
    for decl in &goal.local_ctx {
        let ty = state.metas.instantiate(&decl.ty);
        // Try parsing the raw expression first; fall back to WHNF if needed (#685).
        // WHNF can over-reduce structure projections (e.g. LE.le → Nat.le), changing
        // arity, so we only use it when the normal parse fails.
        let constraint =
            parse_linear_constraint(&ty, &mut var_map, &mut next_var, None).or_else(|| {
                let ty_whnf = state.whnf(goal, &decl.ty);
                parse_linear_constraint(&ty_whnf, &mut var_map, &mut next_var, Some(whnf_fn))
            });
        if let Some(c) = constraint {
            let hyp_index = hypothesis_fvars.len();
            hypothesis_fvars.push(decl.fvar);
            raw_constraints.push((c, hyp_index));
        }
    }

    let num_hyps = hypothesis_fvars.len();
    // Certificate dimension: one slot per parseable hypothesis + one for negated goal
    let total_count = num_hyps + 1;

    // Second pass: create certified constraints with uniform dimension
    let mut constraints: Vec<CertifiedConstraint> = raw_constraints
        .into_iter()
        .map(|(c, hyp_index)| CertifiedConstraint::from_hypothesis(c, hyp_index, total_count))
        .collect();

    // Add negation of goal (for proof by contradiction; WHNF fallback #685)
    let target = state.metas.instantiate(&goal.target);
    let goal_constraint = parse_linear_constraint(&target, &mut var_map, &mut next_var, None)
        .or_else(|| {
            let target_whnf = state.whnf(goal, &goal.target);
            parse_linear_constraint(&target_whnf, &mut var_map, &mut next_var, Some(whnf_fn))
        });
    if let Some(goal_constraint) = goal_constraint {
        // Negate the goal: to prove P, assume ¬P and derive contradiction
        constraints.push(CertifiedConstraint::from_negated_goal(
            goal_constraint.negate(),
            num_hyps,
        ));
    }

    if constraints.is_empty() {
        return None;
    }

    Some((constraints, var_map, hypothesis_fvars))
}

/// Extract linear constraints from the proof state
///
/// REQUIRES: `state` is a valid `ProofState`
/// REQUIRES: `goal` is a valid goal from `state`
/// ENSURES: On `Some(...)`, at least one constraint was extracted
/// ENSURES: `var_map` maps `FVarId`s to contiguous indices `[0, next_var)`
/// ENSURES: On `None`, no hypotheses or goal could be parsed as linear constraints
pub(crate) fn extract_linear_constraints(
    state: &ProofState,
    goal: &Goal,
) -> Option<(
    Vec<LinearConstraint>,
    std::collections::HashMap<FVarId, usize>,
)> {
    let mut constraints = Vec::new();
    let mut var_map: std::collections::HashMap<FVarId, usize> = std::collections::HashMap::new();
    let mut next_var = 0;
    let whnf_fn: &dyn Fn(&Expr) -> Expr = &|e| state.whnf(goal, e);

    // Extract constraints from hypotheses (WHNF fallback on parse failure, #685)
    for decl in &goal.local_ctx {
        let ty = state.metas.instantiate(&decl.ty);
        let constraint =
            parse_linear_constraint(&ty, &mut var_map, &mut next_var, None).or_else(|| {
                let ty_whnf = state.whnf(goal, &decl.ty);
                parse_linear_constraint(&ty_whnf, &mut var_map, &mut next_var, Some(whnf_fn))
            });
        if let Some(c) = constraint {
            constraints.push(c);
        }
    }

    // Add negation of goal (for proof by contradiction; WHNF fallback #685)
    let target = state.metas.instantiate(&goal.target);
    let goal_constraint = parse_linear_constraint(&target, &mut var_map, &mut next_var, None)
        .or_else(|| {
            let target_whnf = state.whnf(goal, &goal.target);
            parse_linear_constraint(&target_whnf, &mut var_map, &mut next_var, Some(whnf_fn))
        });
    if let Some(goal_constraint) = goal_constraint {
        // Negate the goal: to prove P, assume ¬P and derive contradiction
        constraints.push(goal_constraint.negate());
    }

    if constraints.is_empty() {
        return None;
    }

    Some((constraints, var_map))
}

/// Parse an expression as a linear constraint.
///
/// When `whnf_fn` is `Some`, sub-expressions that fail direct parsing are
/// WHNF-normalized and retried. This handles definitions wrapping arithmetic
/// operators (e.g., `myAdd x y` unfolding to `HAdd.hAdd ... x y`).
///
/// REQUIRES: `expr` is a well-formed kernel expression
/// REQUIRES: `var_map` and `next_var` track variable allocation state
/// ENSURES: On `Some(c)`, `c` is Eq/Le/Lt matching the top-level comparison in `expr`
/// ENSURES: On `None`, `expr` does not match a recognized comparison pattern
/// ENSURES: `var_map` and `next_var` are updated with any new free variables encountered
fn parse_linear_constraint(
    expr: &Expr,
    var_map: &mut std::collections::HashMap<FVarId, usize>,
    next_var: &mut usize,
    whnf_fn: Option<&dyn Fn(&Expr) -> Expr>,
) -> Option<LinearConstraint> {
    // Handle ≤, <, =, ≥, >
    // Pattern: LE.le _ _ lhs rhs, LT.lt _ _ lhs rhs, Eq _ lhs rhs

    // Check for equality first
    if let Ok((_ty, lhs, rhs, _levels)) = match_equality(expr) {
        let lhs_lin = parse_linear_expr(&lhs, var_map, next_var, whnf_fn)?;
        let rhs_lin = parse_linear_expr(&rhs, var_map, next_var, whnf_fn)?;
        return Some(LinearConstraint::Eq(lhs_lin.sub(&rhs_lin)));
    }

    // Check for LE.le, LT.lt, GE.ge, GT.gt.
    //
    // Wave 103: the previous implementation only matched the fully
    // type-class-elaborated 4-arg shape (`LE.le ty inst lhs rhs`) via
    // nested `ExprKind::App` peeks. Integration tests and a number of
    // lowered surface fixtures use the 2-arg shape (`LE.le lhs rhs`) or
    // the 3-arg shape (`LE.le ty lhs rhs`) — in both cases the previous
    // matcher silently bailed out, the extractor returned `None`, and
    // `linarith` reported "could not extract linear constraints" even
    // when the hypothesis was structurally a `<=`. The new approach
    // walks the application spine, checks that the head constant is a
    // recognised comparison, and treats the *last two* spine arguments
    // as `lhs`, `rhs`. This subsumes the 2-, 3-, and 4-arg shapes
    // without changing semantics for fully elaborated terms.
    if let Some((head, args)) = app_spine(expr) {
        if args.len() >= 2 {
            if let ExprKind::Const(name, _) = head.kind() {
                let name_str = name.to_string();
                let kind = comparison_kind(&name_str);
                if let Some(kind) = kind {
                    // Treat the last two spine arguments as lhs, rhs.
                    let lhs = args[args.len() - 2];
                    let rhs = args[args.len() - 1];
                    let lhs_lin = parse_linear_expr(lhs, var_map, next_var, whnf_fn)?;
                    let rhs_lin = parse_linear_expr(rhs, var_map, next_var, whnf_fn)?;
                    return Some(match kind {
                        // lhs ≤ rhs  =>  lhs - rhs ≤ 0
                        ComparisonKind::Le => LinearConstraint::Le(lhs_lin.sub(&rhs_lin)),
                        // lhs < rhs  =>  lhs - rhs < 0
                        ComparisonKind::Lt => LinearConstraint::Lt(lhs_lin.sub(&rhs_lin)),
                        // lhs ≥ rhs  =>  rhs - lhs ≤ 0
                        ComparisonKind::Ge => LinearConstraint::Le(rhs_lin.sub(&lhs_lin)),
                        // lhs > rhs  =>  rhs - lhs < 0
                        ComparisonKind::Gt => LinearConstraint::Lt(rhs_lin.sub(&lhs_lin)),
                    });
                }
            }
        }
    }

    None
}

#[derive(Copy, Clone)]
enum ComparisonKind {
    Le,
    Lt,
    Ge,
    Gt,
}

fn comparison_kind(name_str: &str) -> Option<ComparisonKind> {
    if name_str.contains("LE.le")
        || name_str.contains("Nat.le")
        || name_str.contains("Int.le")
        || name_str.contains("Real.le")
        || name_str.contains("Rat.le")
    {
        Some(ComparisonKind::Le)
    } else if name_str.contains("LT.lt")
        || name_str.contains("Nat.lt")
        || name_str.contains("Int.lt")
        || name_str.contains("Real.lt")
        || name_str.contains("Rat.lt")
    {
        Some(ComparisonKind::Lt)
    } else if name_str.contains("GE.ge") {
        Some(ComparisonKind::Ge)
    } else if name_str.contains("GT.gt") {
        Some(ComparisonKind::Gt)
    } else {
        None
    }
}

/// Walk the application spine of `expr` and return `(head, args)` where
/// `args` is left-to-right (i.e. `head args[0] args[1] ...`). Returns
/// `None` if `expr` is not an application.
fn app_spine(expr: &Expr) -> Option<(&Expr, Vec<&Expr>)> {
    let mut args = Vec::new();
    let mut current = expr;
    while let ExprKind::App(f, a) = current.kind() {
        args.push(a.as_ref());
        current = f;
    }
    if args.is_empty() {
        None
    } else {
        args.reverse();
        Some((current, args))
    }
}

/// Parse an expression as a linear expression.
///
/// When `whnf_fn` is `Some`, unrecognized App sub-expressions are
/// WHNF-normalized and retried. This sees through definitions wrapping
/// arithmetic operators (e.g., `myAdd` → `HAdd.hAdd`).
///
/// REQUIRES: `expr` is a well-formed kernel expression
/// ENSURES: On `Some(le)`, `le` is a linear representation of `expr`
/// ENSURES: Multiplication returns `None` when both sides contain variables (non-linear)
/// ENSURES: Stack-safe via `stack_safe()` guard against deep recursion
fn parse_linear_expr(
    expr: &Expr,
    var_map: &mut std::collections::HashMap<FVarId, usize>,
    next_var: &mut usize,
    whnf_fn: Option<&dyn Fn(&Expr) -> Expr>,
) -> Option<LinearExpr> {
    stack_safe(|| {
        let result = parse_linear_expr_direct(expr, var_map, next_var, whnf_fn);
        if result.is_some() {
            return result;
        }
        // WHNF fallback for unrecognized App sub-expressions (#685).
        // Only try if we have a WHNF function and the expression is an
        // application (definitions wrapping arithmetic operators).
        if let Some(whnf) = whnf_fn {
            if matches!(expr.kind(), ExprKind::App(_, _)) {
                let normalized = whnf(expr);
                if normalized != *expr {
                    return parse_linear_expr_direct(&normalized, var_map, next_var, whnf_fn);
                }
            }
        }
        None
    })
}

/// Whether a `@HSub.hSub α β γ inst x y` application is over the `Nat` carrier.
///
/// Truncated `Nat` subtraction must not be modeled as untruncated integer
/// subtraction in the linear form (a soundness hazard). We treat the operation
/// as Nat-sub when any of the (leading) carrier type arguments is `Nat`.
fn hsub_carrier_is_nat(expr: &Expr) -> bool {
    let args = expr.get_app_args();
    // `HSub.hSub α β γ inst x y` — the first three args are the carrier types.
    args.iter()
        .take(3)
        .any(|t| matches!(t.kind(), ExprKind::Const(n, _) if n.to_string() == "Nat"))
}

/// Direct parse of a linear expression without WHNF fallback.
///
/// REQUIRES: `expr` is a well-formed kernel expression
/// ENSURES: On `Some(le)`, `le.coeffs` contains only variables appearing in `expr`
/// ENSURES: Nat literals map to `LinearExpr::constant(n)` where `n` fits in `i64`
/// ENSURES: Free variables get fresh indices via `var_map`/`next_var`
fn parse_linear_expr_direct(
    expr: &Expr,
    var_map: &mut std::collections::HashMap<FVarId, usize>,
    next_var: &mut usize,
    whnf_fn: Option<&dyn Fn(&Expr) -> Expr>,
) -> Option<LinearExpr> {
    match expr.kind() {
        // Literal natural number
        ExprKind::Lit(clean_kernel::expr::Literal::Nat(n)) => {
            big_nat_to_i64(n).map(LinearExpr::constant)
        }

        // Constants like Nat.zero / Int.zero / Real.zero
        ExprKind::Const(name, _) => {
            let name_str = name.to_string();
            if name_str == "Nat.zero"
                || name_str == "Int.zero"
                || name_str == "Real.zero"
                || name_str == "Rat.zero"
            {
                Some(LinearExpr::constant(0))
            } else if name_str == "Nat.one"
                || name_str == "Int.one"
                || name_str == "Real.one"
                || name_str == "Rat.one"
                || name_str == "1"
            {
                Some(LinearExpr::constant(1))
            } else {
                None
            }
        }

        // Free variable - treat as a linear variable
        ExprKind::FVar(fvar_id) => {
            let idx = *var_map.entry(*fvar_id).or_insert_with(|| {
                let v = *next_var;
                *next_var += 1;
                v
            });
            Some(LinearExpr::var(idx))
        }

        // Application - check for operations
        ExprKind::App(f, arg) => {
            // Constructor-style embeddings and successors.
            if let ExprKind::Const(name, _) = f.kind() {
                match name.to_string().as_str() {
                    "Nat.succ" => {
                        let inner = parse_linear_expr(arg, var_map, next_var, whnf_fn)?;
                        return Some(inner.add(&LinearExpr::constant(1)));
                    }
                    // Integer-valued Real/Nat/Rat embeddings preserve linear structure.
                    "Int.ofNat" | "Real.ofNat" | "Real.ofInt" | "Rat.ofInt" => {
                        return parse_linear_expr(arg, var_map, next_var, whnf_fn);
                    }
                    // Int.negSucc n = -(n + 1), which is still affine.
                    "Int.negSucc" => {
                        let inner = parse_linear_expr(arg, var_map, next_var, whnf_fn)?;
                        return Some(LinearExpr::constant(-1).sub(&inner));
                    }
                    // Direct unary negation: Rat.neg x = -x, Int.neg x = -x.
                    "Rat.neg" | "Int.neg" => {
                        let inner = parse_linear_expr(arg, var_map, next_var, whnf_fn)?;
                        return Some(inner.scale(-1));
                    }
                    _ => {}
                }
            }

            // Binary/unary operators via the FULL application spine.
            //
            // Using `app_spine` (head + all args) instead of a fixed-depth
            // `App` peel makes operator detection robust to the fully
            // type-class-elaborated shapes `@HAdd.hAdd α β γ inst a b` (6 args),
            // `@HSub.hSub …`, `@HMul.hMul …`, where the operator head is buried
            // under the carrier-type and instance arguments. The previous fixed
            // 2-3 layer peel only matched partially-applied forms, so an Int
            // goal like `a < b + 1` left `b + 1` UNPARSED. The operands are
            // always the LAST TWO spine args; the preceding args are carrier
            // types / instances.
            if let Some((head, args)) = app_spine(expr) {
                if let ExprKind::Const(op_name, _) = head.kind() {
                    let op_str = op_name.to_string();

                    // Numeric literal `@OfNat.ofNat α n inst` → the numeral `n`
                    // (second explicit spine arg, a raw `Nat` literal). Kernel
                    // re-check in `close_goal` remains the soundness gate.
                    if op_str == "OfNat.ofNat" && args.len() >= 2 {
                        if let ExprKind::Lit(clean_kernel::expr::Literal::Nat(n)) = args[1].kind() {
                            return big_nat_to_i64(n).map(LinearExpr::constant);
                        }
                    }

                    // Unary negation: `@Neg.neg T inst x` / `@HNeg.hNeg α β inst x`.
                    if (op_str == "Neg.neg" || op_str == "HNeg.hNeg") && !args.is_empty() {
                        let inner =
                            parse_linear_expr(args[args.len() - 1], var_map, next_var, whnf_fn)?;
                        return Some(inner.scale(-1));
                    }

                    if args.len() >= 2 {
                        let lhs_e = args[args.len() - 2];
                        let rhs_e = args[args.len() - 1];

                        if op_str.contains("add") || op_str.contains("Add") {
                            let lhs = parse_linear_expr(lhs_e, var_map, next_var, whnf_fn)?;
                            let rhs = parse_linear_expr(rhs_e, var_map, next_var, whnf_fn)?;
                            return Some(lhs.add(&rhs));
                        }
                        if op_str.contains("sub") || op_str.contains("Sub") {
                            // SOUNDNESS: `Nat.sub` is *truncated* subtraction, NOT
                            // the untruncated integer sub `lhs.sub(&rhs)` models —
                            // refuse raw `Nat.sub` AND any `HSub`/`Sub` over a
                            // `Nat` carrier (fail closed); Int/Rat/Real sub parses.
                            if op_str == "Nat.sub" || hsub_carrier_is_nat(expr) {
                                return None;
                            }
                            let lhs = parse_linear_expr(lhs_e, var_map, next_var, whnf_fn)?;
                            let rhs = parse_linear_expr(rhs_e, var_map, next_var, whnf_fn)?;
                            return Some(lhs.sub(&rhs));
                        }
                        if op_str.contains("mul") || op_str.contains("Mul") {
                            // SOUNDNESS: linear only if one factor is constant;
                            // variable*variable is non-linear → None.
                            let lhs = parse_linear_expr(lhs_e, var_map, next_var, whnf_fn)?;
                            let rhs = parse_linear_expr(rhs_e, var_map, next_var, whnf_fn)?;
                            if lhs.is_constant() {
                                return Some(rhs.scale(lhs.constant));
                            }
                            if rhs.is_constant() {
                                return Some(lhs.scale(rhs.constant));
                            }
                            return None;
                        }
                        // SOUNDNESS: `Nat.min`/`Nat.max` (and unrecognized heads)
                        // fall through to `None` so the FM path refuses the goal
                        // rather than modeling a non-linear op as a fresh atom.
                    }
                }
            }

            None
        }

        _ => None,
    }
}

#[cfg(test)]
#[path = "parse_tests.rs"]
mod tests;
