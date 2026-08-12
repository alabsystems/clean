// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Integer interval case splitting tactic (`interval_cases`).
//!
//! Extracted from `finite_cases.rs` for file-size compliance.

use clean_kernel::name::Name;
use clean_kernel::{Expr, ExprKind, Level};

use super::finite_cases::{make_nat_literal, substitute_fvar};
use super::finite_cases_proof::build_or_elim_chain;
use super::nat_expr_eval::read_nat_numeral;
use super::{match_le, match_lt, Goal, LocalDecl, ProofState, TacticError, TacticResult};

/// Case split on an integer hypothesis within an interval.
///
/// Creates separate goals for each integer in [lower, upper] determined
/// from context bounds. Each sub-goal adds an equality hypothesis.
///
/// REQUIRES: `state` is a well-formed proof state
/// REQUIRES: `hyp_name` names a local hypothesis in the current goal's context
///
/// ENSURES: on `Ok(())`, the original goal is closed via an `Or.elim` chain
/// and one sub-goal per integer value is prepended to `state.goals`
/// ENSURES: the range is capped at 100 values; larger ranges return
/// `Err(InvalidTarget)`
/// ENSURES: on `Err(NoGoals)` or `Err(HypothesisNotFound)`, `state` is unchanged
pub fn interval_cases(state: &mut ProofState, hyp_name: &str) -> TacticResult {
    if state.goals.is_empty() {
        return Err(TacticError::NoGoals);
    }

    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();

    // Find the hypothesis
    let hyp = goal
        .local_ctx
        .iter()
        .find(|d| d.name == hyp_name)
        .ok_or_else(|| TacticError::HypothesisNotFound(hyp_name.to_string()))?
        .clone();

    // Try to determine bounds from context
    let (lower, upper) = find_integer_bounds(&goal, &hyp)?;

    if upper - lower > 100 {
        return Err(TacticError::InvalidTarget {
            tactic: "interval_cases".into(),
            detail: format!("range too large ({} values)", upper - lower + 1),
        });
    }

    let (new_goals, value_exprs) =
        build_interval_goals(state, &goal, &hyp, hyp_name, lower, upper)?;

    // SOUNDNESS FIX (#2232): Construct Or.elim chain proof linking original
    // goal meta to sub-goal metas before closing the goal. Previously, the goal
    // was popped without meta assignment, leaving an orphaned metavariable.
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let proof = build_or_elim_chain(
        state,
        &goal.target,
        hyp.fvar,
        &nat_ty,
        &new_goals,
        &value_exprs,
        0,
    )?;

    // Part of #2154 Wave 10: migrated from close_goal_unchecked.
    // Proof is an Or.rec + Classical.em chain with all sub-goal metas linked.
    // Requires env with Or.rec + Classical.em (from init_classical).
    state.close_goal(&goal, proof)?;

    for new_goal in new_goals.into_iter().rev() {
        state.goals.push_front(new_goal);
    }

    Ok(())
}

/// Build sub-goals for each integer value in the range [lower, upper].
///
/// Returns (goals, value_expressions) for proof construction.
///
/// REQUIRES: `lower <= upper` (caller enforces)
/// REQUIRES: `hyp` is a hypothesis from `goal.local_ctx`
///
/// ENSURES: returns `(goals, value_exprs)` where both vectors have length
/// `(upper - lower + 1)`. Non-dependent targets substitute `hyp.fvar` with
/// the corresponding integer value; dependent targets keep the original target
/// and rely on the generated equality hypothesis for refinement
/// ENSURES: each sub-goal context includes an equality hypothesis `hyp_name_eq`
fn build_interval_goals(
    state: &mut ProofState,
    goal: &Goal,
    hyp: &LocalDecl,
    hyp_name: &str,
    lower: i64,
    upper: i64,
) -> Result<(Vec<Goal>, Vec<Expr>), TacticError> {
    let mut new_goals = Vec::new();
    let mut value_exprs = Vec::new();
    let target_depends_on_hyp = goal.target.abstract_fvar(hyp.fvar) != goal.target;

    let value_count =
        usize::try_from(upper - lower + 1).map_err(|_| TacticError::InvalidTarget {
            tactic: "interval_cases".into(),
            detail: "interval size does not fit in memory".into(),
        })?;
    for (case_idx, value) in (lower..=upper).enumerate() {
        let value_expr = make_int_literal(value);
        let mut new_ctx = goal.local_ctx.clone();
        // Each non-final branch is introduced by the corresponding true-side
        // lambda in `build_or_elim_chain`. Allocate its equality FVar in binder
        // order so final proof closing maps it to that lambda's BVar. The final
        // branch is reached only through negations of all prior equalities; the
        // current fallback has no constructive proof of `h = final_value`, so
        // granting that equality would fabricate local authority.
        if case_idx + 1 < value_count {
            new_ctx.push(LocalDecl {
                fvar: state.fresh_fvar(),
                name: format!("{hyp_name}_eq"),
                ty: make_equality_type(
                    &Expr::const_(Name::from_string("Nat"), vec![]),
                    &Expr::fvar(hyp.fvar),
                    &value_expr,
                    Level::succ(Level::zero()), // Nat : Type 0 = Sort 1
                ),
                value: None,
            });
        }

        // The Or.rec fallback only carries the branch-local equality proof for
        // the active branch. If we eagerly substitute a dependent target, the
        // final branch has no equality witness left to transport back to the
        // original goal type, so keep the original target in that case.
        let new_target = if target_depends_on_hyp {
            goal.target.clone()
        } else {
            substitute_fvar(&goal.target, hyp.fvar, &value_expr)
        };
        let new_meta_id = state.fresh_meta_in_context(new_target.clone(), &new_ctx);
        new_goals.push(Goal {
            meta_id: new_meta_id,
            target: new_target,
            local_ctx: new_ctx,
            tag: None,
        });
        value_exprs.push(value_expr);
    }

    Ok((new_goals, value_exprs))
}

/// Find integer bounds for a variable from the context
///
/// REQUIRES: `hyp` is a hypothesis from `goal.local_ctx`
///
/// ENSURES: on `Ok((lower, upper))`, `lower <= upper` and both bounds were
/// derived from `≤` or `<` hypotheses in the goal context
/// ENSURES: returns `Err(InvalidTarget)` when no lower bound, no upper bound,
/// or inconsistent bounds are found (#2239 soundness fix)
fn find_integer_bounds(goal: &Goal, hyp: &LocalDecl) -> Result<(i64, i64), TacticError> {
    let mut lower = i64::MIN;
    let mut upper = i64::MAX;

    // Look through hypotheses for bounds
    for decl in &goal.local_ctx {
        // Check for h ≤ n patterns (upper bound)
        // match_le returns (ty, lhs, rhs) where lhs ≤ rhs
        if let Some((_ty, lhs, rhs)) = match_le(&decl.ty) {
            if let ExprKind::FVar(id) = rhs.kind() {
                if *id == hyp.fvar {
                    if let Some(val) = expr_to_int(&lhs) {
                        lower = lower.max(val);
                    }
                }
            }
            if let ExprKind::FVar(id) = lhs.kind() {
                if *id == hyp.fvar {
                    if let Some(val) = expr_to_int(&rhs) {
                        upper = upper.min(val);
                    }
                }
            }
        }

        // Check for h < n patterns
        // match_lt returns (ty, lhs, rhs) where lhs < rhs
        if let Some((_ty, lhs, rhs)) = match_lt(&decl.ty) {
            if let ExprKind::FVar(id) = rhs.kind() {
                if *id == hyp.fvar {
                    if let Some(val) = expr_to_int(&lhs) {
                        lower = lower.max(val + 1);
                    }
                }
            }
            if let ExprKind::FVar(id) = lhs.kind() {
                if *id == hyp.fvar {
                    if let Some(val) = expr_to_int(&rhs) {
                        upper = upper.min(val - 1);
                    }
                }
            }
        }
    }

    // SOUNDNESS FIX (#2239): Return error when no bounds found.
    // Previously fabricated default bounds (0..10), unsound for unbounded integers.
    if lower == i64::MIN || upper == i64::MAX {
        let missing = match (lower == i64::MIN, upper == i64::MAX) {
            (true, true) => "no bounds",
            (true, false) => "no lower bound",
            (false, true) => "no upper bound",
            (false, false) => unreachable!("both bounds present, handled by outer guard"),
        };
        return Err(TacticError::InvalidTarget {
            tactic: "interval_cases".into(),
            detail: format!("{missing} found in context; add ≤ or < hypotheses"),
        });
    }

    if lower > upper {
        return Err(TacticError::InvalidTarget {
            tactic: "interval_cases".into(),
            detail: "inconsistent bounds".into(),
        });
    }

    Ok((lower, upper))
}

/// Convert expression to integer if possible
///
/// Delegates to the shared `nat_expr_eval::read_nat_numeral` reader so the
/// `@OfNat.ofNat Nat k inst` form the elaborator builds for a source numeral is
/// recognized. Before that (RC-H), this handled only `Nat.zero` / a `Nat.succ`
/// chain / a raw `Lit(Nat)`, so `interval_cases n` under `h1 : 2 ≤ n` and
/// `h2 : n ≤ 3` reported "no bounds found in context" while the
/// `Nat.succ`-spelled bounds were read.
///
/// REQUIRES: `expr` is a well-formed Lean expression
///
/// ENSURES: returns `Some(n)` when `expr` denotes the Nat numeral `n` and `n`
/// fits in an `i64`
/// ENSURES: returns `None` for non-numeral expressions
/// ENSURES: recursive descent runs under `stack_safe`
pub(crate) fn expr_to_int(expr: &Expr) -> Option<i64> {
    read_nat_numeral(expr).and_then(|v| i64::try_from(v).ok())
}

/// Make an integer literal expression
///
/// ENSURES: for `n >= 0`, delegates to `make_nat_literal`
/// ENSURES: for `n < 0`, returns `Int.negOfNat(|n|)`
pub(crate) fn make_int_literal(n: i64) -> Expr {
    if n >= 0 {
        make_nat_literal(n as u64)
    } else {
        // For negative, use Int.negOfNat
        Expr::app(
            Expr::const_(Name::from_string("Int.negOfNat"), vec![]),
            make_nat_literal((-n) as u64),
        )
    }
}

/// Make an equality type expression: `@Eq ty lhs rhs`
///
/// REQUIRES: `ty`, `lhs`, `rhs` are well-formed and `lhs`/`rhs` inhabit `ty`
///
/// ENSURES: returns the fully-applied `@Eq.{level} ty lhs rhs` expression
pub(crate) fn make_equality_type(ty: &Expr, lhs: &Expr, rhs: &Expr, level: Level) -> Expr {
    let eq = Expr::const_(Name::from_string("Eq"), vec![level]);
    Expr::app(
        Expr::app(Expr::app(eq, ty.clone()), lhs.clone()),
        rhs.clone(),
    )
}
