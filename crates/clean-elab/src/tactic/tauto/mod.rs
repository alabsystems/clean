// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Propositional tautology solver
//!
//! Provides the `tauto` tactic for solving classical propositional logic goals.

mod classical;

use clean_kernel::expr::ExprKind;

use super::{
    assumption, cases, clear, contradiction, exprs_syntactically_equal, intro, is_false, left_,
    match_and, match_iff, match_not, match_or, rfl, right_, solve_by_elim, split_, trivial,
    try_tactic_preserving_state, Goal, LocalDecl, ProofState, TacticError, TacticResult,
};
use crate::stack_safe;
use crate::tactic::simp::{is_trivial_equality, is_true_const};

use classical::{try_by_cases_for_disjunction, try_classical_dne};

/// Solve propositional tautologies.
///
/// REQUIRES: `state.goals` is non-empty.
/// ENSURES: On Ok, the current goal is closed as a propositional tautology.
///   On Err(NoProgress), the goal is not a propositional tautology.
pub fn tauto(state: &mut ProofState) -> TacticResult {
    if state.goals.is_empty() {
        return Err(TacticError::NoGoals);
    }

    let max_depth = state
        .options()
        .max_depth_override()
        .unwrap_or(DEFAULT_TAUTO_MAX_DEPTH);

    let trace = std::env::var_os("CLEAN_GRIND_TRACE").is_some();
    if trace {
        eprintln!("tauto-trace: enter max_depth={max_depth}");
    }
    preprocess_tauto_context(state)?;
    if trace {
        eprintln!("tauto-trace: preprocess done");
    }

    if state.goals.is_empty() {
        return Ok(());
    }

    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();

    // Part of #2474: wrap each branch in try_tactic_preserving_state to prevent
    // failed tactics from leaking partial state mutations to subsequent branches.
    if try_tactic_preserving_state(state, rfl) {
        return Ok(());
    }

    if try_tactic_preserving_state(state, trivial) {
        return Ok(());
    }

    if try_tactic_preserving_state(state, assumption) {
        return Ok(());
    }

    if trace {
        eprintln!("tauto-trace: closers done, entering tauto_prove");
    }
    if tauto_prove(state, &goal, 0, max_depth)? {
        return Ok(());
    }

    Err(TacticError::NoProgress {
        tactic: "tauto".into(),
    })
}

/// Simplify the local context for propositional reasoning.
///
/// Removes trivial hypotheses (True, a = a), splits conjunctions, and
/// discharges goals that already contain contradictions.
fn preprocess_tauto_context(state: &mut ProofState) -> Result<(), TacticError> {
    loop {
        if state.goals.is_empty() {
            return Ok(());
        }

        let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();
        let mut progress = false;

        for decl in goal.local_ctx.clone() {
            let ty = state.metas.instantiate(&decl.ty);
            if std::env::var_os("CLEAN_GRIND_TRACE").is_some() {
                eprintln!("tauto-trace: preprocess whnf hyp {}", decl.name);
            }
            let ty_whnf = state.whnf(&goal, &ty);

            if is_false(&ty_whnf) {
                contradiction(state)?;
                return Ok(());
            }

            if is_true_const(&ty_whnf) || is_trivial_equality(&ty_whnf) {
                clear(state, &decl.name)?;
                progress = true;
                break;
            }

            if match_and(&ty_whnf).is_some() {
                cases(state, &decl.name)?;
                progress = true;
                break;
            }
        }

        if !progress {
            break;
        }
    }

    Ok(())
}

/// Find the first disjunctive hypothesis in the local context.
fn find_or_hypothesis(state: &mut ProofState, goal: &Goal) -> Option<String> {
    for decl in &goal.local_ctx {
        let ty = state.metas.instantiate(&decl.ty);
        let ty_whnf = state.whnf(goal, &ty);
        if match_or(&ty_whnf).is_some() {
            return Some(decl.name.clone());
        }
    }
    None
}

/// Maximum recursion depth for tauto_prove.
///
/// With 3-way branching on disjunctions, depth 20 allows 3^20 ≈ 3.5B nodes
/// in the worst case — more than enough for any real propositional formula.
/// Without this bound, nested disjunctions cause exponential time blowup.
const DEFAULT_TAUTO_MAX_DEPTH: usize = 20;

/// Main propositional tautology prover.
///
/// REQUIRES: `state` has at least one goal.
/// ENSURES: Returns Ok(true) if the goal was proved as a propositional
///   tautology using tableau-style search. Returns Ok(false) if the search
///   exhausted without proof or depth limit reached.
fn tauto_prove(
    state: &mut ProofState,
    _goal: &Goal,
    depth: usize,
    max_depth: usize,
) -> Result<bool, TacticError> {
    stack_safe(|| {
        if depth >= max_depth {
            return Ok(false);
        }

        if std::env::var_os("CLEAN_GRIND_TRACE").is_some() {
            eprintln!("tauto-trace: prove depth={depth}");
        }
        preprocess_tauto_context(state)?;

        if state.goals.is_empty() {
            return Ok(true);
        }

        let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();
        let target = &goal.target;

        if contradiction(state).is_ok() {
            return Ok(true);
        }

        if let Some(hyp_name) = find_or_hypothesis(state, &goal) {
            let goals_backup = state.goals.clone();
            if cases(state, &hyp_name).is_ok() {
                let remaining_goals = state.goals.split_off(1);
                let first_goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();
                if tauto_prove(state, &first_goal, depth + 1, max_depth)? {
                    state.goals.extend(remaining_goals);
                    if state.goals.is_empty() {
                        return Ok(true);
                    }
                    let second_goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();
                    let remaining_after_second = state.goals.split_off(1);
                    if tauto_prove(state, &second_goal, depth + 1, max_depth)? {
                        state.goals.extend(remaining_after_second);
                        return Ok(true);
                    }
                }
            }
            state.invalidate_tc_cache();
            state.goals = goals_backup;
        }

        if is_true_const(target) {
            return Ok(trivial(state).is_ok());
        }

        if is_false(target) {
            if assumption(state).is_ok() {
                return Ok(true);
            }
            if contradiction(state).is_ok() {
                return Ok(true);
            }
            return Ok(false);
        }

        // Check for P ∨ ¬P (excluded middle)
        if let Some((p, q)) = match_or(target) {
            if let Some(inner_p) = match_not(&q) {
                if exprs_syntactically_equal(&p, &inner_p) {
                    let hyp_name = fresh_hyp_name(&goal.local_ctx, "h");
                    if super::by_cases(state, &hyp_name, p.clone()).is_ok()
                        && left_(state).is_ok()
                        && assumption(state).is_ok()
                        && right_(state).is_ok()
                        && assumption(state).is_ok()
                    {
                        return Ok(true);
                    }
                }
            }
            if let Some(inner_p) = match_not(&p) {
                if exprs_syntactically_equal(&inner_p, &q) {
                    let hyp_name = fresh_hyp_name(&goal.local_ctx, "h");
                    if super::by_cases(state, &hyp_name, q.clone()).is_ok()
                        && right_(state).is_ok()
                        && assumption(state).is_ok()
                        && left_(state).is_ok()
                        && assumption(state).is_ok()
                    {
                        return Ok(true);
                    }
                }
            }
        }

        // Conjunction: split and prove both
        if let Some((_p, _q)) = match_and(target) {
            if split_(state).is_ok() {
                let first_goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();
                if tauto_prove(state, &first_goal, depth + 1, max_depth)? && !state.goals.is_empty()
                {
                    let second_goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();
                    if tauto_prove(state, &second_goal, depth + 1, max_depth)? {
                        return Ok(true);
                    }
                }
            }
            return Ok(false);
        }

        // Biconditional (Iff): split into two implications
        if match_iff(target).is_some() {
            if split_(state).is_ok() {
                let first_goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();
                if tauto_prove(state, &first_goal, depth + 1, max_depth)? && !state.goals.is_empty()
                {
                    let second_goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();
                    if tauto_prove(state, &second_goal, depth + 1, max_depth)? {
                        return Ok(true);
                    }
                }
            }
            return Ok(false);
        }

        // Disjunction: try left, then right, then by_cases
        if match_or(target).is_some() {
            let goals_backup = state.goals.clone();

            if left_(state).is_ok() {
                let left_goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();
                if tauto_prove(state, &left_goal, depth + 1, max_depth)? {
                    return Ok(true);
                }
            }

            state.invalidate_tc_cache();
            state.goals = goals_backup.clone();
            if right_(state).is_ok() {
                let right_goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();
                if tauto_prove(state, &right_goal, depth + 1, max_depth)? {
                    return Ok(true);
                }
            }

            state.invalidate_tc_cache();
            state.goals = goals_backup;
            if try_by_cases_for_disjunction(state)? {
                return Ok(true);
            }

            return Ok(false);
        }

        // Implication: intro and continue
        if let ExprKind::Pi(_, _, _) = target.kind() {
            let hyp_name = fresh_hyp_name(&goal.local_ctx, "h");
            if intro(state, &hyp_name).is_ok() {
                let new_goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();
                return tauto_prove(state, &new_goal, depth + 1, max_depth);
            }
        }

        if assumption(state).is_ok() {
            return Ok(true);
        }

        if try_classical_dne(state).is_ok() {
            return Ok(true);
        }

        // Keep the fallback local-hypothesis search within the caller's remaining
        // tauto budget so `set_option max_depth` cannot be bypassed here.
        let solve_by_elim_max_depth = max_depth - depth;
        if solve_by_elim(state, solve_by_elim_max_depth).is_ok() {
            return Ok(true);
        }

        Ok(false)
    })
}

/// Generate a fresh hypothesis name
pub(crate) fn fresh_hyp_name(local_ctx: &[LocalDecl], base: &str) -> String {
    let name = base.to_string();
    let mut counter = 0;

    loop {
        let candidate = if counter == 0 {
            name.clone()
        } else {
            format!("{name}{counter}")
        };

        if !local_ctx.iter().any(|d| d.name == candidate) {
            return candidate;
        }
        counter += 1;
    }
}
