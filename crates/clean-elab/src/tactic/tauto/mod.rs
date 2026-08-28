// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Propositional tautology solver
//!
//! Provides the `tauto` tactic for solving classical propositional logic goals.

mod atom_split;
mod classical;
mod search;

use clean_kernel::expr::ExprKind;
use clean_kernel::Expr;

use super::{
    assumption, cases, clear, contradiction, exprs_syntactically_equal, intro, is_false, left_,
    match_and, match_iff, match_not, match_or, rfl, right_, solve_by_elim, split_, trivial,
    try_tactic_preserving_state, Goal, LocalDecl, ProofState, TacticError, TacticResult,
};
use crate::stack_safe;
use crate::tactic::simp::{is_trivial_equality, is_true_const};

use search::tauto_prove;

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
    let mut atom_splits = DEFAULT_TAUTO_MAX_ATOM_SPLITS;
    if tauto_prove(state, &goal, 0, max_depth, &mut atom_splits)? {
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

            // An Iff hypothesis is inert to every matcher in tauto_prove;
            // destructing it into its mp/mpr implications makes both sides
            // reachable by solve_by_elim. Terminates: mp/mpr are Pis, which
            // this arm never re-matches.
            if match_iff(&ty_whnf).is_some() {
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

/// Global `by_cases` budget for classical atom splits, per `tauto` invocation.
///
/// Threaded through `tauto_prove` as a never-restored countdown: every
/// EXECUTED `by_cases` decrements it, including on branch failure, so at most
/// this many splits run in total — an additive bound over the existing
/// tableau search rather than a multiplicative per-dead-end retry. (grind
/// restores its split budget on branch failure; restoring here would re-arm
/// exhausted subtrees on top of an already 3-way-exponential search.)
///
/// Sizing: the split fires at EVERY dead end, so branches that were always
/// going to fail (the or-target's left_/right_ subtrees) burn budget at
/// their nested dead ends before the shallow profitable split runs. The
/// canonical class (from `a ↔ b` prove `(¬a ∧ ¬b) ∨ (b ∧ ¬¬a)`) hand-traces
/// to 15 total executions — 12 of them spent inside failing subtrees — so 8
/// (one full 3-atom split tree) is NOT enough; 24 covers the trace with
/// margin while staying well under grind's effective 32-with-restore.
const DEFAULT_TAUTO_MAX_ATOM_SPLITS: usize = 24;

/// Per-dead-end cap on collected split-atom candidates.
///
/// Bounds per-dead-end ATTEMPTS (a failed `by_cases` still consumes budget);
/// goal-target leaves are collected before hypothesis leaves so large
/// imported contexts cannot drain the budget on context junk.
const MAX_ATOM_CANDIDATES: usize = 4;

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
