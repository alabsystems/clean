// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The tableau search core of `tauto`: `tauto_prove` and its isolated
//! `solve_by_elim` shim. Split out of `tauto/mod.rs` for file size; the
//! budgets it reads stay in the parent module.

// Everything `tauto/mod.rs` imports is in scope here through the glob, so the
// moved bodies resolve exactly the names they resolved before the split.
use super::atom_split::try_classical_atom_split;
use super::classical::{try_by_cases_for_disjunction, try_classical_dne};
use super::*;

/// Main propositional tautology prover.
///
/// REQUIRES: `state` has at least one goal.
/// ENSURES: Returns Ok(true) if the goal was proved as a propositional
///   tautology using tableau-style search. Returns Ok(false) if the search
///   exhausted without proof or depth limit reached.
///   `splits_remaining` is the global classical-split countdown (see
///   DEFAULT_TAUTO_MAX_ATOM_SPLITS); consumed budget is never restored.
pub(super) fn tauto_prove(
    state: &mut ProofState,
    _goal: &Goal,
    depth: usize,
    max_depth: usize,
    splits_remaining: &mut usize,
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

        if let Some(hyp_fvar) = find_or_hypothesis(state, &goal) {
            // SOUNDNESS/COMPLETENESS: back out the METAVARIABLE state as well
            // as the goal list. `cases`/`left_`/`right_` close the goal meta
            // via `close_goal`, and `MetaState::assign` refuses re-assignment,
            // so restoring only `state.goals` leaves the meta assigned and
            // every LATER alternative at this choice point fails — tauto was
            // effectively a left-spine-only prover (and `grind`, which
            // delegates its propositional work here, inherited that). Use the
            // push_scope/commit/pop_scope discipline `try_tactic_preserving_state`
            // and grind's own `try_split_disjunction` already use.
            let goals_backup = state.goals.clone();
            // Positional fvar discipline (see try_classical_atom_split): a
            // rolled-back `by_cases`/`cases` leaves `next_fvar` advanced, and
            // close_fvars ties FVar ids to binder depth — later minting at the
            // shifted cursor fails "assignment violates its creation scope".
            let next_fvar_backup = state.next_fvar;
            state.metas_mut().push_scope();
            if cases_fvar(state, hyp_fvar).is_ok() {
                let remaining_goals = state.goals.split_off(1);
                let first_goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();
                if tauto_prove(state, &first_goal, depth + 1, max_depth, splits_remaining)? {
                    state.goals.extend(remaining_goals);
                    if state.goals.is_empty() {
                        return Ok(true);
                    }
                    let second_goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();
                    let remaining_after_second = state.goals.split_off(1);
                    if tauto_prove(state, &second_goal, depth + 1, max_depth, splits_remaining)? {
                        state.goals.extend(remaining_after_second);
                        state.metas_mut().commit();
                        return Ok(true);
                    }
                }
            }
            state.invalidate_tc_cache();
            state.goals = goals_backup;
            state.next_fvar = next_fvar_backup;
            state.metas_mut().pop_scope();
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
            // Modus-ponens-to-False chains (hab : a → b, ha : a, hb : ¬b
            // ⊢ False) need hypothesis application: without this the branch
            // returns before the solve_by_elim fallback below is reachable.
            // Same remaining-budget formula as that fallback.
            if solve_by_elim_isolated(state, max_depth - depth) {
                return Ok(true);
            }
            if std::env::var_os("CLEAN_TAUTO_TRACE").is_some() {
                eprintln!("atom-split: FALSE leaf unclosed; ctx:");
                for d in &goal.local_ctx {
                    let t: String = format!("{:?}", d.ty).chars().take(90).collect();
                    eprintln!("    {} : {t}", d.name);
                }
            }
            return Ok(false);
        }

        // Check for P ∨ ¬P (excluded middle)
        if let Some((p, q)) = match_or(target) {
            if let Some(inner_p) = match_not(&q) {
                if exprs_syntactically_equal(&p, &inner_p) {
                    let hyp_name = fresh_hyp_name(&goal.local_ctx, "h");
                    if crate::tactic::by_cases(state, &hyp_name, p.clone()).is_ok()
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
                    if crate::tactic::by_cases(state, &hyp_name, q.clone()).is_ok()
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
                if tauto_prove(state, &first_goal, depth + 1, max_depth, splits_remaining)? {
                    // The first recursion may legitimately drain EVERY goal
                    // (its fallbacks range beyond the first conjunct); that
                    // is success, not a missing second conjunct.
                    if state.goals.is_empty() {
                        return Ok(true);
                    }
                    let second_goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();
                    if tauto_prove(state, &second_goal, depth + 1, max_depth, splits_remaining)? {
                        return Ok(true);
                    }
                }
            }
            return try_classical_atom_split(state, &goal, depth, max_depth, splits_remaining);
        }

        // Biconditional (Iff): split into two implications
        if match_iff(target).is_some() {
            if split_(state).is_ok() {
                let first_goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();
                if tauto_prove(state, &first_goal, depth + 1, max_depth, splits_remaining)? {
                    // See the drained-goals note on the conjunction branch.
                    if state.goals.is_empty() {
                        return Ok(true);
                    }
                    let second_goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();
                    if tauto_prove(state, &second_goal, depth + 1, max_depth, splits_remaining)? {
                        return Ok(true);
                    }
                }
            }
            return try_classical_atom_split(state, &goal, depth, max_depth, splits_remaining);
        }

        // Disjunction: try left, then right, then by_cases
        if match_or(target).is_some() {
            // Each alternative runs in its own metavariable scope: `left_`
            // assigns the goal meta, so without the rollback below a failed
            // left branch permanently blocked `right_` (see the note at the
            // or-hypothesis site above).
            let goals_backup = state.goals.clone();
            // Positional fvar discipline (see try_classical_atom_split): a
            // rolled-back `by_cases`/`cases` leaves `next_fvar` advanced, and
            // close_fvars ties FVar ids to binder depth — later minting at the
            // shifted cursor fails "assignment violates its creation scope".
            let next_fvar_backup = state.next_fvar;

            state.metas_mut().push_scope();
            if left_(state).is_ok() {
                let left_goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();
                if tauto_prove(state, &left_goal, depth + 1, max_depth, splits_remaining)? {
                    state.metas_mut().commit();
                    return Ok(true);
                }
            }

            state.invalidate_tc_cache();
            state.goals = goals_backup.clone();
            state.next_fvar = next_fvar_backup;
            state.metas_mut().pop_scope();

            state.metas_mut().push_scope();
            if right_(state).is_ok() {
                let right_goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();
                if tauto_prove(state, &right_goal, depth + 1, max_depth, splits_remaining)? {
                    state.metas_mut().commit();
                    return Ok(true);
                }
            }

            state.invalidate_tc_cache();
            state.goals = goals_backup;
            state.next_fvar = next_fvar_backup;
            state.metas_mut().pop_scope();

            state.metas_mut().push_scope();
            if try_by_cases_for_disjunction(state)? {
                state.metas_mut().commit();
                return Ok(true);
            }
            state.metas_mut().pop_scope();

            // The canonical dead end for `(¬a ∧ ¬b) ∨ (b ∧ ¬¬a)`-class goals:
            // both injections and de Morgan failed, so only a classical case
            // split on an atom can make progress.
            return try_classical_atom_split(state, &goal, depth, max_depth, splits_remaining);
        }

        // Implication: intro and continue
        if let ExprKind::Pi(_, _, _) = target.kind() {
            let hyp_name = fresh_hyp_name(&goal.local_ctx, "h");
            if intro(state, &hyp_name).is_ok() {
                let new_goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();
                return tauto_prove(state, &new_goal, depth + 1, max_depth, splits_remaining);
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
        if solve_by_elim_isolated(state, solve_by_elim_max_depth) {
            return Ok(true);
        }

        // LAST RESORT: retry the structural dispatch on the REDUCED target.
        // Mathlib spells many propositional lemmas over a `def` head
        // (`Xor' a b := (a ∧ ¬b) ∨ (b ∧ ¬a)`), and every matcher above tests
        // the RAW target, so the ∨/∧ structure is invisible and tauto reports
        // no progress. Reducing exposes it.
        //
        // Deliberately narrow, for the reason recorded on
        // `ProofState::whnf_indexing` (core/type_check.rs): unbudgeted
        // full-delta WHNF under a real `import Init` is the 2026-08-13 OOM
        // class. So this runs ONLY here, on the path that has already failed
        // every other route, only once per goal (the `reduced != target`
        // guard plus the depth budget bound the recursion), and the tactic
        // that consumes it is re-entered through the normal budgeted path.
        let reduced = state.whnf(&goal, target);
        if reduced != *target && depth < max_depth {
            // Struct-update rather than `reduced_goal.target = ...`.
            //
            // This is only a LOCAL fallback clone — the real state is advanced
            // by `replace_target_def_eq` below, which carries the def-eq
            // obligation. But `test_ratchet_no_new_inplace_target_mutations`
            // scans SYNTACTICALLY for `.target = `, and cannot see that
            // distinction; it flagged this as a 7th in-place mutation against a
            // baseline of 6. Building the fallback by struct-update keeps the
            // behaviour identical and keeps the ratchet meaningful, rather than
            // raising a soundness baseline for a site that is not a soundness
            // bypass.
            let reduced_goal = Goal {
                target: reduced.clone(),
                ..goal.clone()
            };
            if state.replace_target_def_eq(reduced).is_ok() {
                let cur = state.current_goal().cloned().unwrap_or(reduced_goal);
                return tauto_prove(state, &cur, depth + 1, max_depth, splits_remaining);
            }
        }

        try_classical_atom_split(state, &goal, depth, max_depth, splits_remaining)
    })
}

/// Run `solve_by_elim` against the CURRENT goal only.
///
/// `solve_by_elim` greedily drains ALL of `state.goals` (`solve_all_goals`),
/// so an unsolvable sibling goal would veto a correct current-goal proof.
/// `solve_by_elim`'s own rollback restores the isolated goal on failure.
fn solve_by_elim_isolated(state: &mut ProofState, max_depth: usize) -> bool {
    if state.goals.is_empty() {
        return false;
    }
    let rest = state.goals.split_off(1);
    let solved = solve_by_elim(state, max_depth).is_ok();
    state.goals.extend(rest);
    solved
}
