// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The bounded classical atom split reached only at a dead end of the
//! `tauto` tableau search, plus the candidate collection that feeds it.
//! Split out of `tauto/mod.rs` for file size.

// Everything `tauto/mod.rs` imports is in scope here through the glob, so the
// moved bodies resolve exactly the names they resolved before the split.
use super::search::tauto_prove;
use super::*;

/// Bounded classical fallback: `by_cases` on a propositional atom of the
/// goal, then retry both branches. Reached only after every structural route
/// dead-ended, so splitting stays the most expensive option tried last.
///
/// REQUIRES: `state` has at least one goal.
/// ENSURES: On Ok(true), the current goal is closed and the split's
///   metavariable scope is committed. On Ok(false), goals and metavariable
///   state are restored to entry; budget spent on failed splits stays spent
///   (the countdown bounds total `by_cases` executions, not successes).
pub(super) fn try_classical_atom_split(
    state: &mut ProofState,
    goal: &Goal,
    depth: usize,
    max_depth: usize,
    splits_remaining: &mut usize,
) -> Result<bool, TacticError> {
    if std::env::var_os("CLEAN_TAUTO_TRACE").is_some() {
        eprintln!(
            "atom-split: enter depth={depth} budget={}",
            *splits_remaining
        );
    }

    if depth >= max_depth || *splits_remaining == 0 {
        return Ok(false);
    }
    let trace = std::env::var_os("CLEAN_GRIND_TRACE").is_some();
    for atom in collect_split_atoms(state, goal, MAX_ATOM_CANDIDATES) {
        if *splits_remaining == 0 {
            return Ok(false);
        }
        if trace {
            eprintln!("tauto-trace: atom-split depth={depth} splits_remaining={splits_remaining}");
        }
        // Same rollback discipline as the or-hypothesis site in tauto_prove:
        // goals backup + metavariable scope, committed only when BOTH
        // branches close (see the SOUNDNESS note there). The split itself is
        // sound without new axioms: `by_cases` builds a real
        // `Or.rec (Classical.em p)` term, kernel-rechecked at add_decl.
        let goals_backup = state.goals.clone();
        // OWNED scope: a callee inside the branch recursions can pop an
        // ordinary marker that is not its own (measured: after one rolled-back
        // split, `pop_scope` returned true yet the goal meta stayed ASSIGNED —
        // the marker was stolen mid-recursion, the final pop reverted only a
        // suffix, and every later `by_cases` failed with scope-violation
        // errors). Closing by token rposition-matches THIS marker and pops
        // through anything a callee left above it.
        let scope_token = state.metas_mut().push_owned_scope();
        // Positional fvar discipline: `close_fvars` ties FVar ids to binder
        // depth (FVar(base+k) must sit under k+1 binders), and `by_cases`
        // mints its hypothesis fvar at `next_fvar` — which the meta rollback
        // does NOT rewind. Without restoring it, attempt #2's hAtom lands at
        // base+1 under a depth-1 lambda and every subsequent `by_cases` dies
        // with "assignment violates its creation scope" (measured: the ids in
        // the trace shift by one per attempt). Goals and metas roll back
        // through their own mechanisms; the fvar cursor must roll back here.
        let next_fvar_backup = state.next_fvar;
        let h_name = fresh_hyp_name(&goal.local_ctx, "hAtom");
        // `by_cases` verifies Prop-ness itself and fails state-unchanged; an
        // Err here means skip to the next candidate.
        let atom_dbg: String = if std::env::var_os("CLEAN_TAUTO_TRACE").is_some() {
            format!("{atom:?}").chars().take(80).collect()
        } else {
            String::new()
        };
        let bc = crate::tactic::by_cases(state, &h_name, atom);
        if std::env::var_os("CLEAN_TAUTO_TRACE").is_some() {
            match &bc {
                Ok(()) => eprintln!("atom-split: by_cases OK on {atom_dbg}"),
                Err(e) => {
                    let t: String = format!("{e:?}").chars().take(110).collect();
                    eprintln!("atom-split: by_cases ERR on {atom_dbg}: {t}");
                }
            }
        }
        if bc.is_ok() {
            // Consumed on EXECUTION, deliberately not restored on failure.
            *splits_remaining -= 1;
            // Isolate the positive branch: greedy solve_by_elim must not
            // cross the split boundary.
            let remaining = state.goals.split_off(1);
            let pos_goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();
            let pos_ok = tauto_prove(state, &pos_goal, depth + 1, max_depth, splits_remaining)?;
            if std::env::var_os("CLEAN_TAUTO_TRACE").is_some() {
                let t: String = format!("{:?}", pos_goal.target).chars().take(80).collect();
                eprintln!(
                    "atom-split: POS branch {} target {t}",
                    if pos_ok { "OK" } else { "FAIL" }
                );
            }
            if pos_ok {
                state.goals.extend(remaining);
                if state.goals.is_empty() {
                    if state
                        .metas_mut()
                        .close_owned_scope(scope_token, false)
                        .is_err()
                    {
                        return Ok(false);
                    }
                    return Ok(true);
                }
                let neg_goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();
                let rest = state.goals.split_off(1);
                if tauto_prove(state, &neg_goal, depth + 1, max_depth, splits_remaining)? {
                    state.goals.extend(rest);
                    if state
                        .metas_mut()
                        .close_owned_scope(scope_token, false)
                        .is_err()
                    {
                        return Ok(false);
                    }
                    return Ok(true);
                }
            }
        }
        state.invalidate_tc_cache();
        state.goals = goals_backup;
        state.next_fvar = next_fvar_backup;
        let _ = state.metas_mut().close_owned_scope(scope_token, true);
        state.next_fvar = next_fvar_backup;
    }
    Ok(false)
}

/// Collect `by_cases` candidate atoms for the classical split: the leaves of
/// the goal target's propositional connective spine first, then the leaves of
/// each hypothesis type, truncated to `cap`.
fn collect_split_atoms(state: &ProofState, goal: &Goal, cap: usize) -> Vec<Expr> {
    // Instantiated hypothesis types feed the context-decided admission filter
    // in `admit_split_atom`: an atom the context has already decided is never
    // re-split, which is what terminates post-split recursion.
    let hyp_tys: Vec<Expr> = goal
        .local_ctx
        .iter()
        .map(|d| state.metas.instantiate(&d.ty))
        .collect();
    let target = state.metas.instantiate(&goal.target);
    let mut atoms = Vec::new();
    stack_safe(|| collect_atoms_in(&target, &hyp_tys, &mut atoms, cap));
    for hyp_ty in &hyp_tys {
        if atoms.len() >= cap {
            break;
        }
        stack_safe(|| collect_atoms_in(hyp_ty, &hyp_tys, &mut atoms, cap));
    }
    atoms
}

/// Connective-spine descent for `collect_split_atoms`: And/Or/Iff/Not and
/// non-dependent Pi recurse; dependent Pi stops without a leaf (an atom
/// mentioning a bound variable cannot be `by_cases`'d in the goal context);
/// anything else is a leaf candidate.
fn collect_atoms_in(expr: &Expr, hyp_tys: &[Expr], atoms: &mut Vec<Expr>, cap: usize) {
    if atoms.len() >= cap {
        return;
    }
    // Before the generic Pi arm: `match_not` claims both the App `Not p`
    // spelling and the `p → False` arrow spelling.
    if let Some(inner) = match_not(expr) {
        collect_atoms_in(&inner, hyp_tys, atoms, cap);
        return;
    }
    if let Some((p, q)) = match_and(expr)
        .or_else(|| match_or(expr))
        .or_else(|| match_iff(expr))
    {
        collect_atoms_in(&p, hyp_tys, atoms, cap);
        collect_atoms_in(&q, hyp_tys, atoms, cap);
        return;
    }
    if let ExprKind::Pi(_, dom, cod) = expr.kind() {
        if !cod.has_loose_bvar(0) {
            collect_atoms_in(dom, hyp_tys, atoms, cap);
            collect_atoms_in(cod, hyp_tys, atoms, cap);
        }
        return;
    }
    admit_split_atom(expr, hyp_tys, atoms);
}

/// Leaf admission for `collect_split_atoms`. Rejects leaves that cannot be
/// split — unassigned metas would pollute unification, True/False are
/// trivial — and leaves that make no progress: duplicates, and atoms the
/// context has already decided (some hyp is the atom or its negation), the
/// filter that makes re-splitting the same atom impossible. Prop-ness is NOT
/// pre-checked: `by_cases` verifies it and fails state-unchanged.
fn admit_split_atom(leaf: &Expr, hyp_tys: &[Expr], atoms: &mut Vec<Expr>) {
    if crate::tactic::contains_unassigned_meta(leaf) {
        return;
    }
    if is_true_const(leaf) || is_false(leaf) {
        return;
    }
    if atoms.iter().any(|a| exprs_syntactically_equal(a, leaf)) {
        return;
    }
    for hyp_ty in hyp_tys {
        if exprs_syntactically_equal(hyp_ty, leaf) {
            return;
        }
        if let Some(inner) = match_not(hyp_ty) {
            if exprs_syntactically_equal(&inner, leaf) {
                return;
            }
        }
    }
    atoms.push(leaf.clone());
}
