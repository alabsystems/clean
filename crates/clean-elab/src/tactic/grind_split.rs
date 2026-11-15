// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! grind's CASE SPLITTING: disjunction hypotheses, `ite`/`dite` conditions,
//! and the recursive closer that runs over the goals a split produces.
//!
//! Split out of `grind.rs` to keep that file under the paragon 1000-line
//! limit; everything here is private to the tactic and reached from
//! `grind_core`.

use clean_kernel::expr::ExprKind;
use clean_kernel::{Expr, Name};

use super::existential::by_cases;
use super::grind::{
    grind_core, grind_no_progress_at, grind_preprocess_with, GrindConfig, GRIND_NO_PROGRESS,
};
use super::match_or;
use super::{Goal, ProofState, TacticResult};
use crate::stack_safe;
use crate::unify::MetaState;

// ============================================================================
// Case splitting — disjunctions
// ============================================================================

/// Scan hypotheses for an `Or` disjunction and case-split on it.
///
/// Returns `Some(Ok(()))` if case-splitting succeeded and both branches closed,
/// `Some(Err(...))` if splitting was attempted but a branch failed,
/// `None` if no splittable disjunction was found.
pub(super) fn try_split_disjunction(
    state: &mut ProofState,
    config: &GrindConfig,
    depth: usize,
    splits_remaining: &mut usize,
    case_hyps: &[clean_parser::SurfaceName],
) -> Option<TacticResult> {
    let goal = state.current_goal()?.clone();

    let candidates = collect_or_hypotheses(&goal, &state.metas);
    if candidates.is_empty() {
        return None;
    }

    let mut last_error = None;
    for hyp in candidates {
        let saved_goals = state.goals.clone();
        let saved_splits_remaining = *splits_remaining;
        state.metas_mut().push_scope();

        if super::proof_manipulation::cases_fvar(state, hyp).is_err() {
            state.invalidate_tc_cache();
            state.goals = saved_goals;
            *splits_remaining = saved_splits_remaining;
            state.metas_mut().pop_scope();
            continue;
        }

        *splits_remaining = splits_remaining.saturating_sub(1);
        let result =
            close_all_goals_recursive_with(state, config, depth + 1, splits_remaining, case_hyps);

        match result {
            Ok(()) => {
                state.metas_mut().commit();
                return Some(Ok(()));
            }
            Err(e) => {
                state.invalidate_tc_cache();
                state.goals = saved_goals;
                *splits_remaining = saved_splits_remaining;
                state.metas_mut().pop_scope();
                last_error = Some(e);
            }
        }
    }

    last_error.map(Err)
}

pub(super) fn collect_or_hypotheses(goal: &Goal, metas: &MetaState) -> Vec<clean_kernel::FVarId> {
    goal.local_ctx
        .iter()
        .filter_map(|decl| {
            let ty = metas.instantiate(&decl.ty);
            match_or(&ty).map(|_| decl.fvar)
        })
        .collect()
}

// ============================================================================
// Case splitting — if-then-else
// ============================================================================

/// Scan the goal target for an `ite` condition and split on it via `by_cases`.
///
/// Returns `Some(Ok(()))` if case-splitting succeeded and both branches closed,
/// `Some(Err(...))` if splitting was attempted but a branch failed,
/// `None` if no ite condition was found.
pub(super) fn try_split_ite(
    state: &mut ProofState,
    config: &GrindConfig,
    depth: usize,
    splits_remaining: &mut usize,
    case_hyps: &[clean_parser::SurfaceName],
) -> Option<TacticResult> {
    let goal = state.current_goal()?.clone();
    let target = state.metas.instantiate(&goal.target);
    // Conditions this branch could split on, in order, minus the two kinds it
    // must not.
    //
    // ALREADY DECIDED — by one of THIS grind's own case splits. Without that
    // filter a `dite` the branch simp could not collapse — because the rewrite
    // it needs is ill-typed, or because `dif_pos`/`dif_neg` are absent — is
    // split on again at the next depth, and again, producing nine identical
    // `h_grind.N : P` hypotheses and `grind/max-depth` where one honest `no
    // progress` belongs (`dite_ne_left_iff`, `Mathlib/Logic/Basic.lean`).
    // Compared by CONDITION EXPRESSION, never by the `h_grind` name prefix:
    // legitimately nested splits on DISTINCT conditions must still nest.
    //
    // NOT A TERM HERE — a condition read out from UNDER a binder carries loose
    // bound variables and is not a term in this goal's context at all
    // (`Function.Injective.dite`'s hypothesis is exactly that shape), so it is
    // dropped rather than handed to `by_cases`, the same guard `connective.rs`
    // puts on an `ite` it wants to read.
    let candidates: Vec<Expr> = split_candidate_conditions(&goal, &state.metas, &target)
        .into_iter()
        .filter(|c| !c.has_loose_bvars())
        .filter(|c| !condition_already_decided(&goal, &state.metas, case_hyps, c))
        .collect();
    let case_name =
        clean_parser::SurfaceName::from_name(Name::anon().str("h_grind").num(depth as u64));

    // The first candidate `by_cases` ACCEPTS, not simply the first candidate.
    // The loose-bvar filter above removes the one unposable shape that is
    // MEASURED to occur; this loop is the defensive half for any other refusal
    // (a non-`Prop` argument of a constant that merely shares `ite`'s name,
    // say) and is not claimed to be witnessed by a row. A branch that fails to
    // CLOSE still ends the search here, exactly as before — only a candidate
    // this goal cannot pose advances the cursor.
    let mut posed = None;
    for condition in candidates {
        if std::env::var_os("CLEAN_GRIND_TRACE").is_some() {
            let shown: String = format!("{condition:?}").chars().take(80).collect();
            eprintln!("grind-trace: split depth={depth} on {shown}");
        }
        let attempt_goals = state.goals.clone();
        state.metas_mut().push_scope();
        if by_cases(state, &case_name, condition).is_ok() {
            posed = Some(attempt_goals);
            break;
        }
        state.invalidate_tc_cache();
        state.goals = attempt_goals;
        state.metas_mut().pop_scope();
    }
    // Restored on every exit below, so it is the goal list as it stood before
    // the split that was actually posed.
    let saved_goals = posed?;

    *splits_remaining = splits_remaining.saturating_sub(1);

    // Try to close both branches. Each branch's preprocessing simp gets the
    // case hypothesis (`c` / `¬c`), which the `ite`/`dite` collapse needs to
    // take the branch: Lean's grind asserts it into the E-graph.
    // EVERY case hypothesis in scope, not just this split's. A nested split
    // used to hand its branch only the innermost name, so the outer `ite` the
    // enclosing split had decided was no longer collapsible and the branch
    // carried an undecided-looking conditional down the recursion. Lean asserts
    // every hypothesis into one E-graph, where nothing can go out of scope.
    let mut nested_case_hyps = case_hyps.to_vec();
    nested_case_hyps.push(case_name.clone());
    let result = close_all_goals_recursive_with(
        state,
        config,
        depth + 1,
        splits_remaining,
        &nested_case_hyps,
    );

    match result {
        Ok(()) => {
            state.metas_mut().commit();
            Some(Ok(()))
        }
        Err(e) => {
            state.invalidate_tc_cache();
            state.goals = saved_goals;
            state.metas_mut().pop_scope();
            Some(Err(e))
        }
    }
}

/// Every distinct `ite`/`dite` condition in `expr`, outermost first.
///
/// Replaces the single-answer `find_ite_condition`: taking only the FIRST
/// condition is what produced the nine-deep re-split loop, because a branch
/// that has already decided that condition got it handed back again at the
/// next depth. `@ite α c inst t e` / `@dite α c inst t e` keeps the condition
/// at argument 1 with at least five arguments, exactly as Lean's
/// `isIte`/`isDIte` require (`Lean/Meta/Tactic/Grind/Split.lean`).
pub(super) fn collect_ite_conditions(expr: &Expr) -> Vec<Expr> {
    let mut out = Vec::new();
    stack_safe(|| collect_ite_conditions_inner(expr, &mut out));
    out
}

fn collect_ite_conditions_inner(expr: &Expr, out: &mut Vec<Expr>) {
    match expr.kind() {
        ExprKind::App(f, a) => {
            let head = expr.get_app_fn();
            let args = expr.get_app_args();
            if let ExprKind::Const(name, _) = head.kind() {
                let name_str = name.to_string();
                if (name_str == "ite" || name_str == "dite") && args.len() >= 5 {
                    let condition = args[1].clone();
                    if !out.contains(&condition) {
                        out.push(condition);
                    }
                }
            }
            collect_ite_conditions_inner(f, out);
            collect_ite_conditions_inner(a, out);
        }
        ExprKind::Lam(_, dom, body) | ExprKind::Pi(_, dom, body) => {
            collect_ite_conditions_inner(dom, out);
            collect_ite_conditions_inner(body, out);
        }
        ExprKind::Let(_, ty, val, body, _) => {
            collect_ite_conditions_inner(ty, out);
            collect_ite_conditions_inner(val, out);
            collect_ite_conditions_inner(body, out);
        }
        ExprKind::MData(_, inner) | ExprKind::Proj(_, _, inner) => {
            collect_ite_conditions_inner(inner, out);
        }
        _ => {}
    }
}

/// Conditions worth splitting on: the target's first, then any a HYPOTHESIS
/// carries.
///
/// `try_split_ite` read `goal.target` only, so `Function.Injective.dite` —
/// whose `dite` arrives in a hypothesis, with no `rcases em …` in front of it
/// (Mathlib/Logic/Function/Basic.lean:136-137 is a bare `fun x₁ x₂ h => by
/// grind`) — had nothing to split on at all. Target conditions stay FIRST:
/// splitting the goal is what the previously-measured rows need, and
/// reordering would change which branch grind explores on every one of them.
pub(super) fn split_candidate_conditions(
    goal: &Goal,
    metas: &MetaState,
    target: &Expr,
) -> Vec<Expr> {
    let mut candidates = collect_ite_conditions(target);
    for decl in &goal.local_ctx {
        for condition in collect_ite_conditions(&metas.instantiate(&decl.ty)) {
            if !candidates.contains(&condition) {
                candidates.push(condition);
            }
        }
    }
    candidates
}

/// Has one of THIS grind's own case splits already decided `condition`?
///
/// `by_cases` pushes `h : c` in the positive branch and `h : c → False` in the
/// negative one (`existential::by_cases` builds the negation as a `Pi`, not as
/// an `Not` application), so both spellings are checked.
///
/// SCOPE is `case_hyps` — the `h_grind.*` names the splitter itself minted —
/// and NOT the whole local context, which is what the guard first read.
/// Reading the whole context made an ORDINARY hypothesis block the split:
/// `(hP : P) ⊢ (if P then a else b) = a` was refused outright, because `hP`
/// decides `P` while nothing hands `hP` to the preprocessing simp (only
/// `case_hyps` reach `extra_lemmas`), so the `ite` was never collapsed either.
/// Pinned Lean v4.30.0-rc2 closes that goal. Splitting on it is safe and
/// bounded: the positive branch gets `h_grind.N : P`, which IS a case
/// hypothesis, so a second split on the same condition is still refused, and
/// the negative branch closes by contradiction against `hP`.
pub(super) fn condition_already_decided(
    goal: &Goal,
    metas: &MetaState,
    case_hyps: &[clean_parser::SurfaceName],
    condition: &Expr,
) -> bool {
    let false_c = Expr::const_(Name::from_string("False"), vec![]);
    goal.local_ctx
        .iter()
        .filter(|decl| case_hyps.contains(&decl.name))
        .any(|decl| {
            let ty = metas.instantiate(&decl.ty);
            if ty == *condition {
                return true;
            }
            match ty.kind() {
                // `c → False`, the `by_cases` negative branch.
                ExprKind::Pi(_, dom, body) => {
                    dom.as_ref() == condition && body.as_ref() == &false_c
                }
                // `Not c`, the surface spelling.
                ExprKind::App(f, a) => {
                    matches!(f.kind(), ExprKind::Const(n, _) if n.to_string() == "Not")
                        && a.as_ref() == condition
                }
                _ => false,
            }
        })
}

// ============================================================================
// Recursive goal closing
// ============================================================================

/// Attempt to close every current goal by running the grind core on each,
/// with `case_hyps` naming the case hypotheses in scope (a case split's
/// `h : c` / `h : ¬c`) for the preprocessing simp to rewrite with.
///
/// REQUIRES: `state` has one or more goals.
/// ENSURES: On `Ok(())`, all goals are closed.
/// ENSURES: On `Err`, at least one goal could not be closed.
pub(super) fn close_all_goals_recursive_with(
    state: &mut ProofState,
    config: &GrindConfig,
    depth: usize,
    splits_remaining: &mut usize,
    case_hyps: &[clean_parser::SurfaceName],
) -> TacticResult {
    // Process each goal in sequence. After closing goal 0, goal 1 becomes goal 0.
    let max_goals = state.goals.len();
    for _ in 0..max_goals {
        if state.is_complete() {
            return Ok(());
        }

        // Preprocess this branch
        let before = state.goals.len();
        if config.use_simp {
            grind_preprocess_with(state, config, case_hyps);
        }

        if state.is_complete() {
            return Ok(());
        }

        // Preprocessing CLOSED this goal: the front goal is now the next
        // branch, which must be preprocessed too before the core sees it. The
        // core used to run on it directly, so after a split the negative
        // branch never met its case hypothesis and grind re-split it until
        // max depth (measured 2026-09-12 with CLEAN_GRIND_TRACE).
        if state.goals.len() < before {
            continue;
        }

        // Recurse
        grind_core(state, config, depth, splits_remaining, case_hyps)?;
    }

    if state.is_complete() {
        Ok(())
    } else {
        Err(grind_no_progress_at(state, GRIND_NO_PROGRESS))
    }
}

// ============================================================================
// E-matching helpers
// ============================================================================

/// Collect rewrite-eligible equality hypotheses from the local context.
///
/// Returns pairs `(lhs, rhs)` from hypotheses of the form `lhs = rhs`.
/// Used by CC and the automation engine E-matching passes.
// Staged Lean4-parity scaffold: kept alive by its cfg(test) companion, awaiting
// production wiring — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[cfg_attr(not(test), allow(dead_code))]
pub(super) fn collect_eq_hypotheses(goal: &Goal, metas: &MetaState) -> Vec<(Expr, Expr)> {
    goal.local_ctx
        .iter()
        .filter_map(|decl| {
            let ty = metas.instantiate(&decl.ty);
            super::match_eq_simple(&ty)
        })
        .collect()
}
