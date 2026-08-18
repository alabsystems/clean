// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `simp_all` and `simp_at_all` tactics: simplify all hypotheses and the goal.
//!
//! `simp_all` uses cross-hypothesis rewriting and removes trivial hypotheses.
//! `simp_at_all` simplifies each hypothesis independently (Lean 4 `simp at *`).
//!
//! Extracted from `simp/mod.rs` for file size enforcement (#307).

use std::collections::HashSet;

use super::cache::collect_simp_lemmas_cached;
use super::types::SimpConfig;
use super::{is_trivial_equality, is_true_const, simp_at, simp_at_with_lemmas, simp_default};
use clean_kernel::Expr;

use crate::tactic::{
    assumption, match_equality, rfl, trivial, try_tactic_preserving_state, Goal, ProofState,
    TacticError, TacticResult,
};

/// Simplify all hypotheses and the goal.
///
/// `simp_all` applies simplification to both the hypotheses in the local context
/// and the goal. Hypotheses can be used as rewrite lemmas for each other and
/// for the goal. Trivial hypotheses (like `True` or `a = a`) are removed.
///
/// # Example
/// ```text
/// -- h1 : n + 0 = n
/// -- h2 : m * 1 = m
/// -- Goal: n + 0 = m * 1
/// simp_all
/// -- h1 : n = n (simplified, removed as trivial)
/// -- h2 : m = m (simplified, removed as trivial)
/// -- Goal closed by rfl
/// ```
///
/// # Errors
/// - `NoGoals` if there are no goals
/// - `Other` if simplification makes no progress
///
/// # Contract
///
/// REQUIRES: `state.goals` is non-empty
/// ENSURES: On Ok, both hypotheses and the goal target are simplified
/// ENSURES: On Ok, trivially-true hypotheses (e.g., `n = n`) may be removed from the context
/// ENSURES: On Err(NoGoals), state is unchanged
pub fn simp_all(state: &mut ProofState) -> TacticResult {
    simp_all_with_config(state, SimpConfig::new())
}

/// Simplify all hypotheses and the goal using a caller-supplied config.
///
/// This is the config-aware entrypoint that preserves caller-supplied fields
/// (`aesop_simp_lemmas`, `exclude`, `max_steps`, `only_simplify`) while
/// extending the config with local equality hypotheses as rewrite lemmas.
/// Part of #1867.
pub(crate) fn simp_all_with_config(state: &mut ProofState, mut config: SimpConfig) -> TacticResult {
    if state.goals.is_empty() {
        return Err(TacticError::NoGoals);
    }

    // Part of #3518: resolve Definition-kind `extra_lemmas` into unfold_defs
    // before hypothesis partitioning so `simp_all [foo]` also delta-unfolds
    // `foo` in both hypotheses and the goal target.
    super::seed_unfold_defs_from_extras(state, &mut config);
    super::lemmas::seed_unfold_defs_from_simp_defs(state, &mut config);

    let mut made_progress = false;

    // Build config with hypotheses as extra lemmas, extending the caller's
    // config rather than replacing it.
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();
    let (config, rewrite_hyp_names, other_hyp_names) = partition_simp_all_hypotheses(&goal, config);

    // Keep equality hypotheses stable while they are still needed as rewrite
    // lemmas for the rest of the context and the target.
    let rewrite_simp_lemmas = collect_simp_lemmas_cached(state, &config);

    // Simplify non-equality hypotheses via simp_at_with_lemmas, which uses
    // proper proof terms (fresh fvar + let-binding + Eq.subst/identity cast).
    // This replaces the old in-place mutation which reused fvar IDs.
    for hyp_name in &other_hyp_names {
        if simp_at_with_lemmas(state, hyp_name, &config, &rewrite_simp_lemmas).is_ok() {
            made_progress = true;
        }
    }

    // Use the full `simp` function for target simplification so we get the
    // iterative rewrite loop and transitivity chain support for equality goals
    // (e.g. `a = c` with lemmas `a = b` and `b = c`). Set `only_simplify` to
    // skip closers here — simp_all has its own closer phase below.
    {
        let mut target_config = config.clone();
        target_config.only_simplify = true;
        if super::simp(state, target_config).is_ok() {
            made_progress = true;
        }
    }

    // After the rest of the context has consumed the original equality proofs,
    // simplify the equality hypotheses themselves with a fresh local-lemma set.
    for hyp_name in &rewrite_hyp_names {
        let simp_lemmas = collect_simp_lemmas_cached(state, &config);
        if simp_at_with_lemmas(state, hyp_name, &config, &simp_lemmas).is_ok() {
            made_progress = true;
        }
    }

    if remove_trivial_hypotheses(state) {
        made_progress = true;
    }

    if !config.only_simplify {
        // Part of #2474: wrap each closer in try_tactic_preserving_state to
        // prevent failed tactics from leaking partial state mutations to
        // subsequent branches.
        if try_tactic_preserving_state(state, rfl) {
            return Ok(());
        }

        if try_tactic_preserving_state(state, assumption) {
            return Ok(());
        }

        if try_tactic_preserving_state(state, trivial) {
            return Ok(());
        }
    }

    if made_progress {
        Ok(())
    } else {
        Err(TacticError::NoProgress {
            tactic: "simp_all".into(),
        })
    }
}

/// Split hypotheses into local rewrite lemmas and everything else.
///
/// Extends the caller's config with local equality hypothesis names rather
/// than constructing a fresh `SimpConfig::new()`. This preserves
/// `aesop_simp_lemmas` and other caller-supplied fields. Part of #1867.
fn partition_simp_all_hypotheses(
    goal: &Goal,
    mut config: SimpConfig,
) -> (SimpConfig, Vec<String>, Vec<String>) {
    let mut rewrite_hyp_names = Vec::new();
    let mut other_hyp_names = Vec::new();
    for decl in &goal.local_ctx {
        if match_equality(&decl.ty).is_ok() {
            config.extra_lemmas.push(decl.name.clone());
            rewrite_hyp_names.push(decl.name.clone());
        } else {
            other_hyp_names.push(decl.name.clone());
        }
    }
    (config, rewrite_hyp_names, other_hyp_names)
}

/// Remove trivial hypotheses (`True`, `a = a`) from the current goal context.
///
/// REQUIRES: `state.goals` is non-empty
/// ENSURES: Returns `true` iff at least one hypothesis was removed
/// ENSURES: Removed hypotheses are provably true (soundness preserved)
fn remove_trivial_hypotheses(state: &mut ProofState) -> bool {
    let Some(current_goal) = state.current_goal() else {
        return false;
    };
    let trivial_names: Vec<String> = current_goal
        .local_ctx
        .iter()
        .filter(|d| is_true_const(&d.ty) || is_trivial_equality(&d.ty))
        .map(|d| d.name.clone())
        .collect();
    if trivial_names.is_empty() {
        return false;
    }
    if let Some(goal_mut) = state.goals.front_mut() {
        goal_mut
            .local_ctx
            .retain(|d| !trivial_names.contains(&d.name));
        state.invalidate_tc_cache();
    }
    true
}

/// Simplify all hypotheses independently and then the goal (`simp at *` semantics).
///
/// Unlike `simp_all`, this does NOT use equality hypotheses as rewrite lemmas
/// for other hypotheses (no cross-rewriting) and does NOT remove trivial
/// hypotheses. Each hypothesis is simplified using only the global simp lemma
/// set, matching Lean 4's `simpLocation` with `Location.wildcard`.
///
/// # Errors
/// - `NoGoals` if there are no goals
/// - `NoProgress` if neither any hypothesis nor the goal was simplified
///
/// REQUIRES: `state.goals` is non-empty
/// ENSURES: On Ok, hypotheses are simplified independently (no cross-rewriting)
/// ENSURES: On Ok, trivial hypotheses are NOT removed (unlike `simp_all`)
pub fn simp_at_all(state: &mut ProofState) -> TacticResult {
    if state.goals.is_empty() {
        return Err(TacticError::NoGoals);
    }

    let mut made_progress = false;
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();

    // Match Lean 4 `simpLocation Location.wildcard`: only simplify
    // nondependent propositional hypotheses and skip let-bindings entirely.
    let hyp_names = collect_simp_at_all_hypotheses(state, &goal)?;

    // Simp each hypothesis independently — no cross-rewriting
    for name in &hyp_names {
        if simp_at(state, name).is_ok() {
            made_progress = true;
        }
    }

    // Simp the goal (includes rfl/assumption closers)
    if simp_default(state).is_ok() {
        return Ok(());
    }

    if made_progress {
        Ok(())
    } else {
        Err(TacticError::NoProgress {
            tactic: "simp at *".into(),
        })
    }
}

fn collect_simp_at_all_hypotheses(
    state: &ProofState,
    goal: &Goal,
) -> Result<Vec<String>, TacticError> {
    let mut candidates = HashSet::new();

    for decl in &goal.local_ctx {
        remove_candidate_dependencies(&mut candidates, &state.metas.instantiate(&decl.ty));
        if let Some(value) = &decl.value {
            remove_candidate_dependencies(&mut candidates, &state.metas.instantiate(value));
        }

        if decl.value.is_none() && state.infer_type(goal, &decl.ty)?.is_prop() {
            candidates.insert(decl.fvar);
        }
    }

    remove_candidate_dependencies(&mut candidates, &state.metas.instantiate(&goal.target));

    Ok(goal
        .local_ctx
        .iter()
        .filter(|decl| candidates.contains(&decl.fvar))
        .map(|decl| decl.name.clone())
        .collect())
}

fn remove_candidate_dependencies(candidates: &mut HashSet<clean_kernel::FVarId>, expr: &Expr) {
    if !expr.has_fvar_quick() {
        return;
    }

    let deps = crate::tactic::hypothesis::collect_fvars(expr);
    candidates.retain(|fvar| !deps.contains(fvar));
}
