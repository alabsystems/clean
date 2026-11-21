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
use super::{
    is_trivial_equality, is_true_const, simp, simp_at_closed_goal, simp_at_fvar_with_config,
    simp_at_fvar_with_lemmas,
};
use crate::tactic::display::no_progress_with_goal;
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
/// extending the config with local propositional hypotheses as rewrite lemmas.
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
    let (rewrite_hyps, other_hyps) = partition_simp_all_hypotheses(&goal);
    let erased: HashSet<clean_kernel::FVarId> = config
        .exclude
        .iter()
        .filter_map(|name| {
            goal.local_ctx
                .iter()
                .rev()
                .find(|decl| crate::tactic::pattern::names::hypothesis_named(&decl.name, name))
                .map(|decl| decl.fvar)
        })
        .collect();

    // Context rules carry exact local proofs, including older hidden locals.
    // Keep these locals stable until the other hypotheses and target consume
    // them; rebuilding later reads any replacements by their current identity.
    // Simplify non-equality hypotheses via simp_at_with_lemmas, which uses
    // proper proof terms (fresh fvar + let-binding + Eq.subst/identity cast).
    // This replaces the old in-place mutation which reused fvar IDs.
    // A hypothesis simplified to `False` closes the goal (`hyp_false`, Lean's
    // `applySimpResult`); nothing is left to simplify then, and the next name
    // would be looked up in an unrelated goal.
    let open_goals = state.goals.len();
    for &hyp in other_hyps.iter().filter(|hyp| !erased.contains(*hyp)) {
        // Rebuild from current local identities after each replacement. A
        // proposition must not discharge itself and erase its own evidence.
        let mut hyp_config = simp_all_rewrite_config(state, &config, Some(hyp), &erased);
        hyp_config.use_hypotheses = false;
        let rewrite_simp_lemmas = collect_simp_lemmas_cached(state, &hyp_config);
        if simp_at_fvar_with_lemmas(state, hyp, &hyp_config, &rewrite_simp_lemmas).is_ok() {
            made_progress = true;
            if simp_at_closed_goal(state, open_goals) {
                return Ok(());
            }
        }
    }

    // Use the full `simp` function for target simplification so we get the
    // iterative rewrite loop and transitivity chain support for equality goals
    // (e.g. `a = c` with lemmas `a = b` and `b = c`). Set `only_simplify` to
    // skip closers here — simp_all has its own closer phase below.
    {
        let mut target_config = simp_all_rewrite_config(state, &config, None, &erased);
        target_config.only_simplify = true;
        if simp(state, target_config).is_ok() {
            made_progress = true;
            if simp_at_closed_goal(state, open_goals) {
                return Ok(());
            }
        }
    }

    // After the rest of the context has consumed the original equality proofs,
    // simplify the equality hypotheses themselves with a fresh local-lemma set.
    let mut changed_equality = false;
    for &hyp in rewrite_hyps.iter().filter(|hyp| !erased.contains(*hyp)) {
        // An equality cannot simplify its own proposition to True using its
        // own proof. That would discard a contradictory hypothesis before
        // `reduceCtorEq` can derive False from it. Exclude by identity, so a
        // different local with the same displayed name remains usable.
        let mut hyp_config = simp_all_rewrite_config(state, &config, Some(hyp), &erased);
        hyp_config.use_hypotheses = false;
        let simp_lemmas = collect_simp_lemmas_cached(state, &hyp_config);
        if simp_at_fvar_with_lemmas(state, hyp, &hyp_config, &simp_lemmas).is_ok() {
            made_progress = true;
            changed_equality = true;
            if simp_at_closed_goal(state, open_goals) {
                return Ok(());
            }
        }
    }

    // Constructor injectivity can turn one equality into several local rules.
    // The target's first pass used the original constructor equality. Give
    // it the projections of the simplified hypothesis as well.
    if changed_equality {
        let mut target_config = simp_all_rewrite_config(state, &config, None, &erased);
        target_config.only_simplify = true;
        if simp(state, target_config).is_ok() && simp_at_closed_goal(state, open_goals) {
            return Ok(());
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

        if erased.is_empty() && try_tactic_preserving_state(state, assumption) {
            return Ok(());
        }

        let may_use_trivial = erased.is_empty()
            || state
                .current_goal()
                .is_some_and(|goal| is_true_const(&goal.target));
        if may_use_trivial && try_tactic_preserving_state(state, trivial) {
            return Ok(());
        }
    }

    if made_progress {
        Ok(())
    } else {
        Err(no_progress_with_goal(state, "simp_all"))
    }
}

/// Keep automatic context traversal independent of user-facing spellings.
fn partition_simp_all_hypotheses(
    goal: &Goal,
) -> (Vec<clean_kernel::FVarId>, Vec<clean_kernel::FVarId>) {
    let mut rewrite_hyps = Vec::new();
    let mut other_hyps = Vec::new();
    for decl in &goal.local_ctx {
        if match_equality(&decl.ty).is_ok() {
            rewrite_hyps.push(decl.fvar);
        } else {
            other_hyps.push(decl.fvar);
        }
    }
    (rewrite_hyps, other_hyps)
}

fn simp_all_rewrite_config(
    state: &ProofState,
    config: &SimpConfig,
    excluded: Option<clean_kernel::FVarId>,
    erased: &HashSet<clean_kernel::FVarId>,
) -> SimpConfig {
    let mut config = config.clone();
    if let Some(goal) = state.current_goal() {
        for decl in &goal.local_ctx {
            if Some(decl.fvar) != excluded && !erased.contains(&decl.fvar) {
                config
                    .aesop_simp_lemmas
                    .extend(super::lemmas::collect_local_extra_lemma_for_decl(
                        state, goal, decl,
                    ));
            }
        }
    }
    config
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
    let trivial_fvars: Vec<clean_kernel::FVarId> = current_goal
        .local_ctx
        .iter()
        .filter(|d| is_true_const(&d.ty) || is_trivial_equality(&d.ty))
        .map(|d| d.fvar)
        .collect();
    if trivial_fvars.is_empty() {
        return false;
    }
    if let Some(goal_mut) = state.goals.front_mut() {
        goal_mut
            .local_ctx
            .retain(|d| !trivial_fvars.contains(&d.fvar));
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
    simp_at_all_with_config(state, SimpConfig::new())
}

/// [`simp_at_all`] with the caller's lemma list — `simp [foo, *] at *`.
///
/// The `Wildcard` arm of the `simp` handler used to call [`simp_at_all`] and
/// therefore DROPPED the whole lemma list: `simp only [h] at *` ran the full
/// default simp set at every location and never saw `h`, silently. Lean
/// builds ONE `Simp.Context` in `mkSimpContext` and `simpLocation` hands it to
/// every location, wildcard included.
///
/// `SimpConfig::new()` is exactly what the two call sites used before
/// (`simp_at` is `simp_at_with_config(.., SimpConfig::new())` and
/// `simp_default` is `simp(.., SimpConfig::new())`), so the no-list spelling
/// is unchanged.
///
/// REQUIRES: `state.goals` is non-empty
/// ENSURES: On Ok, hypotheses are simplified independently (no cross-rewriting)
/// ENSURES: a hypothesis is never rewritten by its OWN `[*]` rule
///   (`exclude_hypothesis`, Lean's `simpGoal`) — the same discipline
///   `simp [*] at h` carries
pub(crate) fn simp_at_all_with_config(state: &mut ProofState, config: SimpConfig) -> TacticResult {
    if state.goals.is_empty() {
        return Err(TacticError::NoGoals);
    }

    let mut made_progress = false;
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();

    // Match Lean 4 `simpLocation Location.wildcard`: only simplify
    // nondependent propositional hypotheses and skip let-bindings entirely.
    let hypotheses = collect_simp_at_all_hypotheses(state, &goal)?;

    // Simp each hypothesis independently — no cross-rewriting
    let open_goals = state.goals.len();
    for hyp in hypotheses {
        if simp_at_fvar_with_config(state, hyp, config.clone()).is_ok() {
            made_progress = true;
            // `h : False` closed the goal (`hyp_false`): `simp at *` is done.
            if simp_at_closed_goal(state, open_goals) {
                return Ok(());
            }
        }
    }

    // Simp the goal (includes rfl/assumption closers)
    if simp(state, config).is_ok() {
        return Ok(());
    }

    if made_progress {
        Ok(())
    } else {
        Err(no_progress_with_goal(state, "simp at *"))
    }
}

fn collect_simp_at_all_hypotheses(
    state: &ProofState,
    goal: &Goal,
) -> Result<Vec<clean_kernel::FVarId>, TacticError> {
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
        .map(|decl| decl.fvar)
        .collect())
}

fn remove_candidate_dependencies(candidates: &mut HashSet<clean_kernel::FVarId>, expr: &Expr) {
    if !expr.has_fvar_quick() {
        return;
    }

    let deps = crate::tactic::hypothesis::collect_fvars(expr);
    candidates.retain(|fvar| !deps.contains(fvar));
}

#[cfg(test)]
mod shadow_tests {
    use super::*;
    use crate::tactic::LocalDecl;
    use clean_kernel::{env::Environment, FVarId, Name};

    #[test]
    fn removing_trivial_hypothesis_preserves_nontrivial_namesake() {
        let name = clean_parser::SurfaceName::generated_path("h");
        let mut state = ProofState::with_context(
            Environment::new(),
            Expr::const_(Name::from_string("True"), vec![]),
            vec![
                LocalDecl {
                    binder_info: Default::default(),
                    fvar: FVarId::new(0),
                    name: name.clone(),
                    ty: Expr::const_(Name::from_string("True"), vec![]),
                    value: None,
                },
                LocalDecl {
                    binder_info: Default::default(),
                    fvar: FVarId::new(1),
                    name,
                    ty: Expr::const_(Name::from_string("P"), vec![]),
                    value: None,
                },
            ],
        );
        assert!(remove_trivial_hypotheses(&mut state));
        let ctx = &state.current_goal().expect("goal").local_ctx;
        assert_eq!(ctx.len(), 1);
        assert_eq!(ctx[0].fvar, FVarId::new(1));
    }
}
