// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Simplification tactics
//!
//! This module provides the `simp` family of tactics for automatic simplification
//! of expressions using rewrite lemmas, beta/eta reduction, and other normalizations.

mod all;
pub(crate) mod args;
mod binder;
mod binder_domain;
mod cache;
// Unwired roadmap prototype (2026-08-10): compiled only with its unit tests until the live
// pipeline owns it. Mirrors pattern_match_ext / error_recovery* precedent.
mod budget;
mod conditional_congr;
#[cfg(test)]
pub(crate) mod congr;
mod ctor_eq;
mod ctor_inj;
mod declared_equations;
pub(crate) use declared_equations::collect as collect_declared_equations;
mod discharge;
#[cfg(test)]
mod discharge_tests;
mod expr;
mod fixpoint;
mod hyp_false;
mod imp_false;
mod index_path_memo;
mod instance_slot;
mod iota;
pub(crate) mod lean_builtin_simprocs;
mod lean_names;
mod lemma_levels;
mod lemmas;
mod lemmas_builtin;
mod lemmas_builtin_list;
mod lemmas_local;
mod match_target;
mod matcher;
mod pattern;
mod perm;
mod proj_reduce;
pub(super) use proj_reduce::reduce_proj;
mod proof;
mod prop_lemmas;
mod rec_equations;
mod rec_equations_lifted;
mod reduce;
mod rw;
pub(crate) mod simproc;
mod simproc_builtins;
mod simproc_builtins_bool;
mod simproc_builtins_cmp;
mod squeeze;
pub(crate) mod types;
mod zeta_size;

// Re-export public API
pub use all::{simp_all, simp_at_all};
pub(crate) use all::{simp_all_with_config, simp_at_all_with_config};
pub use expr::extract_equality_from_type;
pub(crate) use rw::simp_rw_with_rules;
pub use rw::{simp_rw, simp_rw_hyps};
pub use squeeze::{squeeze_simp, squeeze_simp_and_apply, squeeze_simp_with_config};
pub use squeeze::{SqueezeSimpConfig, SqueezeSimpResult};
pub use types::{AssumptionCloser, SimpConfig, SimpIndexMode, SimpLemma};

// Re-export pub(crate) items used by other tactic modules
pub(crate) use binder::is_binder_temporary;
// For tests outside this module that need a REAL simp binder temporary.
#[cfg(test)]
pub(crate) use binder::open_binder;
pub(crate) use budget::SimpBudget;
#[cfg(test)]
pub(crate) use cache::cacheable_rebuild_count;
pub(crate) use cache::collect_simp_lemmas_cached;
pub(crate) use ctor_inj::simple_constructor_injectivity;
pub(crate) use expr::{make_eq_expr, simp_expr};
pub(crate) use hyp_false::{close_goal_by_proof_of_false, simp_at_closed_goal};
#[cfg(test)]
pub(crate) use index_path_memo::path_computation_count;
// The uncached builder stays available to tests as the goal-independent
// reference implementation; production entrypoints go through the cache.
pub(super) use lemmas::collect_local_extra_lemma_for_decl;
#[cfg(test)]
pub(crate) use lemmas::collect_simp_lemmas;
pub(crate) use lemmas::{collect_named_eq_lemmas, resolve_unfold_defs};
pub(crate) use proof::{
    mk_congr, mk_congr_arg, mk_congr_fun, mk_eq_refl_expr, mk_eq_symm_expr, mk_eq_trans_expr,
    mk_funext,
};
pub(crate) use reduce::beta_reduce;
#[cfg(test)]
pub(crate) use reduce::substitute_bvar;
pub(crate) use types::SimpLemmaSet;

// Re-export pub(crate) items used only by tests (via tactic/mod.rs #[cfg(test)] re-exports)
#[cfg(test)]
pub(crate) use reduce::{contains_bvar, eta_reduce, shift_expr};

use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Expr, ExprKind, Level};

use crate::unify::MetaState;

use super::{
    assumption, exprs_syntactically_equal, match_equality, rfl, try_tactic_preserving_state, Goal,
    LocalDecl, ProofState, TacticError, TacticResult,
};

use self::expr::{extract_eq_parts, simp_expr_budgeted, try_apply_simp_lemma_with_proof};
use self::match_target::MatchTarget;
use crate::tactic::display::no_progress_with_goal;

/// Simplification tactic that rewrites the goal using a set of lemmas.
///
/// The `simp` tactic repeatedly applies simplification lemmas to the goal
/// until no more progress can be made. It handles:
/// - Beta reduction: (λ x => e) a → e[x := a]
/// - Eta reduction: λ x => f x → f (when x not free in f)
/// - Simp lemmas: equations marked @[simp] in the environment
/// - Custom lemmas: additional lemmas passed in config
///
/// # Arguments
/// * `state` - The proof state
/// * `config` - Configuration options for simplification
///
/// # Example
/// ```text
/// -- Goal: a + 0 = a
/// simp  -- Uses Nat.add_zero : n + 0 = n
/// -- Goal closed by reflexivity
/// ```
///
/// # Errors
/// - `NoGoals` if there are no goals
/// - `Other` if simplification makes no progress and goal not closed
/// - `BudgetExceeded` if one traversal exceeded its work/growth budget
///
/// # Contract
///
/// REQUIRES: `state.goals` is non-empty
/// ENSURES: On Ok, each simplification step is justified by an `Eq.trans` proof chain
/// ENSURES: On Ok, at most `config.max_steps` rewrite steps are applied
/// ENSURES: On Err(NoGoals), state is unchanged
/// ENSURES: On Err(BudgetExceeded), state is unchanged — the traversal that
///   exceeded its budget is discarded whole, so no partial rewrite and no
///   proof over one reaches the goal (see `simp/budget.rs`)
pub fn simp(state: &mut ProofState, config: SimpConfig) -> TacticResult {
    simp_impl(state, config, None)
}

/// `simp` with an explicit [`SimpBudget`].
///
/// Test-only: the refusal fixtures need a trip to be reachable without a
/// pathological goal, and the production entry must not grow a knob that lets
/// a caller widen the budget it is being protected by.
#[cfg(test)]
pub(crate) fn simp_with_budget(
    state: &mut ProofState,
    config: SimpConfig,
    budget: SimpBudget,
) -> TacticResult {
    simp_impl(state, config, Some(budget))
}

fn simp_impl(
    state: &mut ProofState,
    mut config: SimpConfig,
    budget: Option<SimpBudget>,
) -> TacticResult {
    if state.goals.is_empty() {
        return Err(TacticError::NoGoals);
    }

    seed_unfold_defs_from_extras(state, &mut config);
    lemmas::seed_unfold_defs_from_simp_defs(state, &mut config);

    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();
    let mut current_target = goal.target.clone();
    let mut steps = 0;
    let mut made_progress = false;

    // Collect simp lemmas from environment (per-env cached: repeated simp
    // calls against an unchanged environment reuse the built set + index).
    let simp_lemmas = collect_simp_lemmas_cached(state, &config);

    // Growth/work budget: a rewrite/unfold interplay that GROWS the target
    // every pass (e.g. mutually-referencing unfold defs layering per
    // iteration) would otherwise run all `max_steps` passes over an
    // exponentially growing term — first observed as a stack overflow /
    // memory abort under real `import Init` once the typed simpExtension
    // decoder made ~10k entries live.
    //
    // This budget is now consulted INSIDE `simp_expr` as well as between
    // steps. The between-steps check could only ever see a runaway that
    // RETURNED; the measured one does not — it lives in a single traversal
    // that recurses into subterms, rewrites them larger, and pays a
    // `whnf`/`instantiate` per candidate at every node it is growing (see
    // `budget.rs` for the stack signature and the 9.95 CPU-hour check it
    // wedged). `SimpBudget::for_target` reproduces the old size formula
    // exactly, so the ceiling is unchanged; only where it is checked moved.
    let budget = budget.unwrap_or_else(|| SimpBudget::for_target(&current_target));

    // Main simplification loop — accumulate proof via Eq.trans chaining
    let mut accumulated_proof: Option<Expr> = None;
    while steps < config.max_steps {
        // The bound is per TRAVERSAL: a `simp` that legitimately needs many
        // steps must not be starved by the steps it already took.
        budget.refuel();
        let step_result = simp_expr_budgeted(
            state,
            &goal,
            &current_target,
            &simp_lemmas,
            &config,
            &budget,
        );

        // Exceeding the budget is an honest FAILURE, not a partial rewrite:
        // the traversal already unwound to the original term (`expr.rs`), and
        // returning here leaves `state` — and therefore the goal — exactly as
        // simp found it. Anything else would hand the kernel a term this
        // tactic could not justify, or silently answer a different goal.
        if let Some(detail) = budget.detail() {
            return Err(TacticError::BudgetExceeded {
                tactic: "simp".into(),
                detail,
            });
        }

        if step_result.expr != current_target {
            // Chain proofs: accumulated proves (original = current_target),
            // step_result.proof proves (current_target = step_result.expr).
            accumulated_proof = match (accumulated_proof.take(), step_result.proof) {
                (None, p) => p,
                (p, None) => p,
                (Some(p1), Some(p2)) => {
                    // Same invariant preservation as mk_eq_trans:
                    // if mk_eq_trans_expr fails, fall back to p2 to avoid silently
                    // dropping the entire accumulated proof chain to None.
                    Some(mk_eq_trans_expr(state, &goal, &p1, &p2).unwrap_or(p2))
                }
            };
            made_progress = true;
            current_target = step_result.expr;
            steps += 1;
        } else {
            break;
        }
    }

    // Transitivity support for equality goals:
    // If the goal is `a = c` and we have lemmas `a = b` and `b = c`,
    // try to rewrite the LHS iteratively: a → b → c, then close with rfl.
    // Part of #2442: produce congruence proofs for each rewrite step to
    // avoid trustedArith fallback.
    if !config.only_simplify {
        if let Some((eq_type, lhs, rhs)) = extract_eq_parts(&current_target) {
            let mut current_lhs = lhs.clone();
            let mut trans_steps = 0;
            let mut trans_proof: Option<Expr> = None;

            'trans: while trans_steps < config.max_steps && steps < config.max_steps {
                let mut rewrote = false;

                // Try to rewrite current_lhs using simp lemmas (with proof terms)
                let match_target = MatchTarget::new(state, &goal, &current_lhs);
                for lemma in simp_lemmas.candidates_for_target(state, &goal, &match_target) {
                    if let Some((new_lhs, lhs_proof)) = try_apply_simp_lemma_with_proof(
                        state,
                        &goal,
                        &match_target,
                        lemma,
                        &simp_lemmas,
                        &config,
                        &budget,
                    ) {
                        if new_lhs == current_lhs {
                            continue;
                        }
                        // See the sibling trace in `expr.rs`: fired-rewrite
                        // diagnostics for the LHS-transitivity loop.
                        if std::env::var_os("CLEAN_SIMP_REWRITE_TRACE").is_some() {
                            eprintln!(
                                "simp-rewrite(trans): lemma={} from={current_lhs:?} to={new_lhs:?}",
                                lemma.name
                            );
                        }
                        if !budget.admit(
                            &new_lhs,
                            format_args!("rewriting the left-hand side with {}", lemma.name),
                        ) {
                            // Same growth budget as the main loop: a lemma
                            // that balloons the LHS ends the search. `admit`
                            // trips the budget, and the post-loop check turns
                            // that into a refusal rather than a partial answer.
                            break 'trans;
                        }

                        // Build target-level congruence:
                        // (@Eq α current_lhs rhs) = (@Eq α new_lhs rhs)
                        let step_proof = proof::mk_eq_lhs_congr(
                            state,
                            &goal,
                            &eq_type,
                            &current_lhs,
                            &new_lhs,
                            &rhs,
                            &lhs_proof,
                        );

                        // Chain with accumulated transitivity proof
                        trans_proof = match (trans_proof.take(), step_proof) {
                            (None, p) => p,
                            (p, None) => p,
                            (Some(p1), Some(p2)) => {
                                Some(mk_eq_trans_expr(state, &goal, &p1, &p2).unwrap_or(p2))
                            }
                        };

                        current_lhs = new_lhs;
                        rewrote = true;
                        trans_steps += 1;
                        steps += 1;
                        made_progress = true;

                        // Part of #2477: stop early when rfl-closable instead
                        // of mutating goals[0].target in place (Pattern B).
                        if exprs_syntactically_equal(&current_lhs, &rhs) {
                            break 'trans;
                        }
                        break; // Try next iteration with new LHS
                    }
                }

                if !rewrote {
                    break; // No more progress possible
                }
            }

            // If we made progress, update the computed target and chain proofs
            if current_lhs != lhs {
                let new_target = make_eq_expr(&current_target, &current_lhs, &rhs);
                current_target = new_target;

                // Chain transitivity proof with the main loop's accumulated proof
                accumulated_proof = match (accumulated_proof.take(), trans_proof) {
                    (None, p) => p,
                    (p, None) => p,
                    (Some(p1), Some(p2)) => {
                        Some(mk_eq_trans_expr(state, &goal, &p1, &p2).unwrap_or(p2))
                    }
                };
            }
        }
    }

    // The transitivity loop above can also trip the budget (its `admit` call).
    // Same rule as the main loop: refuse, do not keep the partial LHS chain.
    if let Some(detail) = budget.detail() {
        return Err(TacticError::BudgetExceeded {
            tactic: "simp".into(),
            detail,
        });
    }

    if made_progress {
        // Part of #2477: use replace_target_* instead of in-place mutation.
        // In-place target mutation (Pattern B) keeps MetaId(0) but proves
        // the wrong type, breaking proof extraction.
        // Part of #2442: accumulated_proof now covers both main loop and
        // transitivity loop changes via congruence proof chaining.
        if let Some(proof) = accumulated_proof {
            state.replace_target_eq(current_target.clone(), proof)?;
        } else {
            // All changes were definitional (beta/eta) — no proof term needed.
            // Part of #2442: use def-eq replacement instead of trustedArith fallback.
            state.replace_target_def_eq(current_target.clone())?;
        }

        if !config.only_simplify
            && try_simp_closers(state, config.assumption_closer, config.legacy_ctor_closer)
        {
            return Ok(());
        }
        Ok(())
    } else {
        // No progress made - try closing with trivial tactics anyway
        if !config.only_simplify
            && try_simp_closers(state, config.assumption_closer, config.legacy_ctor_closer)
        {
            return Ok(());
        }
        Err(no_progress_with_goal(state, "simp"))
    }
}

/// After a simp rewrite step (or in lieu of progress), try to close the
/// remaining goal via reducible-transparency `rfl` or `assumption`.
///
/// Part of #2474: each closer is wrapped in `try_tactic_preserving_state` to
/// prevent a failed attempt from leaking partial state mutations to the
/// subsequent closer. Returns `true` iff one of the closers actually ran to
/// completion and closed the goal.
///
/// B15 (simp-set discipline): the reflexivity closer runs at `withReducible`
/// transparency (`close_refl_reducible`), not full def-eq. Lean's `simp` closes
/// an equality goal only when its two sides are equal at reducible transparency
/// (a bare `a = a` after simplification, or an `@[reducible]`/abbrev unfold) —
/// it does NOT unfold a semireducible `def f := e` to prove `f = e`. The old
/// full-transparency `rfl` closer silently accepted `f = e := by simp` for any
/// semireducible `f`, a proof Lean rejects with "simp made no progress".
///
/// G49: the `assumption` closer runs only under [`AssumptionCloser::On`].
/// Lean's `simp` has no such step, so the surface front ends turn it off.
fn try_simp_closers(
    state: &mut ProofState,
    assumption_closer: AssumptionCloser,
    legacy_ctor_closer: bool,
) -> bool {
    try_tactic_preserving_state(state, close_refl_reducible)
        || try_tactic_preserving_state(state, close_true_goal)
        || (assumption_closer == AssumptionCloser::On
            && try_tactic_preserving_state(state, assumption))
        || (legacy_ctor_closer
            && try_tactic_preserving_state(state, close_constructor_diseq_implication))
}

/// The subset of [`try_simp_closers`] that `dsimp` shares: reflexivity at
/// REDUCIBLE transparency, and `⊢ True`.
///
/// `dsimp` reduced its target definitionally and then abandoned it, so a goal
/// that its own normalization made self-evident was still reported unsolved.
/// Lean's `dsimp` closes exactly such a goal.
///
/// Deliberately EXCLUDES simp's `assumption` and constructor-disequality
/// closers. `dsimp` in Lean closes a goal its own definitional normalization
/// made true and nothing else; adding `assumption` here would let `dsimp`
/// discharge goals Lean's `dsimp` leaves open.
///
/// SOUNDNESS: inherited unchanged from the two closers — `close_refl_reducible`
/// gates on `is_def_eq_reducible`, strictly stronger than the full-transparency
/// check `close_goal` performs afterwards, and `close_true_goal` fires only when
/// the target WHNFs to `True`. Both submit their proof term through
/// `close_goal`, which kernel-checks it.
pub(crate) fn try_definitional_closers(state: &mut ProofState) -> bool {
    try_tactic_preserving_state(state, close_refl_reducible)
        || try_tactic_preserving_state(state, close_true_goal)
}

/// Lean's `with_reducible rfl` on the main goal, as `try`: whether it closed
/// it. A failed attempt leaves the state untouched.
pub(crate) fn try_reducible_rfl(state: &mut ProofState) -> bool {
    state.current_goal().is_some() && try_tactic_preserving_state(state, close_refl_reducible)
}

/// Close an equality goal `a = b` by reflexivity, but only when `a` and `b` are
/// definitionally equal at `withReducible` transparency (B15).
///
/// SOUNDNESS: the gate (`is_def_eq_reducible`) is strictly stronger than the
/// full-transparency check the kernel later performs at `close_goal`, so any
/// goal this closer accepts is still kernel-verified — it only REJECTS goals
/// that need a semireducible/irreducible unfold to close (which `simp` must not
/// do). On a non-`Eq` goal `match_equality` fails and we fall through to the
/// ordinary `rfl` (which is Eq-only and simply fails on non-equality goals), so
/// no non-equality closing behavior is added or removed.
fn close_refl_reducible(state: &mut ProofState) -> TacticResult {
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();
    let target = state.metas.instantiate(&goal.target);
    match match_equality(&target) {
        Ok((_ty, lhs, rhs, _lvls)) => {
            if state.is_def_eq_reducible(&goal, &lhs, &rhs) {
                rfl(state)
            } else {
                Err(TacticError::no_progress("simp"))
            }
        }
        Err(_) => rfl(state),
    }
}

/// Close a goal that simp reduced to `⊢ True` (e.g. `(n = n) = True` → `True`,
/// or `if n = n then True else False` → `True`) by `True.intro`.
///
/// SOUNDNESS: fires ONLY when the goal WHNFs to the `True` constant; the proof
/// term `True.intro : True` is kernel-checked by `close_goal`. A non-`True`
/// goal (including `False`) leaves the closer a no-op, so no false goal closes.
fn close_true_goal(state: &mut ProofState) -> TacticResult {
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();
    let target = state.whnf(&goal, &goal.target);
    if !is_true_const(&target) {
        return Err(TacticError::no_progress("simp"));
    }
    let proof = Expr::const_(Name::from_string("True.intro"), vec![]);
    state.close_goal(&goal, proof)
}

/// Close a goal of the form `(lhs = rhs) → False` (i.e. `lhs ≠ rhs` after the
/// kernel unfolds the reducible `Ne`/`Not`) when `lhs` and `rhs` are distinct
/// constructors of the same inductive, by building a `T.noConfusion` proof.
///
/// SOUNDNESS: the proof term is `fun (h : lhs = rhs) => … T.noConfusion … h`,
/// produced by the shared `build_noconfusion_ne_proof` builder and re-checked by
/// `close_goal` → kernel `add_decl`. `T.noConfusion` is the inductive's
/// auto-generated no-confusion principle (derived from `T.rec`), axiom closure
/// empty — NOT an axiom restatement. The builder fires only on genuinely
/// distinct constructors (e.g. `Nat.zero` vs `Nat.succ`); for `n ≠ n` both
/// operands WHNF to the same constructor head and the builder returns `None`,
/// so the false goal is NOT closed. Operand normalization (`whnf`) is
/// def-eq-preserving, so it can only expose the genuine constructor — a
/// mis-reduction would make the `noConfusion` application fail to type-check at
/// `add_decl` and the tactic fails closed.
fn close_constructor_diseq_implication(state: &mut ProofState) -> TacticResult {
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();
    let target = state.whnf(&goal, &goal.target);
    let ExprKind::Pi(_bi, domain, codomain) = target.kind() else {
        return Err(TacticError::no_progress("simp"));
    };

    let false_expr = Expr::const_(Name::from_string("False"), vec![]);
    let codomain_whnf = state.whnf(&goal, codomain);
    if !state.is_def_eq(&goal, &codomain_whnf, &false_expr) {
        return Err(TacticError::no_progress("simp"));
    }

    let (eq_type, lhs, rhs, eq_levels) = match_equality(domain)?;

    // Normalize each operand toward constructor / literal form. WHNF turns
    // typeclass arithmetic (`n + 1` → `Nat.succ n`) and numeric-literal wrappers
    // (`@OfNat.ofNat Nat 0 (instOfNatNat 0)` → `Lit(Nat 0)`) into the shapes the
    // shared noConfusion builder recognizes via `to_nat_view`, which the bare
    // `Const`-head check used to miss for literal `0` / numerals.
    let lhs_norm = state.whnf(&goal, &lhs);
    let rhs_norm = state.whnf(&goal, &rhs);

    // Universe level of the underlying equality (`@Eq.{u} α a b`); falls back to
    // `Sort 1` (the carrier level for Nat/Int/Bool) if absent.
    let eq_level = eq_levels
        .first()
        .cloned()
        .unwrap_or_else(|| Level::succ(Level::zero()));

    // SOUNDNESS: `build_noconfusion_ne_proof` returns `Some` only when the two
    // operands reduce to DISTINCT constructors of the SAME inductive; it returns
    // `None` for equal heads (so `n ≠ n` does not close) and for symbolic /
    // unsupported operands. The produced lambda is kernel-checked by `close_goal`.
    let Some(proof) = crate::tactic::decide_eq_noconfusion::build_noconfusion_ne_proof(
        state.env(),
        &eq_type,
        &lhs_norm,
        &rhs_norm,
        &eq_level,
    ) else {
        return Err(TacticError::no_progress("simp"));
    };

    state.close_goal(&goal, proof)
}

/// Simplified simp tactic with default config
///
/// REQUIRES: `state.goals` is non-empty
/// ENSURES: Same guarantees as `simp` with `SimpConfig::new()`
pub fn simp_default(state: &mut ProofState) -> TacticResult {
    simp(state, SimpConfig::new())
}

/// Simp tactic with specific lemmas only (no built-in or @[simp] set).
///
/// REQUIRES: `state.goals` is non-empty
/// REQUIRES: `lemmas` are valid lemma names in the environment or local context
/// ENSURES: Only the specified lemmas are used for rewriting (no @[simp] set)
/// ENSURES: Beta/eta reduction still applies
pub fn simp_only(state: &mut ProofState, lemmas: Vec<clean_parser::SurfaceName>) -> TacticResult {
    let mut config = SimpConfig::new();
    config.only = true;
    config.extra_lemmas = lemmas;
    simp(state, config)
}

/// Simp at a specific hypothesis with default config.
///
/// REQUIRES: `state.goals` is non-empty
/// REQUIRES: `hyp_name` exists in the current goal's local context
/// ENSURES: On Ok, the named hypothesis is simplified in the goal context
pub fn simp_at(state: &mut ProofState, hyp_name: &clean_parser::SurfaceName) -> TacticResult {
    simp_at_with_config(state, hyp_name, SimpConfig::new())
}

/// Simp at a specific hypothesis with only the given lemmas.
///
/// REQUIRES: `state.goals` is non-empty
/// REQUIRES: `hyp_name` exists in the current goal's local context
/// ENSURES: On Ok, the named hypothesis is simplified using only the specified lemmas
pub fn simp_only_at(
    state: &mut ProofState,
    hyp_name: &clean_parser::SurfaceName,
    lemmas: Vec<clean_parser::SurfaceName>,
) -> TacticResult {
    let mut config = SimpConfig::new();
    config.extra_lemmas = lemmas;
    simp_at_with_config(state, hyp_name, config)
}

/// Simp at a specific hypothesis with a given config.
///
/// Closes the old goal and creates a new one with the simplified hypothesis,
/// using a `let`-binding proof term. When a top-level simp lemma matches,
/// the cast proof is constructed via `Eq.subst` (same pattern as `rewrite_at`).
/// For sub-expression simplification, proof terms are built via congruence
/// (congrArg/congrFun/congr), funext (lambdas), and forall_congr+propext (Pi).
/// Returns an error for non-definitional changes where proof construction
/// fails (e.g., Let-expression bodies, non-Prop Pi types).
///
/// REQUIRES: `state` has at least one goal. `hyp_name` is a valid hypothesis
///   name in the current goal's local context.
/// ENSURES: On Ok, the old goal is closed with a proof cast and a new goal
///   replaces it with `hyp_name` simplified according to `config`. All
///   subsequent hypothesis types and the goal target have the old FVar
///   replaced with the new one. On Err(NoProgress), the hypothesis was
///   unchanged by simplification. On Err(TypeCheckFailed), a non-definitional
///   simplification lacked a proof term (soundness guard).
pub(crate) fn simp_at_with_config(
    state: &mut ProofState,
    hyp_name: &clean_parser::SurfaceName,
    mut config: SimpConfig,
) -> TacticResult {
    seed_unfold_defs_from_extras(state, &mut config);
    lemmas::seed_unfold_defs_from_simp_defs(state, &mut config);
    let simp_lemmas = collect_simp_lemmas_cached(state, &config);
    simp_at_with_lemmas(state, hyp_name, &config, &simp_lemmas)
}

/// Wildcard locations select locals by identity. Remove precisely that
/// local's own rules; duplicate spellings may denote distinct usable proofs.
pub(super) fn simp_at_fvar_with_config(
    state: &mut ProofState,
    hyp_fvar: clean_kernel::FVarId,
    mut config: SimpConfig,
) -> TacticResult {
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?;
    config.extra_lemmas.retain(|name| {
        !goal
            .local_ctx
            .iter()
            .rev()
            .find(|decl| crate::tactic::pattern::names::hypothesis_named(&decl.name, name))
            .is_some_and(|decl| decl.fvar == hyp_fvar)
    });
    config.exclude_hypothesis = None;
    if config.use_hypotheses {
        config
            .aesop_simp_lemmas
            .extend(lemmas::collect_hypothesis_lemmas_excluding(
                state,
                &config,
                Some(hyp_fvar),
            ));
        config.use_hypotheses = false;
    }
    seed_unfold_defs_from_extras(state, &mut config);
    lemmas::seed_unfold_defs_from_simp_defs(state, &mut config);
    let simp_lemmas = collect_simp_lemmas_cached(state, &config);
    simp_at_fvar_with_lemmas(state, hyp_fvar, &config, &simp_lemmas)
}

/// Simplify the TYPE of `proof` and transport `proof` along the resulting
/// equality — the half of `simpa … using e` that Lean performs and Clean did
/// not.
///
/// `simpa using h` in Lean 4 simplifies BOTH the goal and `h`'s type, then
/// closes the goal with the simplified `h`. Clean's compound `simpa` handler
/// simplified only the goal and then ran `exact` on the RAW term, so it worked
/// exactly when simp was a no-op on `h`.
///
/// Returns the transported proof, or `proof` unchanged whenever transport is
/// unnecessary or cannot be justified:
///   * no goal, or the proof's type cannot be inferred;
///   * simp made no progress on the type;
///   * simp's change was definitional only (`result.proof == None`) — `exact`
///     already accepts the raw term up to def-eq, so no cast is needed;
///   * the budget tripped.
///
/// The cast is the same `Eq.subst`-with-identity-motive construction
/// [`simp_at_with_lemmas`] uses for `simp … at h`, including its universe-level
/// derivation (`Eq.subst.{u}` with `α : Sort u`, so `u = succ l` when
/// `α = Sort l`).
///
/// SOUNDNESS: the assembled term is accepted only when its own INFERRED type is
/// def-eq to the simplified type; otherwise the original proof is returned
/// untouched and `exact` refuses it in the normal way. Nothing here bypasses
/// `close_goal`, which kernel-checks whatever `exact` finally submits.
pub(crate) fn simp_proof_type(state: &ProofState, mut config: SimpConfig, proof: Expr) -> Expr {
    let Some(goal) = state.current_goal().cloned() else {
        return proof;
    };
    let Ok(old_ty) = state.infer_type(&goal, &proof) else {
        return proof;
    };

    seed_unfold_defs_from_extras(state, &mut config);
    lemmas::seed_unfold_defs_from_simp_defs(state, &mut config);
    let simp_lemmas = collect_simp_lemmas_cached(state, &config);

    let budget = SimpBudget::for_target(&old_ty);
    // A runaway (no fixpoint) is treated as a tripped budget: the raw term
    // goes to `exact`, which kernel-checks it like any other.
    let Ok(result) =
        fixpoint::simp_type_to_fixpoint(state, &goal, &old_ty, &simp_lemmas, &config, &budget)
    else {
        return proof;
    };
    if budget.detail().is_some() || result.expr == old_ty {
        return proof;
    }
    let new_ty = result.expr;
    let Some(eq_proof) = result.proof else {
        // Definitional-only normalization: `exact` unifies up to def-eq, so the
        // raw term still lands. Fabricating a cast without a witness is exactly
        // the soundness gap `simp_at_with_lemmas` refuses.
        return proof;
    };

    let alpha = state
        .infer_type(&goal, &old_ty)
        .unwrap_or(Expr::sort(Level::zero()));
    let eq_subst_level = match alpha.kind() {
        ExprKind::Sort(level) => Level::succ(level.clone()),
        _ => Level::succ(Level::zero()),
    };
    let motive = Expr::lam(BinderInfo::Default, alpha.clone(), Expr::bvar(0));
    let transported = Expr::apps(
        Expr::const_(Name::from_string("Eq.subst"), vec![eq_subst_level]),
        [
            alpha,
            motive,
            old_ty,
            new_ty.clone(),
            eq_proof,
            proof.clone(),
        ],
    );

    match state.infer_type(&goal, &transported) {
        Ok(ty) if state.is_def_eq(&goal, &ty, &new_ty) => transported,
        _ => proof,
    }
}

/// Populate `config.unfold_defs` from `config.extra_lemmas` entries whose
/// resolved `ConstantInfo` is a `Declaration::Definition` (Part of #3518).
///
/// Shared helper for `simp`, `simp_at_with_config`, and `simp_all_with_config`
/// so every top-level entrypoint treats `simp [foo]` where `foo` is a
/// definition as a delta-unfold, matching Lean 4 `simp` semantics.
///
/// Preserves any pre-existing entries in `config.unfold_defs` (callers may
/// seed the map directly for advanced use cases; this function only fills
/// gaps from `extra_lemmas`).
pub(crate) fn seed_unfold_defs_from_extras(state: &ProofState, config: &mut SimpConfig) {
    config.prepared_rec_equations.clear();
    if config.extra_lemmas.is_empty() {
        return;
    }
    let resolved = resolve_unfold_defs(
        state,
        &config.extra_lemmas,
        &mut config.prepared_rec_equations,
    );
    for (name, def) in resolved {
        config.unfold_defs.entry(name).or_insert(def);
    }
}

/// `simp_at` with pre-collected lemmas.
///
/// Use this variant when calling in a loop to avoid re-collecting the
/// same environment-dependent lemma set on every iteration.
pub(super) fn simp_at_with_lemmas(
    state: &mut ProofState,
    hyp_name: &clean_parser::SurfaceName,
    config: &SimpConfig,
    simp_lemmas: &SimpLemmaSet,
) -> TacticResult {
    if state.goals.is_empty() {
        return Err(TacticError::NoGoals);
    }

    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();

    let hyp_idx = goal
        .local_ctx
        .iter()
        .rposition(|d| crate::tactic::pattern::names::hypothesis_named(&d.name, hyp_name))
        .ok_or_else(|| TacticError::HypothesisNotFound(hyp_name.to_string()))?;

    simp_at_fvar_with_lemmas(state, goal.local_ctx[hyp_idx].fvar, config, simp_lemmas)
}

pub(super) fn simp_at_fvar_with_lemmas(
    state: &mut ProofState,
    hyp_fvar: clean_kernel::FVarId,
    config: &SimpConfig,
    simp_lemmas: &SimpLemmaSet,
) -> TacticResult {
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();
    let hyp_idx = goal
        .local_ctx
        .iter()
        .position(|decl| decl.fvar == hyp_fvar)
        .ok_or_else(|| TacticError::HypothesisNotFound(format!("{hyp_fvar:?}")))?;
    let hyp_name = &goal.local_ctx[hyp_idx].name;

    let old_ty = goal.local_ctx[hyp_idx].ty.clone();
    // Own the budget so a trip is reported as a refusal rather than silently
    // read as "the hypothesis did not simplify".
    let budget = SimpBudget::for_target(&old_ty);
    // To a fixpoint, as Lean's `Simp.main` and the goal entry point do: one
    // traversal leaves the right-hand side it produced unvisited (G25).
    let simp_result =
        fixpoint::simp_type_to_fixpoint(state, &goal, &old_ty, simp_lemmas, config, &budget)
            .map_err(|runaway| TacticError::BudgetExceeded {
                tactic: format!("simp at {hyp_name}"),
                detail: runaway.detail(),
            })?;
    if let Some(detail) = budget.detail() {
        return Err(TacticError::BudgetExceeded {
            tactic: format!("simp at {hyp_name}"),
            detail,
        });
    }
    let new_ty = simp_result.expr;

    if new_ty == old_ty {
        // Lean's `applySimpResult` tests the RESULT, changed or not: a
        // hypothesis that already IS `False` closes the goal (pinned
        // v4.30.0-rc2: `example (h : False) : 1 = 2 := by simp at h`), it is
        // not "no progress".
        if !config.only_simplify
            && hyp_false::close_goal_by_false_hypothesis(
                state,
                &goal,
                &old_ty,
                &Expr::fvar(hyp_fvar),
            )
        {
            return Ok(());
        }
        return Err(no_progress_with_goal(state, format!("simp at {hyp_name}")));
    }

    // The simplified hypothesis is the `let` binder wrapped around this
    // goal's continuation, so it sits at the goal's own binder depth: its id
    // is the goal's binder base, as `intro` and `have` number theirs. The
    // global counter is not that base when several goals are simplified in
    // turn (`cases a <;> simp … at h`, `all_goals simp … at h`): the id then
    // named no binder at its depth and the proof was refused as capturing an
    // out-of-scope local.
    let h_new_fvar = {
        let base = state.goal_binder_base(&goal);
        state.next_fvar = state.next_fvar.max(base + 1);
        clean_kernel::FVarId::new(base)
    };

    // Build new local context with the simplified hypothesis
    let mut new_ctx = goal.local_ctx.clone();
    new_ctx[hyp_idx] = LocalDecl {
        binder_info: Default::default(),
        fvar: h_new_fvar,
        name: hyp_name.clone(),
        ty: new_ty.clone(),
        value: None,
    };

    // Replace references to old fvar with new fvar in subsequent hypotheses and target
    let new_target = goal.target.subst_fvar(hyp_fvar, &Expr::fvar(h_new_fvar));
    for decl in new_ctx.iter_mut().skip(hyp_idx + 1) {
        decl.ty = decl.ty.subst_fvar(hyp_fvar, &Expr::fvar(h_new_fvar));
    }

    // Create new goal metavariable
    let new_meta_id = state.fresh_meta_in_context(new_target.clone(), &new_ctx);
    let new_meta_expr = Expr::fvar(MetaState::to_fvar(new_meta_id));

    // Build the cast for the hypothesis using the SimpResult proof directly.
    let h_cast = if let Some(eq_proof) = &simp_result.proof {
        // Real proof available: eq_proof : old_ty = new_ty.
        // Use Eq.subst with identity motive to cast h : old_ty to h' : new_ty.
        // @Eq.subst α (λ T, T) old_ty new_ty eq_proof h
        let alpha = state
            .infer_type(&goal, &old_ty)
            .unwrap_or(Expr::sort(Level::zero()));
        let motive = Expr::lam(BinderInfo::Default, alpha.clone(), Expr::bvar(0));
        // Eq.subst.{u_1} has {α : Sort u_1}. When alpha = Sort(l),
        // alpha : Sort(succ(l)), so u_1 = succ(l).
        let eq_subst_level = match alpha.kind() {
            ExprKind::Sort(level) => Level::succ(level.clone()),
            _ => Level::succ(Level::zero()), // fallback: Type 0
        };
        let eq_subst = Expr::const_(Name::from_string("Eq.subst"), vec![eq_subst_level]);
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(Expr::app(eq_subst, alpha), motive),
                        old_ty.clone(),
                    ),
                    new_ty.clone(),
                ),
                eq_proof.clone(),
            ),
            Expr::fvar(hyp_fvar),
        )
    } else {
        // No proof — check definitional equality via is_def_eq (WHNF + unification).
        // Covers beta, eta, iota, zeta, and delta reductions.
        if state.is_def_eq(&goal, &old_ty, &new_ty) {
            Expr::fvar(hyp_fvar)
        } else {
            // Non-definitional change but proof was lost (e.g., congruence builder
            // failure inside nested expressions). Return error instead of silently
            // inserting sorry — this is a soundness gap (#2185).
            return Err(TacticError::TypeCheckFailed(format!(
                "simp at {hyp_name}: congruence proof construction failed; \
                 simplified type is not definitionally equal to the original"
            )));
        }
    };

    // Lean's `applySimpResult`: a hypothesis simplified to `False` closes the
    // goal (`hyp_false`). `only_simplify` callers asked for the rewrite alone.
    if !config.only_simplify
        && hyp_false::close_goal_by_false_hypothesis(state, &goal, &new_ty, &h_cast)
    {
        return Ok(());
    }

    let proof = Expr::let_named(
        hyp_name.name().clone(),
        new_ty.clone(),
        h_cast,
        new_meta_expr.abstract_fvar(h_new_fvar),
        false,
    );

    // Part of #2154: migrated to checked close_goal after fixing Eq.subst universe level.
    state.close_goal(&goal, proof)?;

    let new_goal = Goal {
        meta_id: new_meta_id,
        target: new_target,
        local_ctx: new_ctx,
        case_binders: goal.case_binders.clone(),
        tag: goal.tag.clone(),
    };
    state.goals.push_front(new_goal);

    Ok(())
}

/// Check if an expression is the True constant
///
/// ENSURES: Returns `true` iff `expr` is `Const("True", _)` or `Const("true", _)`
pub(crate) fn is_true_const(expr: &Expr) -> bool {
    if let ExprKind::Const(name, _) = expr.kind() {
        let name_str = name.to_string();
        name_str == "True" || name_str == "true"
    } else {
        false
    }
}

/// Check if an expression is a trivial equality (a = a)
///
/// ENSURES: Returns `true` iff `expr` is `@Eq _ a a` where `a` is syntactically equal on both sides
pub(crate) fn is_trivial_equality(expr: &Expr) -> bool {
    if let Ok((_ty, lhs, rhs, _levels)) = match_equality(expr) {
        exprs_syntactically_equal(&lhs, &rhs)
    } else {
        false
    }
}

/// Iterative node count with an early-exit cap (never recurses — it guards
/// paths whose whole failure mode is stack exhaustion). Returns
/// `min(actual_count, cap)`.
pub(crate) fn expr_node_count_capped(e: &Expr, cap: usize) -> usize {
    let mut count = 0usize;
    let mut work: Vec<&Expr> = vec![e];
    while let Some(cur) = work.pop() {
        count += 1;
        if count >= cap {
            return cap;
        }
        match cur.kind() {
            ExprKind::App(f, a) => {
                work.push(f);
                work.push(a);
            }
            ExprKind::Lam(_, t, b) | ExprKind::Pi(_, t, b) => {
                work.push(t);
                work.push(b);
            }
            ExprKind::Let(_, t, v, b, _) => {
                work.push(t);
                work.push(v);
                work.push(b);
            }
            ExprKind::Proj(_, _, inner) | ExprKind::MData(_, inner) => {
                work.push(inner);
            }
            _ => {}
        }
    }
    count
}
