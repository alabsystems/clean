// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Simplification tactics
//!
//! This module provides the `simp` family of tactics for automatic simplification
//! of expressions using rewrite lemmas, beta/eta reduction, and other normalizations.

mod all;
// Unwired roadmap prototype (2026-08-10): compiled only with its unit tests until the live
// pipeline owns it. Mirrors pattern_match_ext / error_recovery* precedent.
#[cfg(test)]
pub(crate) mod congr;
mod discharge;
#[cfg(test)]
mod discharge_tests;
mod expr;
mod lemmas;
mod lemmas_builtin;
mod pattern;
mod proof;
mod reduce;
mod rw;
pub(crate) mod simproc;
mod simproc_builtins;
mod simproc_builtins_bool;
mod squeeze;
mod types;

// Re-export public API
pub(crate) use all::simp_all_with_config;
pub use all::{simp_all, simp_at_all};
pub use expr::extract_equality_from_type;
pub use rw::{simp_rw, simp_rw_hyps};
pub use squeeze::{squeeze_simp, squeeze_simp_and_apply, squeeze_simp_with_config};
pub use squeeze::{SqueezeSimpConfig, SqueezeSimpResult};
pub use types::{SimpConfig, SimpIndexMode, SimpLemma};

// Re-export pub(crate) items used by other tactic modules
pub(crate) use expr::{make_eq_expr, simp_expr};
pub(crate) use lemmas::{collect_named_eq_lemmas, collect_simp_lemmas, resolve_unfold_defs};
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

use self::expr::{extract_eq_parts, try_apply_simp_lemma_with_proof};

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
///
/// # Contract
///
/// REQUIRES: `state.goals` is non-empty
/// ENSURES: On Ok, each simplification step is justified by an `Eq.trans` proof chain
/// ENSURES: On Ok, at most `config.max_steps` rewrite steps are applied
/// ENSURES: On Err(NoGoals), state is unchanged
pub fn simp(state: &mut ProofState, mut config: SimpConfig) -> TacticResult {
    if state.goals.is_empty() {
        return Err(TacticError::NoGoals);
    }

    seed_unfold_defs_from_extras(state, &mut config);
    lemmas::seed_unfold_defs_from_simp_defs(state, &mut config);

    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();
    let mut current_target = goal.target.clone();
    let mut steps = 0;
    let mut made_progress = false;

    // Collect simp lemmas from environment
    let simp_lemmas = collect_simp_lemmas(state, &config);

    // Main simplification loop — accumulate proof via Eq.trans chaining
    let mut accumulated_proof: Option<Expr> = None;
    while steps < config.max_steps {
        let step_result = simp_expr(state, &goal, &current_target, &simp_lemmas, &config);

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
                for lemma in simp_lemmas.candidates(state, &goal, &current_lhs) {
                    if let Some((new_lhs, lhs_proof)) = try_apply_simp_lemma_with_proof(
                        state,
                        &goal,
                        &current_lhs,
                        lemma,
                        &simp_lemmas,
                        &config,
                    ) {
                        if new_lhs == current_lhs {
                            continue;
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

        if !config.only_simplify && try_simp_closers(state) {
            return Ok(());
        }
        Ok(())
    } else {
        // No progress made - try closing with trivial tactics anyway
        if !config.only_simplify && try_simp_closers(state) {
            return Ok(());
        }
        Err(TacticError::NoProgress {
            tactic: "simp".into(),
        })
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
fn try_simp_closers(state: &mut ProofState) -> bool {
    try_tactic_preserving_state(state, close_refl_reducible)
        || try_tactic_preserving_state(state, close_true_goal)
        || try_tactic_preserving_state(state, assumption)
        || try_tactic_preserving_state(state, close_constructor_diseq_implication)
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
                Err(TacticError::NoProgress {
                    tactic: "simp".into(),
                })
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
        return Err(TacticError::NoProgress {
            tactic: "simp".into(),
        });
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
        return Err(TacticError::NoProgress {
            tactic: "simp".into(),
        });
    };

    let false_expr = Expr::const_(Name::from_string("False"), vec![]);
    let codomain_whnf = state.whnf(&goal, codomain);
    if !state.is_def_eq(&goal, &codomain_whnf, &false_expr) {
        return Err(TacticError::NoProgress {
            tactic: "simp".into(),
        });
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
        return Err(TacticError::NoProgress {
            tactic: "simp".into(),
        });
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
pub fn simp_only(state: &mut ProofState, lemmas: Vec<String>) -> TacticResult {
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
pub fn simp_at(state: &mut ProofState, hyp_name: &str) -> TacticResult {
    simp_at_with_config(state, hyp_name, SimpConfig::new())
}

/// Simp at a specific hypothesis with only the given lemmas.
///
/// REQUIRES: `state.goals` is non-empty
/// REQUIRES: `hyp_name` exists in the current goal's local context
/// ENSURES: On Ok, the named hypothesis is simplified using only the specified lemmas
pub fn simp_only_at(state: &mut ProofState, hyp_name: &str, lemmas: Vec<String>) -> TacticResult {
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
    hyp_name: &str,
    mut config: SimpConfig,
) -> TacticResult {
    seed_unfold_defs_from_extras(state, &mut config);
    lemmas::seed_unfold_defs_from_simp_defs(state, &mut config);
    let simp_lemmas = collect_simp_lemmas(state, &config);
    simp_at_with_lemmas(state, hyp_name, &config, &simp_lemmas)
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
    if config.extra_lemmas.is_empty() {
        return;
    }
    let resolved = resolve_unfold_defs(state, &config.extra_lemmas);
    for (name, body) in resolved {
        config.unfold_defs.entry(name).or_insert(body);
    }
}

/// `simp_at` with pre-collected lemmas.
///
/// Use this variant when calling in a loop to avoid re-collecting the
/// same environment-dependent lemma set on every iteration.
pub(super) fn simp_at_with_lemmas(
    state: &mut ProofState,
    hyp_name: &str,
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
        .position(|d| d.name == hyp_name)
        .ok_or_else(|| TacticError::HypothesisNotFound(hyp_name.to_string()))?;

    let hyp_fvar = goal.local_ctx[hyp_idx].fvar;

    let old_ty = goal.local_ctx[hyp_idx].ty.clone();
    let simp_result = simp_expr(state, &goal, &old_ty, simp_lemmas, config);
    let new_ty = simp_result.expr;

    if new_ty == old_ty {
        return Err(TacticError::NoProgress {
            tactic: format!("simp at {hyp_name}"),
        });
    }

    // Create a fresh fvar for the simplified hypothesis
    let h_new_fvar = state.fresh_fvar();

    // Build new local context with the simplified hypothesis
    let mut new_ctx = goal.local_ctx.clone();
    new_ctx[hyp_idx] = LocalDecl {
        fvar: h_new_fvar,
        name: hyp_name.to_string(),
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

    let proof = Expr::let_named(
        Name::from_string(hyp_name),
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
