// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Phase 3D Wave 3: rewrite/simplification tactic registrations.
//!
//! Migrates `Rw`, `Simp`, `SimpRw`, `Simpa` from hardcoded `eval_rewrite_tactic`
//! dispatch to registry-based compound handlers (#2440).
//!
//! These handlers operate entirely on `ProofState` — they do not need
//! `TacticEval` for recursive tactic evaluation or expression elaboration.
//! The `&mut dyn TacticEval` parameter is unused.

use std::sync::Arc;

use super::conv_proof::{
    build_conv_rewrite_eq_proof, chain_conv_focus_eq_proofs, ConvRewriteProofInputs,
};
use super::equality::{contains_expr, match_equality, replace_expr, resolve_env_rewrite_parts};
use super::registry::{CompoundTacticEntry, TacticEval, TacticRegistry};
use super::{ProofState, SimpConfig, TacticError};
use clean_kernel::{Expr, Level, Name};
use clean_parser::{Projection, SurfaceExpr, SurfaceRwRule, SurfaceTactic, SurfaceTacticLocation};

/// A rw rule term resolves to a *name* (local hypothesis or environment
/// constant) iff it is a bare identifier, a dotted projection chain
/// (`Nat.testBit_and`), or such a term wrapped in parentheses. Anything else —
/// an application (`lem x y h`), a `show A = B from rfl` ascription, a lambda,
/// etc. — must be elaborated as a *proof term* instead, because reducing it to
/// a `format!`-derived string (as `surface_expr_to_name` does for unhandled
/// variants) would never match a real declaration.
fn rw_rule_is_name(term: &SurfaceExpr) -> bool {
    match term {
        SurfaceExpr::Ident(..) => true,
        SurfaceExpr::Proj(_, base, Projection::Named(_)) => rw_rule_is_name(base),
        SurfaceExpr::Paren(_, inner) => rw_rule_is_name(inner),
        _ => false,
    }
}

/// Register rewrite/simp compound tactics into the registry.
/// ENSURES: `registry` contains compound handlers for `rw`, `simp`, `simp_rw`, and `simpa`.
/// ENSURES: Existing compound entries with those names are replaced.
pub(crate) fn register_phase3d_rewrite(registry: &mut TacticRegistry) {
    registry.register_compound(compound_rw());
    registry.register_compound(compound_simp());
    registry.register_compound(compound_simp_rw());
    registry.register_compound(compound_simpa());
}

/// `rw [rules] (at loc)?` — rewrite with location dispatch.
fn compound_rw() -> CompoundTacticEntry {
    CompoundTacticEntry {
        name: "rw".into(),
        handler: Arc::new(|eval, ps, tac| {
            let SurfaceTactic::Rw(_, rules, location) = tac else {
                return Err(TacticError::InvalidTarget {
                    tactic: "rw".into(),
                    detail: "unexpected syntax variant".into(),
                });
            };
            match location {
                SurfaceTacticLocation::Hyps(hyps) => rw_hyp_rules(eval, ps, rules, hyps),
                SurfaceTacticLocation::HypsAndGoal(hyps) => {
                    rw_hyp_rules(eval, ps, rules, hyps)?;
                    rw_goal_rules(eval, ps, rules)
                }
                SurfaceTacticLocation::Wildcard => {
                    // rw [...] at * — rewrite in all hypotheses then goal.
                    // Lean 4 semantics: skip hypotheses used as rewrite lemmas.
                    let goal = ps.current_goal().ok_or(TacticError::NoGoals)?.clone();
                    let lemma_names: Vec<String> = rules
                        .iter()
                        .map(|r| super::builtins::surface_expr_to_name(&r.term))
                        .collect();
                    for decl in &goal.local_ctx {
                        if lemma_names.contains(&decl.name) {
                            continue;
                        }
                        for rule in rules {
                            let lemma_name = super::builtins::surface_expr_to_name(&rule.term);
                            let _ = super::rewrite_at(ps, &lemma_name, &decl.name, rule.reverse);
                        }
                    }
                    for rule in rules {
                        let lemma_name = super::builtins::surface_expr_to_name(&rule.term);
                        if rule.reverse {
                            super::rewrite_rtl(ps, &lemma_name)?;
                        } else {
                            super::rewrite_ltr(ps, &lemma_name)?;
                        }
                    }
                    let _ = super::rfl(ps);
                    Ok(())
                }
                SurfaceTacticLocation::Goal => rw_goal_rules(eval, ps, rules),
            }
        }),
    }
}

/// `simp (only)? [lemmas] (at loc)?` — simplification with location dispatch.
fn compound_simp() -> CompoundTacticEntry {
    CompoundTacticEntry {
        name: "simp".into(),
        handler: Arc::new(|_eval, ps, tac| {
            let SurfaceTactic::Simp {
                only,
                lemmas,
                location,
                ..
            } = tac
            else {
                return Err(TacticError::InvalidTarget {
                    tactic: "simp".into(),
                    detail: "unexpected syntax variant".into(),
                });
            };
            match location {
                SurfaceTacticLocation::Hyps(hyps) => simp_hyps(ps, *only, lemmas, hyps),
                SurfaceTacticLocation::HypsAndGoal(hyps) => {
                    simp_hyps(ps, *only, lemmas, hyps)?;
                    simp_goal_with_lemmas(ps, *only, lemmas)
                }
                SurfaceTacticLocation::Wildcard => super::simp_at_all(ps),
                SurfaceTacticLocation::Goal => simp_goal_with_lemmas(ps, *only, lemmas),
            }
        }),
    }
}

fn simp_names(lemmas: &[SurfaceExpr]) -> Vec<String> {
    lemmas
        .iter()
        .map(super::builtins::surface_expr_to_name)
        .collect()
}

fn simp_goal_with_lemmas(
    ps: &mut ProofState,
    only: bool,
    lemmas: &[SurfaceExpr],
) -> Result<(), TacticError> {
    let names = simp_names(lemmas);
    if only {
        super::simp_only(ps, names)
    } else {
        let mut config = SimpConfig::new();
        config.extra_lemmas = names;
        super::simp(ps, config)
    }
}

/// `simp_rw [rules] (at loc)?` — simp + rw combined.
fn compound_simp_rw() -> CompoundTacticEntry {
    CompoundTacticEntry {
        name: "simp_rw".into(),
        handler: Arc::new(|_eval, ps, tac| {
            let SurfaceTactic::SimpRw(_, rules, location) = tac else {
                return Err(TacticError::InvalidTarget {
                    tactic: "simp_rw".into(),
                    detail: "unexpected syntax variant".into(),
                });
            };
            let names: Vec<String> = rules
                .iter()
                .map(|r| super::builtins::surface_expr_to_name(&r.term))
                .collect();
            match location {
                SurfaceTacticLocation::Hyps(hyps) => simp_rw_hyps(ps, &names, hyps),
                SurfaceTacticLocation::HypsAndGoal(hyps) => {
                    simp_rw_hyps(ps, &names, hyps)?;
                    super::simp_rw(ps, names)
                }
                SurfaceTacticLocation::Wildcard => {
                    let goal = ps.current_goal().ok_or(TacticError::NoGoals)?.clone();
                    for decl in &goal.local_ctx {
                        let _ = super::simp_only_at(ps, &decl.name, names.clone());
                    }
                    super::simp_rw(ps, names)
                }
                SurfaceTacticLocation::Goal => super::simp_rw(ps, names),
            }
        }),
    }
}

/// Apply `rw` rules to the current goal target.
///
/// When inside a navigated conv body (`ps.conv_nav` has a non-empty path), the
/// target is a focused sub-expression (possibly non-Prop). The generic `Eq.subst`
/// path requires a Prop-valued target, so we dispatch to `conv_focus_rewrite`
/// for structural replacement and let `eval_conv_goal` lift the proof (#2540).
fn rw_goal_rules(
    eval: &mut dyn TacticEval,
    ps: &mut ProofState,
    rules: &[SurfaceRwRule],
) -> Result<(), TacticError> {
    let in_conv_focus = ps
        .conv_nav
        .as_ref()
        .is_some_and(|(_, path)| !path.is_empty())
        // Multi-focus congr: a selected sub-focus is the focused (possibly
        // non-Prop) target; route to the structural conv rewrite (#2477 Phase 4).
        || (ps.conv_focus_tree.is_some() && ps.conv_congr_cursor.is_some());
    if in_conv_focus {
        // Conv navigation rewrites a (possibly non-Prop) focused sub-expression
        // through a structural witness; that path is name-keyed only. A
        // non-name rewrite term here is unsupported, so it still falls through
        // `surface_expr_to_name` (which yields a non-matching name → clear error).
        for rule in rules {
            let lemma_name = super::builtins::surface_expr_to_name(&rule.term);
            conv_focus_rewrite(ps, &lemma_name, rule.reverse)?;
        }
    } else {
        for rule in rules {
            if rw_rule_is_name(&rule.term) {
                let lemma_name = super::builtins::surface_expr_to_name(&rule.term);
                if rule.reverse {
                    super::rewrite_rtl(ps, &lemma_name)?;
                } else {
                    super::rewrite_ltr(ps, &lemma_name)?;
                }
            } else {
                // Non-identifier rule term: elaborate it as a proof term and
                // rewrite by its inferred equality type (`rw [show A = B from
                // rfl]`, `rw [lem x y h]`, …).
                let proof = eval.elaborate(&rule.term)?;
                super::rewrite_with_proof(ps, proof, rule.reverse)?;
            }
        }
    }
    let _ = super::rfl(ps);
    Ok(())
}

fn rw_hyp_rules(
    eval: &mut dyn TacticEval,
    ps: &mut ProofState,
    rules: &[SurfaceRwRule],
    hyps: &[String],
) -> Result<(), TacticError> {
    for hyp in hyps {
        for rule in rules {
            if rw_rule_is_name(&rule.term) {
                let lemma_name = super::builtins::surface_expr_to_name(&rule.term);
                super::rewrite_at(ps, &lemma_name, hyp, rule.reverse)?;
            } else {
                // `rw [<term>] at h`: elaborate the rule as a proof term and
                // rewrite the hypothesis by its inferred equality type
                // (`rw [Nat.add_comm a b] at h`, `rw [lem x y] at h`, …).
                let proof = eval.elaborate(&rule.term)?;
                super::rewrite_at_with_proof(ps, proof, hyp, rule.reverse)?;
            }
        }
    }
    Ok(())
}

fn simp_hyps(
    ps: &mut ProofState,
    only: bool,
    lemmas: &[SurfaceExpr],
    hyps: &[String],
) -> Result<(), TacticError> {
    let names = simp_names(lemmas);
    if only {
        for hyp in hyps {
            super::simp_only_at(ps, hyp, names.clone())?;
        }
    } else {
        let mut config = SimpConfig::new();
        config.extra_lemmas = names;
        for hyp in hyps {
            super::simp::simp_at_with_config(ps, hyp, config.clone())?;
        }
    }
    Ok(())
}

fn simp_rw_hyps(ps: &mut ProofState, names: &[String], hyps: &[String]) -> Result<(), TacticError> {
    for hyp in hyps {
        super::simp_only_at(ps, hyp, names.to_vec())?;
    }
    Ok(())
}

/// Structural focus-only rewrite for navigated conv mode.
///
/// When `rw` runs inside a navigated conv body (`ps.conv_nav` has a non-empty
/// path), the current goal target is the focused sub-expression, which may be
/// non-Prop (e.g., `x : Nat`). The generic `rewrite` path builds an `Eq.subst`
/// proof whose motive must be a type family `α → Prop`, which is ill-typed for
/// term-valued focuses.
///
/// This helper rewrites the focused target and records a checked equality
/// witness on the nested proof state. The outer `eval_conv_goal` /
/// `eval_conv_hyps` in `builtins_phase3d_conv.rs` lifts that focused witness
/// through the saved navigation path.
///
/// Part of #2555.
fn conv_focus_rewrite(
    ps: &mut ProofState,
    hyp_name: &str,
    reverse: bool,
) -> Result<(), TacticError> {
    let goal = ps.current_goal().ok_or(TacticError::NoGoals)?.clone();
    let target = ps.metas.instantiate(&goal.target);

    // Resolve the rewrite rule to a concrete equation `base_proof : lhs = rhs`
    // (original orientation). A local hypothesis of the name shadows an
    // environment constant (Lean 4 resolution order). When no local hypothesis
    // exists, fall back to the environment: `resolve_env_rewrite_parts` peels
    // the constant's leading `∀` binders to metavariables and unifies its
    // `from` side against the focus `target` to solve them — the identical
    // resolution `rw [envLemma]` performs, here lifted through conv's
    // congruence proof (`build_conv_rewrite_eq_proof`) rather than
    // `finish_rewrite`. This is what lets `conv => …; rw [Nat.add_zero]` reach
    // an env lemma instead of failing `HypothesisNotFound`.
    let (eq_type, lhs, rhs, eq_levels, base_proof): (Expr, Expr, Expr, Vec<Level>, Expr) =
        match goal.local_ctx.iter().find(|d| d.name == hyp_name) {
            Some(hyp_decl) => {
                let hyp_decl = hyp_decl.clone();
                let hyp_ty = ps.whnf(&goal, &hyp_decl.ty);
                let (eq_type, lhs, rhs, eq_levels) = match_equality(&hyp_ty)?;
                (eq_type, lhs, rhs, eq_levels, Expr::fvar(hyp_decl.fvar))
            }
            None => resolve_env_rewrite_parts(ps, &goal, hyp_name, reverse, &target)?,
        };

    // Orient the (concrete) equation for the requested direction and build the
    // leaf equality proof. `base_proof : lhs = rhs`; a reverse rewrite flips the
    // sides and wraps the proof in `Eq.symm`. (For the env path, the metavars
    // were already solved against the correct — reverse-aware — `from` side, so
    // both `lhs` and `rhs` are concrete here.)
    let (from, to, leaf_eq_proof) = if reverse {
        let symm = Expr::const_(Name::from_string("Eq.symm"), eq_levels);
        let symm_proof = Expr::app(
            Expr::app(
                Expr::app(Expr::app(symm, eq_type.clone()), lhs.clone()),
                rhs.clone(),
            ),
            base_proof,
        );
        (rhs, lhs, symm_proof)
    } else {
        (lhs, rhs, base_proof)
    };

    if !contains_expr(&target, &from) {
        return Err(TacticError::NoProgress {
            tactic: "rw".into(),
        });
    }

    let new_target = replace_expr(&target, &from, &to);
    let step_eq_proof = build_conv_rewrite_eq_proof(
        ps,
        &goal,
        ConvRewriteProofInputs {
            target: &target,
            path: &[],
            focus_before: &target,
            focus_after: &new_target,
            from: &from,
            to: &to,
            from_ty: &eq_type,
            leaf_eq_proof,
        },
    )?
    .ok_or_else(|| {
        TacticError::TypeCheckFailed("conv_rw: failed to build focus rewrite witness".into())
    })?;
    // Multi-focus congr tree active with a selected focus: write the rewrite
    // into that focus node instead of the global single-focus witness. The
    // per-focus equalities are recombined at the conv reconstruction boundary
    // (#2477 Phase 4).
    if let Some(cursor) = ps.conv_congr_cursor.clone() {
        let prev_eq = focus_eq_proof_at(ps, &cursor);
        let new_eq = match prev_eq {
            Some(existing) => chain_conv_focus_eq_proofs(ps, &goal, &existing, &step_eq_proof)?,
            None => step_eq_proof,
        };
        write_congr_focus_rewrite(ps, &cursor, new_target.clone(), new_eq)?;
        if let Some(g) = ps.current_goal_mut() {
            g.target = new_target;
        }
        return Ok(());
    }

    let accumulated_witness = match ps.conv_focus_witness.as_ref() {
        Some(existing) => super::core::ConvFocusWitness {
            before: existing.before.clone(),
            after: new_target.clone(),
            eq_proof: chain_conv_focus_eq_proofs(ps, &goal, &existing.eq_proof, &step_eq_proof)?,
        },
        None => super::core::ConvFocusWitness {
            before: target.clone(),
            after: new_target.clone(),
            eq_proof: step_eq_proof,
        },
    };
    ps.conv_focus_witness = Some(accumulated_witness);
    if let Some(g) = ps.current_goal_mut() {
        g.target = new_target;
    }
    Ok(())
}

/// The current accumulated `eq_proof` for the focus at the cursor path, if any.
fn focus_eq_proof_at(ps: &ProofState, cursor: &[usize]) -> Option<Expr> {
    ps.conv_focus_tree
        .as_ref()?
        .focus_at_path(cursor)?
        .eq_proof
        .clone()
}

/// Write a rewrite result (`after` + `before = after` proof) into the focus at
/// the cursor path of the active congr tree.
fn write_congr_focus_rewrite(
    ps: &mut ProofState,
    cursor: &[usize],
    after: Expr,
    eq_proof: Expr,
) -> Result<(), TacticError> {
    let tree = ps.conv_focus_tree.as_mut().ok_or_else(|| {
        TacticError::TypeCheckFailed("conv congr: rewrite outside an active focus tree".into())
    })?;
    let focus = tree.focus_at_path_mut(cursor).ok_or_else(|| {
        TacticError::TypeCheckFailed("conv congr: focus cursor out of range".into())
    })?;
    focus.after = after;
    focus.eq_proof = Some(eq_proof);
    Ok(())
}

/// `simpa (only)? [lemmas] (using term)?` — simp the goal, then close it.
///
/// With `using term`, the goal is simplified (best effort) and then closed with
/// the elaborated `term` via `exact` (the term's type must be definitionally
/// equal to the simplified goal — the common `simpa using lemma_app` shape where
/// `simp` is a no-op and the lemma closes the goal directly). Without `using`,
/// it simplifies and falls back to `assumption`.
///
/// `simp` making no progress is *not* a failure here: `simpa` succeeds whenever
/// the closing step (the `using` term, or an assumption) discharges the
/// post-simplification goal, exactly as in Lean 4.
fn compound_simpa() -> CompoundTacticEntry {
    CompoundTacticEntry {
        name: "simpa".into(),
        handler: Arc::new(|eval, ps, tac| {
            let SurfaceTactic::Simpa {
                only,
                lemmas,
                using_term,
                ..
            } = tac
            else {
                return Err(TacticError::InvalidTarget {
                    tactic: "simpa".into(),
                    detail: "unexpected syntax variant".into(),
                });
            };

            // Simplify the goal. A `NoProgress` result is tolerated: the closing
            // step below may still discharge the (unchanged) goal.
            let simp_result = if *only && !lemmas.is_empty() {
                let names: Vec<String> = lemmas
                    .iter()
                    .map(super::builtins::surface_expr_to_name)
                    .collect();
                super::simp_only(ps, names)
            } else {
                super::simp_default(ps)
            };
            match simp_result {
                Ok(()) => {}
                Err(TacticError::NoProgress { .. }) | Err(TacticError::NoGoals) => {}
                Err(e) => return Err(e),
            }

            // If simp already closed the goal, we are done.
            if ps.current_goal().is_none() {
                return Ok(());
            }

            match using_term {
                Some(term) => {
                    let proof = eval.elaborate(term)?;
                    super::exact(ps, proof)
                }
                None => super::assumption(ps),
            }
        }),
    }
}
