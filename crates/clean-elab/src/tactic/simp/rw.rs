// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `simp_rw` tactic — simplification with interleaved rewriting.

use clean_kernel::name::Name;
use clean_kernel::{Expr, Level};

use super::budget::SimpBudget;
use super::cache::collect_simp_lemmas_cached;
use super::expr::{extract_eq_sides, simp_expr_budgeted};
use super::lemmas::{extract_local_equality_template, mk_local_proof_template};
use super::types::{SimpConfig, SimpIndexMode, SimpLemma};
use crate::tactic::discr_tree::{mk_path, query_path_is_too_generic, IndexMode};
use crate::tactic::display::no_progress_with_goal;
use crate::tactic::{
    exprs_syntactically_equal, rfl, try_tactic_preserving_state, Goal, ProofState, TacticError,
    TacticResult,
};

fn mk_reverse_local_eq_proof(
    state: &ProofState,
    eq_type: &Expr,
    lhs: &Expr,
    rhs: &Expr,
    levels: Vec<Level>,
    forward_proof: Expr,
) -> Result<Expr, TacticError> {
    let symm_name = Name::from_string("Eq.symm");
    if state.env.get_const(&symm_name).is_none() {
        return Err(TacticError::EnvironmentMissing {
            constant: "Eq.symm".to_string(),
        });
    }

    let mut reverse_proof = Expr::const_(symm_name, levels);
    reverse_proof = Expr::app(reverse_proof, eq_type.clone());
    reverse_proof = Expr::app(reverse_proof, lhs.clone());
    reverse_proof = Expr::app(reverse_proof, rhs.clone());
    reverse_proof = Expr::app(reverse_proof, forward_proof);
    Ok(reverse_proof)
}

fn collect_local_rw_simp_lemmas(
    state: &ProofState,
    goal: &Goal,
    lemmas: &[clean_parser::SurfaceName],
) -> Result<Vec<SimpLemma>, TacticError> {
    let mut out = Vec::new();

    for lemma_name in lemmas {
        let Some(hyp_decl) =
            goal.local_ctx.iter().rev().find(|decl| {
                crate::tactic::pattern::names::hypothesis_named(&decl.name, lemma_name)
            })
        else {
            continue;
        };

        let hyp_ty = state.whnf(goal, &hyp_decl.ty);
        let Some((binder_count, eq_type, lhs, rhs, levels)) =
            extract_local_equality_template(&hyp_ty)
        else {
            continue;
        };

        let eq_type = state.metas.instantiate(&eq_type);
        let lhs = state.metas.instantiate(&lhs);
        let rhs = state.metas.instantiate(&rhs);
        let forward_proof = state.metas.instantiate(&mk_local_proof_template(
            Expr::fvar(hyp_decl.fvar),
            binder_count,
        ));
        let reverse_proof =
            mk_reverse_local_eq_proof(state, &eq_type, &lhs, &rhs, levels, forward_proof.clone())?;

        out.push(SimpLemma {
            name: lemma_name.name().clone(),
            lhs: lhs.clone(),
            rhs: rhs.clone(),
            eq_type: Some(eq_type.clone()),
            proof_expr: Some(forward_proof),
            index_mode: SimpIndexMode::NoIndexAtArgs,
            priority: 1_000,
        });

        let reverse_query_path = mk_path(state, goal, &rhs, IndexMode::NoIndexAtArgs);
        if !query_path_is_too_generic(&reverse_query_path) {
            out.push(SimpLemma {
                name: lemma_name.name().clone(),
                lhs: rhs,
                rhs: lhs,
                eq_type: Some(eq_type),
                proof_expr: Some(reverse_proof),
                index_mode: SimpIndexMode::NoIndexAtArgs,
                priority: 1_000,
            });
        }
    }

    Ok(out)
}

/// `simp_rw` applies simplification and rewriting interleaved.
/// Unlike `simp`, it applies rewrites more aggressively at all positions.
///
/// # Example
/// ```text
/// -- Goal: f (a + 0) = f a
/// simp_rw [h]  -- where h : a + 0 = a
/// ```
///
/// # Contract
///
/// REQUIRES: `state.goals` is non-empty
/// ENSURES: On Ok, goal target was simplified; may or may not be closed (rfl attempted)
/// ENSURES: On Err(NoProgress), no rewrite or simp step changed the target
/// ENSURES: On Err(NoGoals), no goals exist; state unchanged
pub fn simp_rw(state: &mut ProofState, lemmas: Vec<clean_parser::SurfaceName>) -> TacticResult {
    simp_rw_with_rules(state, lemmas, Vec::new())
}

/// `simp_rw` over rules that are already resolved.
///
/// `prebuilt` carries what the by-name channel cannot express — a `←`-reversed
/// rule and a rule whose surface form is a TERM — built by
/// `simp::args::resolve_simp_args`. `lemmas` is the by-name remainder, and it
/// now reaches `extra_lemmas` as well as `collect_local_rw_simp_lemmas`: that
/// function skips every name that is not a local hypothesis (`else { continue
/// }`), so `simp_rw [and_comm]` used to run with the default simp set and NONE
/// of the named rules, silently.
///
/// NOT Lean-faithful yet, and the gap is stated rather than hidden: Mathlib's
/// `simp_rw` (`Mathlib/Tactic/SimpRw.lean`) desugars to `simp only` with no
/// rules followed by ONE `simp only [lᵢ]` per rule IN ORDER
/// (`withSimpRWRulesSeq`), where this applies the whole set at once. That
/// ordering difference has its own counterexample in Mathlib's docstring;
/// porting the desugaring is separate work.
pub(crate) fn simp_rw_with_rules(
    state: &mut ProofState,
    lemmas: Vec<clean_parser::SurfaceName>,
    prebuilt: Vec<SimpLemma>,
) -> TacticResult {
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();
    let mut current_target = goal.target.clone();
    let mut made_progress = false;
    let mut steps = 0;
    let mut accumulated_proof: Option<Expr> = None;

    let mut simp_config = SimpConfig::new();
    simp_config.aesop_simp_lemmas = collect_local_rw_simp_lemmas(state, &goal, &lemmas)?;
    simp_config.aesop_simp_lemmas.extend(prebuilt);
    simp_config.extra_lemmas = lemmas.clone();
    let simp_lemmas = collect_simp_lemmas_cached(state, &simp_config);

    // Same per-traversal budget `simp` carries (see `simp/budget.rs`); a trip
    // is a refusal, not a truncated rewrite chain.
    let budget = SimpBudget::for_target(&current_target);

    while steps < simp_config.max_steps {
        budget.refuel();
        let simp_result = simp_expr_budgeted(
            state,
            &goal,
            &current_target,
            &simp_lemmas,
            &simp_config,
            &budget,
        );
        if let Some(detail) = budget.detail() {
            return Err(TacticError::BudgetExceeded {
                tactic: "simp_rw".into(),
                detail,
            });
        }
        if simp_result.expr == current_target {
            break;
        }

        accumulated_proof = match (accumulated_proof.take(), simp_result.proof) {
            (None, proof) => proof,
            (proof, None) => proof,
            (Some(p1), Some(p2)) => {
                Some(super::mk_eq_trans_expr(state, &goal, &p1, &p2).unwrap_or(p2))
            }
        };
        current_target = simp_result.expr;
        made_progress = true;
        steps += 1;

        if let Some((lhs, rhs)) = extract_eq_sides(&current_target) {
            if exprs_syntactically_equal(&lhs, &rhs) {
                break;
            }
        }
    }

    if made_progress {
        if let Some(proof) = accumulated_proof {
            state.replace_target_eq(current_target.clone(), proof)?;
        } else {
            state.replace_target_def_eq(current_target.clone())?;
        }

        // Part of #2474: wrap in try_tactic_preserving_state to prevent
        // failed rfl from leaking partial state mutations.
        if try_tactic_preserving_state(state, rfl) {
            return Ok(());
        }

        Ok(())
    } else {
        Err(no_progress_with_goal(state, "simp_rw"))
    }
}

/// Simplified version of simp_rw that uses hypotheses by name.
pub fn simp_rw_hyps(
    state: &mut ProofState,
    hyp_names: Vec<&clean_parser::SurfaceName>,
) -> TacticResult {
    simp_rw(state, hyp_names.into_iter().cloned().collect())
}
