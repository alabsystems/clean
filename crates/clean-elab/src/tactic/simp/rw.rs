// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `simp_rw` tactic — simplification with interleaved rewriting.

use clean_kernel::name::Name;
use clean_kernel::{Expr, Level};

use super::cache::collect_simp_lemmas_cached;
use super::expr::{extract_eq_sides, simp_expr};
use super::lemmas::{extract_local_equality_template, mk_local_proof_template};
use super::types::{SimpConfig, SimpIndexMode, SimpLemma};
use crate::tactic::discr_tree::{mk_path, query_path_is_too_generic, IndexMode};
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
    lemmas: &[String],
) -> Result<Vec<SimpLemma>, TacticError> {
    let mut out = Vec::new();

    for lemma_name in lemmas {
        let Some(hyp_decl) = goal.local_ctx.iter().find(|decl| &decl.name == lemma_name) else {
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
            name: Name::from_string(lemma_name),
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
                name: Name::from_string(lemma_name),
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
/// REQUIRES: `lemmas` contains names of hypotheses in the goal's local context
/// ENSURES: On Ok, goal target was simplified; may or may not be closed (rfl attempted)
/// ENSURES: On Err(NoProgress), no rewrite or simp step changed the target
/// ENSURES: On Err(NoGoals), no goals exist; state unchanged
pub fn simp_rw(state: &mut ProofState, lemmas: Vec<String>) -> TacticResult {
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();
    let mut current_target = goal.target.clone();
    let mut made_progress = false;
    let mut steps = 0;
    let mut accumulated_proof: Option<Expr> = None;

    let mut simp_config = SimpConfig::new();
    simp_config.aesop_simp_lemmas = collect_local_rw_simp_lemmas(state, &goal, &lemmas)?;
    let simp_lemmas = collect_simp_lemmas_cached(state, &simp_config);

    while steps < simp_config.max_steps {
        let simp_result = simp_expr(state, &goal, &current_target, &simp_lemmas, &simp_config);
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
        Err(TacticError::NoProgress {
            tactic: "simp_rw".into(),
        })
    }
}

/// Simplified version of simp_rw that uses hypotheses by name.
pub fn simp_rw_hyps(state: &mut ProofState, hyp_names: Vec<&str>) -> TacticResult {
    simp_rw(
        state,
        hyp_names.into_iter().map(ToString::to_string).collect(),
    )
}
