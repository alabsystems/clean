// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Classical propositional reasoning helpers for tauto.
//!
//! Provides double negation elimination and de Morgan case analysis
//! for goals that require classical logic (excluded middle).

use clean_kernel::name::Name;
use clean_kernel::Expr;

use super::super::{
    assumption, by_cases, exact, intro, left_, match_and, match_not, match_or, right_, ProofState,
    TacticError, TacticResult,
};
use super::fresh_hyp_name;

/// Try classical double negation elimination.
///
/// If the goal is P and there's a hypothesis h : ¬¬P, use Classical.byContradiction.
/// Handles both ¬¬P = Not (Not P) and ¬¬P = (P → False) → False forms.
///
/// REQUIRES: `state` has at least one goal. `Classical.byContradiction` must
///   exist in the environment.
/// ENSURES: On Ok, the goal is closed using byContradiction applied to a
///   double-negation hypothesis. On Err, no matching hypothesis was found
///   or the classical axiom is unavailable.
pub(super) fn try_classical_dne(state: &mut ProofState) -> TacticResult {
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();
    let target = state.metas.instantiate(&goal.target);

    // Check if Classical.byContradiction exists
    let byc_name = Name::from_string("Classical.byContradiction");
    if state.env.get_const(&byc_name).is_none() {
        return Err(TacticError::EnvironmentMissing {
            constant: "Classical.byContradiction".to_string(),
        });
    }

    // Look for a hypothesis of type ¬¬P where P is def-eq to target
    for decl in &goal.local_ctx {
        let hyp_ty = state.metas.instantiate(&decl.ty);

        // Use match_not twice: ¬¬P = ¬(¬P)
        if let Some(inner_neg) = match_not(&hyp_ty) {
            if let Some(inner_p) = match_not(&inner_neg) {
                // Check if inner_p is def-eq to target
                if state.is_def_eq(&goal, &inner_p, &target) {
                    // Found ¬¬P where P = target
                    // Apply Classical.byContradiction : {p : Prop} → (¬p → False) → p
                    // byContradiction @target h
                    let byc = Expr::const_(byc_name, vec![]);
                    let byc_at_p = Expr::app(byc, target.clone());
                    let proof = Expr::app(byc_at_p, Expr::fvar(decl.fvar));
                    return exact(state, proof);
                }
            }
        }
    }

    Err(TacticError::HypothesisNotFound(
        "no double negation hypothesis found".into(),
    ))
}

/// Try classical by_cases for disjunctive goals.
///
/// Handles goals like `¬P ∨ ¬Q` with hypothesis `¬(P ∧ Q)` (de Morgan's law).
/// Uses case analysis on propositions that appear negated in the goal.
///
/// For goal `¬A ∨ ¬B` with hypothesis `h : ¬(A ∧ B)`:
/// - Case A: prove ¬B via contradiction (A ∧ B contradicts h)
/// - Case ¬A: prove ¬A ∨ ¬B via left
///
/// REQUIRES: `state` has at least one goal whose target is a disjunction.
///   `Classical.em` must exist in the environment for by_cases.
/// ENSURES: Returns Ok(true) if the goal was closed via de Morgan case analysis.
///   Returns Ok(false) if no applicable hypothesis was found.
pub(super) fn try_by_cases_for_disjunction(state: &mut ProofState) -> Result<bool, TacticError> {
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();
    let target = state.metas.instantiate(&goal.target);

    // Must be a disjunction
    let Some((left, right)) = match_or(&target) else {
        return Ok(false);
    };

    // Check if Classical.em exists for by_cases
    let em_name = Name::from_string("Classical.em");
    if state.env.get_const(&em_name).is_none() {
        return Ok(false);
    }

    // Try case analysis when we have ¬A ∨ ¬B and a negated conjunction hypothesis
    // This handles de Morgan: ¬(A ∧ B) → ¬A ∨ ¬B
    if let (Some(inner_a), Some(inner_b)) = (match_not(&left), match_not(&right)) {
        // Look for hypothesis ¬(A ∧ B)
        for decl in &goal.local_ctx {
            let hyp_ty = state.metas.instantiate(&decl.ty);
            if let Some(inner_neg) = match_not(&hyp_ty) {
                if let Some((hyp_a, hyp_b)) = match_and(&inner_neg) {
                    // Check if we have ¬(A ∧ B) where A and B match our goal
                    let a_matches = state.is_def_eq(&goal, &hyp_a, &inner_a);
                    let b_matches = state.is_def_eq(&goal, &hyp_b, &inner_b);

                    if a_matches && b_matches {
                        // Found matching hypothesis ¬(A ∧ B)
                        // Proof: by_cases on A
                        let hyp_name_for_cases = decl.name.clone();
                        let goals_backup = state.goals.clone();

                        let h_name = fresh_hyp_name(&goal.local_ctx, "hCase");
                        if by_cases(state, &h_name, inner_a.clone()).is_ok() {
                            // Case 1: A holds
                            // Goal is ¬A ∨ ¬B, prove via right → ¬B
                            if right_(state).is_ok() {
                                // Now goal is ¬B = B → False
                                let h_b_name = fresh_hyp_name(
                                    &state.current_goal().ok_or(TacticError::NoGoals)?.local_ctx,
                                    "hB",
                                );
                                if intro(state, &h_b_name).is_ok() {
                                    // Goal is False, we have hCase : A, hB : B
                                    // Apply the original hypothesis ¬(A ∧ B) to And.intro hCase hB
                                    let goal2 =
                                        state.current_goal().ok_or(TacticError::NoGoals)?.clone();

                                    // Find fvars for hCase and hB
                                    let h_case_fvar = goal2
                                        .local_ctx
                                        .iter()
                                        .find(|d| d.name == h_name)
                                        .map(|d| d.fvar);
                                    let h_b_fvar = goal2
                                        .local_ctx
                                        .iter()
                                        .find(|d| d.name == h_b_name)
                                        .map(|d| d.fvar);
                                    let not_and_fvar = goal2
                                        .local_ctx
                                        .iter()
                                        .find(|d| d.name == hyp_name_for_cases)
                                        .map(|d| d.fvar);

                                    if let (Some(h_a), Some(h_b), Some(h_not_and)) =
                                        (h_case_fvar, h_b_fvar, not_and_fvar)
                                    {
                                        // Build And.intro h_a h_b
                                        let and_intro =
                                            Expr::const_(Name::from_string("And.intro"), vec![]);
                                        let and_intro_a = Expr::app(and_intro, inner_a.clone());
                                        let and_intro_ab = Expr::app(and_intro_a, inner_b.clone());
                                        let and_intro_ha = Expr::app(and_intro_ab, Expr::fvar(h_a));
                                        let and_proof = Expr::app(and_intro_ha, Expr::fvar(h_b));

                                        // Apply h_not_and to and_proof
                                        let proof = Expr::app(Expr::fvar(h_not_and), and_proof);
                                        if exact(state, proof).is_ok() {
                                            // Case 1 complete, now handle Case 2
                                            // Case 2: ¬A holds, goal is ¬A ∨ ¬B
                                            if state.goals.is_empty() {
                                                return Ok(true);
                                            }
                                            // Goal 2 should be ¬A ∨ ¬B with h : ¬A
                                            if left_(state).is_ok() {
                                                // Goal is ¬A, we have assumption
                                                if assumption(state).is_ok() {
                                                    return Ok(true);
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }

                        // Restore on failure
                        state.invalidate_tc_cache();
                        state.goals = goals_backup;
                    }
                }
            }
        }
    }

    Ok(false)
}
