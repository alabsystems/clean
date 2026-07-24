// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Propositional proof reconstruction for the SMT-Kernel Bridge (#2442).
//!
//! Builds Lean kernel proof terms for non-equality goals from DPLL(T) UNSAT
//! results. Phase 1 (commit 6c869d4) handled True, And, False, and hypothesis
//! match. Phase 2A adds Or (Or.inl/Or.inr), Implies (lambda), Not (lambda +
//! absurd), and And decomposition from hypotheses (And.left/And.right).
//! Phase 2B adds lambda-parameter-aware proof reconstruction: Not/Implies
//! handlers now use the introduced binder (bvar 0) in the lambda body,
//! enabling absurd/modus-ponens proofs that depend on the lambda argument.
//! Also adds Or.elim case analysis on Or-typed hypotheses and modus ponens
//! from Implies-typed hypotheses.
//! Phase 2C adds Eq.mp/Eq.mpr propositional rewriting: transport proofs along
//! propositional equalities (grind-style `closeGoalWithTrueEqFalse` pattern).
//! Phase 3 adds sub-goal handling for types that previously only had top-level
//! support: Eq.refl for reflexive equality sub-goals, Le/Lt/Ge/Gt delegation
//! to direct arithmetic reconstruction, and Forall via lambda introduction.
//! Phase 3B adds non-reflexive equality sub-goal handling: Eq.symm for reversed
//! equality hypotheses and Eq.trans for one-step transitivity chains.
//!
//! # Supported goal forms
//!
//! | Goal form | Proof strategy |
//! |-----------|----------------|
//! | Direct hypothesis match | `Expr::fvar(h)` |
//! | And hypothesis decomposition | `And.left h` / `And.right h` |
//! | Modus ponens | `h p_proof` where `h : P → G` and `p_proof : P` |
//! | Eq.mp/Eq.mpr rewriting | `Eq.mp h lhs_proof` or `Eq.mpr h rhs_proof` |
//! | Or.elim from hypothesis | `Or.rec ... h` where `h : A ∨ B` |
//! | Exists.elim from hypothesis | `Exists.elim h (fun x hx => body_proof)` |
//! | `True` | `True.intro` |
//! | `And(P, Q)` | `And.intro p_proof q_proof` |
//! | `Or(P, Q)` | `Or.inl p_proof` or `Or.inr q_proof` |
//! | `P → Q` | `fun (hp : P) => q_proof` (q_proof may use `hp` via bvar) |
//! | `¬P` | `fun (hp : P) => absurd hp h_neg` or `fun (_ : P) => false_proof` |
//! | `False` | `False.elim goal false_proof` or `absurd h_pos h_neg` |
//! | `Eq(α, a, a)` | `Eq.refl a` (reflexive sub-goals) |
//! | `Eq(α, a, b)` | `Eq.symm h` where `h : b = a` |
//! | `Eq(α, a, c)` | `Eq.trans h₁ h₂` where `h₁ : a = b`, `h₂ : b = c` |
//! | `Le/Lt/Ge/Gt` | Direct arithmetic reconstruction |
//! | `∀ x : α, P x` | `fun (x : α) => body_proof` |
//! | `∃ x : α, P x` | `Exists.intro witness body_proof` with in-scope/closed witness |

use crate::proof::ProofStep;
use clean_kernel::{BinderInfo, Expr, FVarId};

use super::disjunction::{
    mk_absurd, mk_and_intro, mk_and_left, mk_and_right, mk_classical_em, mk_false_elim, mk_or_inl,
    mk_or_inr, mk_or_swap, mk_true_intro,
};
use super::eq_proof_builders::mk_eq_refl;
use super::expr_classifier::LogicalForm;
use super::translate::ExprKey;
use super::{BridgeError, BridgeResult, SmtBridge};

/// Maximum recursion depth for propositional proof reconstruction.
/// Reduced from 100 to 50 after OOM incidents (gamma-crown#3502, clean#2489):
/// depth 100 with mutual recursion through try_or_elim ↔ try_prove_under_assumption
/// allowed search trees large enough to consume 106GB RSS on pathological inputs.
const MAX_PROP_RECONSTRUCTION_DEPTH: u32 = 50;

impl<'env> SmtBridge<'env> {
    /// Build a propositional proof for a non-equality goal (#2442).
    pub(crate) fn build_propositional_proof(
        &self,
        goal_class: &LogicalForm,
        goal_expr: &Expr,
    ) -> BridgeResult<(ProofStep, Expr)> {
        // Reset node budget for each top-level proof attempt (#2489)
        self.prop_reconstruction_budget.set(10_000);
        self.build_prop_proof_inner(goal_class, goal_expr, 0)
    }

    /// Inner recursive propositional proof builder with depth bound.
    pub(super) fn build_prop_proof_inner(
        &self,
        goal_class: &LogicalForm,
        goal_expr: &Expr,
        depth: u32,
    ) -> BridgeResult<(ProofStep, Expr)> {
        if depth > MAX_PROP_RECONSTRUCTION_DEPTH {
            return Err(BridgeError::ProofTraceFailed(
                "propositional proof reconstruction depth exceeded".into(),
            ));
        }

        // Node-count budget: prevents OOM from exponential branching (#2489)
        let remaining = self.prop_reconstruction_budget.get();
        if remaining == 0 {
            return Err(BridgeError::ProofTraceFailed(
                "propositional proof reconstruction node budget exhausted".into(),
            ));
        }
        self.prop_reconstruction_budget.set(remaining - 1);

        // First try direct hypothesis match — works for any goal form
        if let Ok(result) = self.try_hypothesis_match(goal_expr) {
            return Ok(result);
        }

        // Try modus ponens: if h : P → G exists and P is provable, use h p_proof
        if let Ok(result) = self.try_modus_ponens(goal_expr, depth) {
            return Ok(result);
        }

        // Try Iff decomposition: if h : Iff(P, Q) exists, use Iff.mp or Iff.mpr
        if let Ok(result) = self.try_iff_hypothesis(goal_expr, depth) {
            return Ok(result);
        }

        // Try Eq.mp/Eq.mpr rewriting: if h : Eq(ty, P, Q) exists, transport
        // proof terms along propositional equalities (grind-style pattern #2442)
        if let Ok(result) = self.try_eq_rewrite(goal_expr, depth) {
            return Ok(result);
        }

        // Try Or.elim: if h : A ∨ B exists and G is provable from A and from B
        if let Ok(result) = self.try_or_elim(goal_class, goal_expr, depth) {
            return Ok(result);
        }

        if let Ok(result) = self.try_exists_elim(goal_class, goal_expr, depth) {
            return Ok(result);
        }

        let result = match goal_class {
            LogicalForm::True => {
                let proof = mk_true_intro();
                Ok((ProofStep::Propositional("True.intro".into()), proof))
            }
            LogicalForm::And(p, q) => {
                let p_class = self.classify_prop(p);
                let q_class = self.classify_prop(q);
                let (_, p_proof) = self.build_prop_proof_inner(&p_class, p, depth + 1)?;
                let (_, q_proof) = self.build_prop_proof_inner(&q_class, q, depth + 1)?;
                let proof = mk_and_intro(p, q, &p_proof, &q_proof);
                Ok((ProofStep::Propositional("And.intro".into()), proof))
            }
            LogicalForm::Or(p, q) => {
                // P ∨ Q: try proving left disjunct (→ Or.inl), then right (→ Or.inr)
                let p_class = self.classify_prop(p);
                if let Ok((_, p_proof)) = self.build_prop_proof_inner(&p_class, p, depth + 1) {
                    let proof = mk_or_inl(p, q, &p_proof);
                    return Ok((ProofStep::Propositional("Or.inl".into()), proof));
                }
                let q_class = self.classify_prop(q);
                if let Ok((_, q_proof)) = self.build_prop_proof_inner(&q_class, q, depth + 1) {
                    let proof = mk_or_inr(p, q, &q_proof);
                    return Ok((ProofStep::Propositional("Or.inr".into()), proof));
                }
                // Classical.em: cover both `P ∨ ¬P` and `¬P ∨ P`.
                // Part of #302: eliminates trustedAy for excluded-middle tautologies
                // regardless of disjunct ordering.
                if let LogicalForm::Not(inner) = &p_class {
                    if inner == q {
                        let proof = mk_or_swap(q, p, &mk_classical_em(q));
                        return Ok((ProofStep::Propositional("Classical.em".into()), proof));
                    }
                }
                if let LogicalForm::Not(inner) = &q_class {
                    if inner == p {
                        let proof = mk_classical_em(p);
                        return Ok((ProofStep::Propositional("Classical.em".into()), proof));
                    }
                }
                // Classical split: case-split on P ∨ ¬P via Classical.em,
                // then prove the Or goal in each branch (#2442 Phase 2).
                if let Some(proof) = self.try_or_via_classical_split(p, q, goal_expr, depth) {
                    return Ok((ProofStep::Propositional("Or.classical_split".into()), proof));
                }
                Err(BridgeError::ProofTraceFailed(
                    "Or: neither disjunct provable and not excluded middle".into(),
                ))
            }
            LogicalForm::Implies(p, q) => self.build_implies_proof(p, q, depth),
            LogicalForm::Not(p) => self.build_not_proof(p, depth),
            LogicalForm::False => {
                if let Some((fvar_id, _)) = self.find_hypothesis_by_form(&LogicalForm::False) {
                    let proof = mk_false_elim(goal_expr, &Expr::fvar(fvar_id));
                    Ok((ProofStep::Propositional("False.elim".into()), proof))
                } else if let Some(proof) = self.try_absurd_from_hypotheses(goal_expr) {
                    Ok((ProofStep::Propositional("absurd".into()), proof))
                } else {
                    Err(BridgeError::UnsupportedExpr {
                        context: "propositional: cannot derive False without False hypothesis"
                            .into(),
                    })
                }
            }
            LogicalForm::Iff(p, q) => {
                // Iff(P, Q) = Iff.intro P Q (fun hp : P => q_proof) (fun hq : Q => p_proof)
                let (_, mp) = self.build_implies_proof(p, q, depth)?;
                let (_, mpr) = self.build_implies_proof(q, p, depth)?;
                let proof = Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::app(
                                Expr::const_(
                                    clean_kernel::name::Name::from_string("Iff.intro"),
                                    vec![],
                                ),
                                p.clone(),
                            ),
                            q.clone(),
                        ),
                        mp,
                    ),
                    mpr,
                );
                Ok((ProofStep::Propositional("Iff.intro".into()), proof))
            }
            LogicalForm::Neq { ty, lhs, rhs } => {
                // Neq(a, b) = ¬(a = b). classify_prop normally folds this to Not(eq_expr),
                // but if sort_level_of_type failed it stays as Neq. Build the Eq expression
                // and delegate to Not proof (#2442 Phase 2).
                let eq_form = LogicalForm::Eq {
                    ty: ty.clone(),
                    lhs: lhs.clone(),
                    rhs: rhs.clone(),
                };
                let eq_expr = self.logicalform_to_expr(&eq_form)?;
                self.build_not_proof(&eq_expr, depth)
            }
            // Equality sub-goals (#2442 Phase 3 + Phase 3B).
            // Phase 3: Eq.refl for reflexive sub-goals (a = a).
            // Phase 3B: Eq.symm/Eq.trans from equality hypotheses.
            LogicalForm::Eq { ty, lhs, rhs } => {
                let lhs_key = ExprKey::from_expr(lhs);
                let rhs_key = ExprKey::from_expr(rhs);
                let is_reflexive = match (&lhs_key, &rhs_key) {
                    (Some(lhs_key), Some(rhs_key)) => lhs_key == rhs_key,
                    _ => lhs.strip_mdata() == rhs.strip_mdata(),
                };
                // Eq.refl: lhs == rhs. Fall back to direct stripped Expr equality
                // when ExprKey intentionally declines to hash Let/Proj/Sort forms.
                if is_reflexive {
                    if let Ok(u) = self.sort_level_of_type(ty) {
                        let proof = mk_eq_refl(&u, ty, lhs);
                        return Ok((ProofStep::Propositional("Eq.refl".into()), proof));
                    }
                }
                // Eq.symm: hypothesis h : Eq(ty, rhs, lhs)
                if let Ok(result) = self.try_eq_symm_subgoal(ty, lhs, rhs) {
                    return Ok(result);
                }
                // Eq.trans: hypotheses h1 : Eq(ty, lhs, mid), h2 : Eq(ty, mid, rhs)
                if let Ok(result) = self.try_eq_trans_subgoal(ty, lhs, rhs) {
                    return Ok(result);
                }
                Err(BridgeError::UnsupportedExpr {
                    context: "propositional: Eq sub-goal not provable from hypotheses".into(),
                })
            }
            // Comparison sub-goals: delegate to direct arithmetic reconstruction
            // (#2442 Phase 3). Handles Le/Lt/Ge/Gt that appear as sub-goals of
            // compound propositional goals (e.g., And(Le(Nat, 0, 1), True)).
            LogicalForm::Le { .. }
            | LogicalForm::Lt { .. }
            | LogicalForm::Ge { .. }
            | LogicalForm::Gt { .. } => self.build_direct_arithmetic_goal_proof(goal_class),
            // Forall sub-goals: introduce the bound variable via lambda and
            // recursively prove the body (#2442 Phase 3). This mirrors the
            // Implies handler but preserves the dependent binder.
            LogicalForm::Forall { binder_type, body } => {
                let body_class = self.classify_prop(body);
                let (_, body_proof) = self.build_prop_proof_inner(&body_class, body, depth + 1)?;
                let proof = Expr::lam(BinderInfo::Default, binder_type.clone(), body_proof);
                Ok((ProofStep::Propositional("Forall.lam".into()), proof))
            }
            // Exists sub-goals: choose a witness already valid in the goal
            // context (local variable) or a closed monomorphic constant, then
            // recursively prove the instantiated body.
            LogicalForm::Exists { binder_type, body } => {
                self.build_exists_proof(goal_expr, binder_type, body, depth)
            }
            _ => Err(BridgeError::UnsupportedExpr {
                context: "propositional proof reconstruction: no matching strategy".into(),
            }),
        };

        result.or_else(|original_error| self.try_ex_falso(goal_expr).ok_or(original_error))
    }

    // build_implies_proof, build_not_proof, try_implies_modus_ponens_with_bvar,
    // try_implies_via_absurd are in prop_lambda_proofs.rs
    // try_eq_symm_subgoal, try_eq_trans_subgoal are in prop_eq_subgoals.rs

    /// Try to find a hypothesis whose type matches the goal expression.
    ///
    /// Also searches And hypotheses for decomposed sub-proofs (#2442 Phase 2):
    /// - `h : A ∧ B` where `A` matches goal → `And.left h` (projection `.1`)
    /// - `h : A ∧ B` where `B` matches goal → `And.right h` (projection `.2`)
    fn try_hypothesis_match(&self, goal_expr: &Expr) -> BridgeResult<(ProofStep, Expr)> {
        let goal_key = ExprKey::from_expr(goal_expr);
        for (fvar_id, hyp_type) in self.iter_guided_hypotheses() {
            // Direct match: hypothesis type equals goal
            let hyp_key = ExprKey::from_expr(hyp_type);
            if goal_key.is_some() && goal_key == hyp_key {
                return Ok((
                    ProofStep::Propositional("hypothesis_match".into()),
                    Expr::fvar(fvar_id),
                ));
            }

            // And decomposition: hypothesis is A ∧ B, check if A or B matches goal
            let hyp_class = self.classify_prop(hyp_type);
            if let LogicalForm::And(ref left, ref right) = hyp_class {
                let left_key = ExprKey::from_expr(left);
                if goal_key.is_some() && goal_key == left_key {
                    let proof = mk_and_left(&Expr::fvar(fvar_id));
                    return Ok((ProofStep::Propositional("And.left".into()), proof));
                }
                let right_key = ExprKey::from_expr(right);
                if goal_key.is_some() && goal_key == right_key {
                    let proof = mk_and_right(&Expr::fvar(fvar_id));
                    return Ok((ProofStep::Propositional("And.right".into()), proof));
                }
            }
        }
        Err(BridgeError::UnsupportedExpr {
            context: "propositional: no hypothesis matches goal".into(),
        })
    }

    /// Find a tracked hypothesis matching a logical form.
    pub(super) fn find_hypothesis_by_form(&self, target: &LogicalForm) -> Option<(FVarId, Expr)> {
        for (fvar_id, hyp_type) in self.iter_guided_hypotheses() {
            let hyp_class = self.classify_prop(hyp_type);
            if logical_form_tag_matches(&hyp_class, target) {
                return Some((fvar_id, hyp_type.clone()));
            }
        }
        None
    }

    /// Try to prove any goal from a tracked `False` or tracked contradiction.
    fn try_ex_falso(&self, target: &Expr) -> Option<(ProofStep, Expr)> {
        if let Some((fvar_id, _)) = self.find_hypothesis_by_form(&LogicalForm::False) {
            let proof = mk_false_elim(target, &Expr::fvar(fvar_id));
            return Some((ProofStep::Propositional("False.elim".into()), proof));
        }

        self.try_absurd_from_hypotheses(target)
            .map(|proof| (ProofStep::Propositional("absurd".into()), proof))
    }

    /// Try to derive False from a contradictory hypothesis pair.
    ///
    /// Searches for a positive hypothesis `h_pos : P` and a negative hypothesis
    /// `h_neg : ¬P` where the inner expression of ¬P matches P. If found,
    /// builds `absurd h_pos h_neg : target`.
    fn try_absurd_from_hypotheses(&self, target: &Expr) -> Option<Expr> {
        let negatives: Vec<(FVarId, Expr)> = self
            .iter_guided_hypotheses()
            .filter_map(|(fvar_id, hyp_type)| {
                let hyp_class = self.classify_prop(hyp_type);
                if let LogicalForm::Not(inner) = hyp_class {
                    Some((fvar_id, inner))
                } else {
                    None
                }
            })
            .collect();

        if negatives.is_empty() {
            return None;
        }

        for (pos_fvar, pos_type) in self.iter_guided_hypotheses() {
            let pos_key = ExprKey::from_expr(pos_type);
            if pos_key.is_none() {
                continue;
            }
            for (neg_fvar, neg_inner) in &negatives {
                let neg_key = ExprKey::from_expr(neg_inner);
                if pos_key == neg_key {
                    return Some(mk_absurd(
                        pos_type,
                        target,
                        &Expr::fvar(pos_fvar),
                        &Expr::fvar(*neg_fvar),
                    ));
                }
            }
        }
        None
    }
}

/// Check if two LogicalForm variants match structurally (tag only, not content).
fn logical_form_tag_matches(a: &LogicalForm, b: &LogicalForm) -> bool {
    matches!(
        (a, b),
        (LogicalForm::True, LogicalForm::True) | (LogicalForm::False, LogicalForm::False)
    )
}
