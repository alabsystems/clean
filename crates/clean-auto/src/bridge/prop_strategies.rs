// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Hypothesis-combining proof strategies for propositional reconstruction (#2442 Phase 2B).
//!
//! Extracted from `prop_reconstruction.rs` to keep file sizes under 500 lines.
//! Contains strategies that combine hypotheses with assumption-based reasoning:
//! - Modus ponens from Implies-typed hypotheses
//! - Iff decomposition from Iff-typed hypotheses
//! - Or.elim case analysis from Or-typed hypotheses
//! - Assumption-based proof search (for Or.elim branches)
//!
//! Eq.mp/Eq.mpr propositional rewriting is in `prop_eq_rewrite.rs` (Phase 2C).

use crate::proof::ProofStep;
use clean_kernel::{BinderInfo, Expr};

use super::arith_chain::{
    detect_sort, mk_chain_step, mk_lt_irrefl_false, mk_nat_ground_le, ArithSort, CmpOp,
};
use super::disjunction::{
    mk_absurd, mk_constant_or_motive, mk_false_elim, mk_iff_mp, mk_iff_mpr, mk_or_rec,
};
use super::expr_classifier::{classify_expr, LogicalForm};
use super::translate::ExprKey;
use super::{BridgeError, BridgeResult, SmtBridge};

/// Build the `False` constant expression.
pub(super) fn mk_false_const() -> Expr {
    Expr::const_(clean_kernel::name::Name::from_string("False"), vec![])
}

impl<'env> SmtBridge<'env> {
    /// Try modus ponens from Implies-typed hypotheses (#2442 Phase 2B).
    ///
    /// For any goal G, searches for hypothesis `h : P → G` where P is provable
    /// from existing hypotheses. Builds: `h p_proof`.
    pub(super) fn try_modus_ponens(
        &self,
        goal_expr: &Expr,
        depth: u32,
    ) -> BridgeResult<(ProofStep, Expr)> {
        let goal_key = ExprKey::from_expr(goal_expr);
        if goal_key.is_none() {
            return Err(BridgeError::UnsupportedExpr {
                context: "modus_ponens: goal not classifiable".into(),
            });
        }
        for (fvar_id, hyp_type) in self.iter_guided_hypotheses() {
            let hyp_class = self.classify_prop(hyp_type);
            if let LogicalForm::Implies(ref ante, ref cons) = hyp_class {
                let cons_key = ExprKey::from_expr(cons);
                if cons_key == goal_key {
                    // h : P → G. Try to prove P.
                    let ante_class = self.classify_prop(ante);
                    if let Ok((_, p_proof)) =
                        self.build_prop_proof_inner(&ante_class, ante, depth + 1)
                    {
                        let h = Expr::fvar(fvar_id);
                        let proof = Expr::app(h, p_proof);
                        return Ok((ProofStep::Propositional("modus_ponens".into()), proof));
                    }
                }
            }
        }
        Err(BridgeError::UnsupportedExpr {
            context: "modus_ponens: no applicable implication hypothesis".into(),
        })
    }

    /// Try Iff decomposition from Iff-typed hypotheses (#2442 Phase 2).
    ///
    /// For any goal G, searches for hypothesis `h : Iff(P, Q)` where:
    /// - G matches Q and P is provable → `Iff.mp h p_proof`
    /// - G matches P and Q is provable → `Iff.mpr h q_proof`
    pub(super) fn try_iff_hypothesis(
        &self,
        goal_expr: &Expr,
        depth: u32,
    ) -> BridgeResult<(ProofStep, Expr)> {
        let goal_key = ExprKey::from_expr(goal_expr);
        if goal_key.is_none() {
            return Err(BridgeError::UnsupportedExpr {
                context: "iff_hypothesis: goal not classifiable".into(),
            });
        }
        for (fvar_id, hyp_type) in self.iter_guided_hypotheses() {
            // Use classify_expr (not classify_prop) to preserve Iff structure.
            // classify_prop folds Iff(P,Q) to And(P→Q, Q→P) which hides the Iff.
            let hyp_class = classify_expr(hyp_type);
            if let LogicalForm::Iff(ref p, ref q) = hyp_class {
                let p_key = ExprKey::from_expr(p);
                let q_key = ExprKey::from_expr(q);
                // goal = Q, P provable → Iff.mp h p_proof
                if goal_key == q_key {
                    let p_class = self.classify_prop(p);
                    if let Ok((_, p_proof)) = self.build_prop_proof_inner(&p_class, p, depth + 1) {
                        let h = Expr::fvar(fvar_id);
                        let proof = mk_iff_mp(p, q, &h, &p_proof);
                        return Ok((ProofStep::Propositional("Iff.mp".into()), proof));
                    }
                }
                // goal = P, Q provable → Iff.mpr h q_proof
                if goal_key == p_key {
                    let q_class = self.classify_prop(q);
                    if let Ok((_, q_proof)) = self.build_prop_proof_inner(&q_class, q, depth + 1) {
                        let h = Expr::fvar(fvar_id);
                        let proof = mk_iff_mpr(p, q, &h, &q_proof);
                        return Ok((ProofStep::Propositional("Iff.mpr".into()), proof));
                    }
                }
            }
        }
        Err(BridgeError::UnsupportedExpr {
            context: "iff_hypothesis: no applicable Iff hypothesis".into(),
        })
    }

    /// Try Or.elim case analysis from Or-typed hypotheses (#2442 Phase 2B).
    ///
    /// For any goal G, searches for hypothesis `h : A ∨ B` where G is provable
    /// from A alone and from B alone. Builds:
    /// ```text
    /// Or.rec A B (fun _ : Or A B => G) (fun (a : A) => left_proof) (fun (b : B) => right_proof) h
    /// ```
    pub(super) fn try_or_elim(
        &self,
        goal_class: &LogicalForm,
        goal_expr: &Expr,
        depth: u32,
    ) -> BridgeResult<(ProofStep, Expr)> {
        for (fvar_id, hyp_type) in self.iter_guided_hypotheses() {
            // Skip hypotheses already being eliminated higher on the call stack.
            // Without this guard, build_prop_proof_inner → try_or_elim → try_prove_under_assumption
            // → build_prop_proof_inner → try_or_elim re-enters with the same Or hypothesis,
            // producing deeply nested Or.rec terms. (#2442)
            if self.or_elim_active.borrow().contains(&fvar_id) {
                continue;
            }
            let hyp_class = self.classify_prop(hyp_type);
            if let LogicalForm::Or(ref a, ref b) = hyp_class {
                self.or_elim_active.borrow_mut().push(fvar_id);
                let left_proof = self.try_prove_under_assumption(a, goal_class, goal_expr, depth);
                // Short-circuit: skip right branch if left fails (avoids exponential blowup
                // from mutual recursion with build_prop_proof_inner)
                let result = if let Some(left_body) = left_proof {
                    let right_proof =
                        self.try_prove_under_assumption(b, goal_class, goal_expr, depth);
                    if let Some(right_body) = right_proof {
                        let f_inl = Expr::lam(BinderInfo::Default, a.clone(), left_body);
                        let f_inr = Expr::lam(BinderInfo::Default, b.clone(), right_body);
                        let motive = mk_constant_or_motive(a, b, goal_expr);
                        let h = Expr::fvar(fvar_id);
                        let proof = mk_or_rec(a, b, &motive, &f_inl, &f_inr, &h);
                        Some(proof)
                    } else {
                        None
                    }
                } else {
                    None
                };
                self.or_elim_active.borrow_mut().retain(|&id| id != fvar_id);
                if let Some(proof) = result {
                    return Ok((ProofStep::Propositional("Or.elim".into()), proof));
                }
            }
        }
        Err(BridgeError::UnsupportedExpr {
            context: "or_elim: no applicable disjunction hypothesis".into(),
        })
    }

    pub(super) fn try_assumption_arithmetic_false(&self, assumption_type: &Expr) -> Option<Expr> {
        let assumption = Expr::bvar(0);
        match self.classify_prop(assumption_type) {
            LogicalForm::Lt { ty, lhs, rhs } => {
                self.try_ground_strict_assumption_false(&ty, &lhs, &rhs, &assumption)
            }
            LogicalForm::Gt { ty, lhs, rhs } => {
                self.try_ground_strict_assumption_false(&ty, &rhs, &lhs, &assumption)
            }
            _ => None,
        }
    }

    fn try_ground_strict_assumption_false(
        &self,
        ty: &Expr,
        lhs: &Expr,
        rhs: &Expr,
        assumption: &Expr,
    ) -> Option<Expr> {
        let sort = detect_sort(ty)?;
        if sort != ArithSort::Nat {
            return None;
        }

        let backward = mk_nat_ground_le(rhs, lhs)?;
        let cycle = mk_chain_step(
            sort,
            lhs,
            rhs,
            lhs,
            CmpOp::Lt,
            CmpOp::Le,
            assumption,
            &backward,
        );
        Some(mk_lt_irrefl_false(sort, lhs, &cycle))
    }

    /// assumption = P (bvar 0), hypothesis h_neg : ¬P → absurd → False.elim goal
    pub(super) fn try_assumption_absurd(
        &self,
        assumption_type: &Expr,
        goal_expr: &Expr,
    ) -> Option<Expr> {
        let assumption_key = ExprKey::from_expr(assumption_type);
        for (neg_fvar, neg_type) in self.iter_guided_hypotheses() {
            let neg_class = self.classify_prop(neg_type);
            if let LogicalForm::Not(ref inner) = neg_class {
                let inner_key = ExprKey::from_expr(inner);
                if assumption_key == inner_key {
                    let hp = Expr::bvar(0);
                    let h_neg = Expr::fvar(neg_fvar);
                    let false_proof = mk_absurd(assumption_type, &mk_false_const(), &hp, &h_neg);
                    return Some(mk_false_elim(goal_expr, &false_proof));
                }
            }
        }
        None
    }

    /// assumption = P (bvar 0), hypothesis h : P → G → h (bvar 0)
    pub(super) fn try_assumption_modus_ponens(
        &self,
        assumption_type: &Expr,
        goal_expr: &Expr,
    ) -> Option<Expr> {
        let assumption_key = ExprKey::from_expr(assumption_type);
        let goal_key = ExprKey::from_expr(goal_expr);
        for (fvar_id, hyp_type) in self.iter_guided_hypotheses() {
            let hyp_class = self.classify_prop(hyp_type);
            if let LogicalForm::Implies(ref ante, ref cons) = hyp_class {
                let ante_key = ExprKey::from_expr(ante);
                let cons_key = ExprKey::from_expr(cons);
                if ante_key == assumption_key && cons_key.is_some() && cons_key == goal_key {
                    let hp = Expr::bvar(0);
                    let h = Expr::fvar(fvar_id);
                    return Some(Expr::app(h, hp));
                }
            }
        }
        None
    }

    /// assumption = ¬P (bvar 0), hypothesis h_pos : P → absurd → False.elim goal
    pub(super) fn try_neg_assumption_absurd(
        &self,
        assumption_type: &Expr,
        goal_expr: &Expr,
    ) -> Option<Expr> {
        let assumption_class = self.classify_prop(assumption_type);
        if let LogicalForm::Not(ref inner) = assumption_class {
            let inner_key = ExprKey::from_expr(inner);
            if inner_key.is_some() {
                for (pos_fvar, pos_type) in self.iter_guided_hypotheses() {
                    let pos_key = ExprKey::from_expr(pos_type);
                    if pos_key == inner_key {
                        let h_neg = Expr::bvar(0);
                        let h_pos = Expr::fvar(pos_fvar);
                        let false_proof = mk_absurd(inner, &mk_false_const(), &h_pos, &h_neg);
                        return Some(mk_false_elim(goal_expr, &false_proof));
                    }
                }
            }
        }
        None
    }
}
