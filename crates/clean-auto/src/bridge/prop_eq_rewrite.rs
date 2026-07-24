// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Eq.mp/Eq.mpr propositional rewriting for proof reconstruction (#2442 Phase 2C).
//!
//! Implements the grind-style `closeGoalWithTrueEqFalse` pattern from Lean 4:
//! transport proofs along propositional equalities using `Eq.mp` (forward) and
//! `Eq.mpr` (backward). When the DPLL(T) E-graph establishes propositional
//! equalities (e.g., `P = True`), this module enables proof reconstruction
//! without falling back to trustedAy.
//!
//! Two strategies:
//! - `try_eq_rewrite`: top-level strategy searching Eq-typed hypotheses
//! - `try_eq_rewrite_under_assumption`: for Or.elim branches where the
//!   assumption is an Eq-typed expression

use crate::proof::ProofStep;
use clean_kernel::{Expr, Level};

use super::disjunction::mk_true_intro;
use super::eq_proof_builders::{mk_eq_mp, mk_eq_mpr};
use super::expr_classifier::LogicalForm;
use super::translate::ExprKey;
use super::{BridgeError, BridgeResult, SmtBridge};

impl<'env> SmtBridge<'env> {
    /// Try propositional Eq.mp/Eq.mpr rewriting from Eq-typed hypotheses (#2442 Phase 2C).
    ///
    /// For any goal G, searches for hypothesis `h : Eq(ty, lhs, rhs)` where:
    /// - `lhs` matches G and `rhs` is provable → `Eq.mpr h rhs_proof : G`
    /// - `rhs` matches G and `lhs` is provable → `Eq.mp h lhs_proof : G`
    ///
    /// Special case (grind pattern): if one side is `True`, use `True.intro` directly.
    /// This implements the key `closeGoalWithTrueEqFalse` pattern from Lean 4 grind.
    pub(super) fn try_eq_rewrite(
        &self,
        goal_expr: &Expr,
        depth: u32,
    ) -> BridgeResult<(ProofStep, Expr)> {
        let goal_key = ExprKey::from_expr(goal_expr);
        if goal_key.is_none() {
            return Err(BridgeError::UnsupportedExpr {
                context: "eq_rewrite: goal not classifiable".into(),
            });
        }
        let u = Level::zero(); // propositions live in Sort 0
        for (fvar_id, hyp_type) in self.iter_guided_hypotheses() {
            let hyp_class = self.classify_prop(hyp_type);
            if let LogicalForm::Eq {
                ty: _,
                ref lhs,
                ref rhs,
            } = hyp_class
            {
                let lhs_key = ExprKey::from_expr(lhs);
                let rhs_key = ExprKey::from_expr(rhs);
                let h = Expr::fvar(fvar_id);

                // goal = lhs, try proving rhs → Eq.mpr h rhs_proof
                if goal_key == lhs_key {
                    let rhs_class = self.classify_prop(rhs);
                    if let Ok((_, rhs_proof)) =
                        self.build_prop_proof_inner(&rhs_class, rhs, depth + 1)
                    {
                        let proof = mk_eq_mpr(&u, lhs, rhs, &h, &rhs_proof);
                        return Ok((ProofStep::Propositional("Eq.mpr".into()), proof));
                    }
                }

                // goal = rhs, try proving lhs → Eq.mp h lhs_proof
                if goal_key == rhs_key {
                    let lhs_class = self.classify_prop(lhs);
                    if let Ok((_, lhs_proof)) =
                        self.build_prop_proof_inner(&lhs_class, lhs, depth + 1)
                    {
                        let proof = mk_eq_mp(&u, lhs, rhs, &h, &lhs_proof);
                        return Ok((ProofStep::Propositional("Eq.mp".into()), proof));
                    }
                }
            }
        }
        Err(BridgeError::UnsupportedExpr {
            context: "eq_rewrite: no applicable Eq hypothesis for propositional transport".into(),
        })
    }

    /// Try Eq.mp/Eq.mpr transport under an assumption (for Or.elim branches).
    ///
    /// If assumption is `Eq(ty, lhs, rhs)`:
    /// - goal = lhs, rhs provable → `Eq.mpr (bvar 0) rhs_proof`
    /// - goal = rhs, lhs provable → `Eq.mp (bvar 0) lhs_proof`
    /// - goal = lhs, rhs = True → `Eq.mpr (bvar 0) True.intro`
    /// - goal = rhs, lhs = True → `Eq.mp (bvar 0) True.intro`
    pub(super) fn try_eq_rewrite_under_assumption(
        &self,
        assumption_type: &Expr,
        goal_class: &LogicalForm,
        goal_expr: &Expr,
        depth: u32,
    ) -> Option<Expr> {
        let assumption_class = self.classify_prop(assumption_type);
        let LogicalForm::Eq {
            ty: _,
            ref lhs,
            ref rhs,
        } = assumption_class
        else {
            return None;
        };
        let goal_key = ExprKey::from_expr(goal_expr);
        goal_key.as_ref()?;
        let lhs_key = ExprKey::from_expr(lhs);
        let rhs_key = ExprKey::from_expr(rhs);
        let u = Level::zero();
        let h = Expr::bvar(0);

        // goal = lhs, try proving rhs → Eq.mpr (bvar 0) rhs_proof
        if goal_key == lhs_key {
            let rhs_class = self.classify_prop(rhs);
            // Special case: rhs = True → use True.intro directly
            if matches!(rhs_class, LogicalForm::True) {
                return Some(mk_eq_mpr(&u, lhs, rhs, &h, &mk_true_intro()));
            }
            const MAX_INNER: u32 = 45;
            let inner_depth = depth.saturating_add(1).max(MAX_INNER);
            if let Ok((_, rhs_proof)) = self.build_prop_proof_inner(&rhs_class, rhs, inner_depth) {
                return Some(mk_eq_mpr(&u, lhs, rhs, &h, &rhs_proof));
            }
        }

        // goal = rhs, try proving lhs → Eq.mp (bvar 0) lhs_proof
        if goal_key == rhs_key {
            let lhs_class = self.classify_prop(lhs);
            // Special case: lhs = True → use True.intro directly
            if matches!(lhs_class, LogicalForm::True) {
                return Some(mk_eq_mp(&u, lhs, rhs, &h, &mk_true_intro()));
            }
            const MAX_INNER: u32 = 45;
            let inner_depth = depth.saturating_add(1).max(MAX_INNER);
            if let Ok((_, lhs_proof)) = self.build_prop_proof_inner(&lhs_class, lhs, inner_depth) {
                return Some(mk_eq_mp(&u, lhs, rhs, &h, &lhs_proof));
            }
        }

        let _ = goal_class;
        None
    }
}
