// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Classical-split and assumption-only contradiction helpers for #2442.

use clean_kernel::{BinderInfo, Expr};

use super::disjunction::{
    mk_absurd, mk_and_intro, mk_and_left, mk_and_right, mk_classical_em, mk_constant_or_motive,
    mk_false_elim, mk_or_rec,
};
use super::translate::ExprKey;
use super::{LogicalForm, SmtBridge};

impl<'env> SmtBridge<'env> {
    /// Try a bounded `Classical.em` split for disjunction goals whose direct
    /// disjunct proofs failed.
    pub(super) fn try_or_via_classical_split(
        &self,
        left: &Expr,
        right: &Expr,
        goal_expr: &Expr,
        depth: u32,
    ) -> Option<Expr> {
        if depth >= 3 {
            return None;
        }

        let goal_class = self.classify_prop(goal_expr);
        for neg_branch in [left, right] {
            let Some(split_prop) = self.negated_inner(neg_branch) else {
                continue;
            };
            let true_body =
                self.try_prove_under_assumption(&split_prop, &goal_class, goal_expr, depth + 1)?;
            let false_body =
                self.try_prove_under_assumption(neg_branch, &goal_class, goal_expr, depth + 1)?;
            let f_true = Expr::lam(BinderInfo::Default, split_prop.clone(), true_body);
            let f_false = Expr::lam(BinderInfo::Default, neg_branch.clone(), false_body);
            let motive = mk_constant_or_motive(&split_prop, neg_branch, goal_expr);
            let em = mk_classical_em(&split_prop);
            return Some(mk_or_rec(
                &split_prop,
                neg_branch,
                &motive,
                &f_true,
                &f_false,
                &em,
            ));
        }
        None
    }

    pub(super) fn try_contradiction_from_and_assumption(
        &self,
        left: &Expr,
        right: &Expr,
        goal_expr: &Expr,
        goal_class: &LogicalForm,
    ) -> Option<Expr> {
        let left_proof = mk_and_left(&Expr::bvar(0));
        let right_proof = mk_and_right(&Expr::bvar(0));
        let left_key = ExprKey::from_expr(left);
        let right_key = ExprKey::from_expr(right);
        if let LogicalForm::Not(inner) = self.classify_prop(right) {
            let inner_key = ExprKey::from_expr(&inner);
            if left_key.is_some() && left_key == inner_key {
                let false_proof = mk_absurd(left, &self.false_expr(), &left_proof, &right_proof);
                return Some(self.finish_false_assumption(goal_expr, goal_class, false_proof));
            }
        }
        if let LogicalForm::Not(inner) = self.classify_prop(left) {
            let inner_key = ExprKey::from_expr(&inner);
            if right_key.is_some() && right_key == inner_key {
                let false_proof = mk_absurd(right, &self.false_expr(), &right_proof, &left_proof);
                return Some(self.finish_false_assumption(goal_expr, goal_class, false_proof));
            }
        }
        None
    }

    pub(super) fn try_negated_conjunction_hypothesis(
        &self,
        assumption_type: &Expr,
        goal_class: &LogicalForm,
    ) -> Option<Expr> {
        let LogicalForm::Not(goal_inner) = goal_class else {
            return None;
        };

        let assumption_key = ExprKey::from_expr(assumption_type)?;
        let goal_key = ExprKey::from_expr(goal_inner)?;

        for (neg_fvar, neg_type) in self.iter_guided_hypotheses() {
            let LogicalForm::Not(negated) = self.classify_prop(neg_type) else {
                continue;
            };
            let LogicalForm::And(left, right) = self.classify_prop(&negated) else {
                continue;
            };
            let Some(left_key) = ExprKey::from_expr(&left) else {
                continue;
            };
            let Some(right_key) = ExprKey::from_expr(&right) else {
                continue;
            };

            let (left_proof, right_proof, binder_ty) =
                if assumption_key == left_key && goal_key == right_key {
                    (Expr::bvar(1), Expr::bvar(0), right.clone())
                } else if assumption_key == right_key && goal_key == left_key {
                    (Expr::bvar(0), Expr::bvar(1), left.clone())
                } else {
                    continue;
                };

            let pair_proof = mk_and_intro(&left, &right, &left_proof, &right_proof);
            let body = mk_absurd(
                &negated,
                &self.false_expr(),
                &pair_proof,
                &Expr::fvar(neg_fvar),
            );
            return Some(Expr::lam(BinderInfo::Default, binder_ty, body));
        }
        None
    }

    fn negated_inner(&self, expr: &Expr) -> Option<Expr> {
        match self.classify_prop(expr) {
            LogicalForm::Not(inner) => Some(inner),
            _ => None,
        }
    }

    fn finish_false_assumption(
        &self,
        goal_expr: &Expr,
        goal_class: &LogicalForm,
        false_proof: Expr,
    ) -> Expr {
        if matches!(goal_class, LogicalForm::False) {
            false_proof
        } else {
            mk_false_elim(goal_expr, &false_proof)
        }
    }

    fn false_expr(&self) -> Expr {
        Expr::const_(clean_kernel::name::Name::from_string("False"), vec![])
    }
}
