// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Assumption-scoped proof search used by Or.elim and Exists continuations.

use clean_kernel::{BinderInfo, Expr};

use super::disjunction::{
    mk_and_intro, mk_and_left, mk_and_right, mk_constant_or_motive, mk_false_elim, mk_iff_mp,
    mk_iff_mpr, mk_or_inl, mk_or_inr, mk_or_rec,
};
use super::expr_classifier::{classify_expr, LogicalForm};
use super::prop_eq_trans::try_and_eq_trans;
use super::prop_local_assumptions::LocalAssumption;
use super::prop_strategies::mk_false_const;
use super::translate::ExprKey;
use super::SmtBridge;

impl<'env> SmtBridge<'env> {
    /// Try to prove a goal under an additional assumption.
    ///
    /// Used for Or.elim branch proofs: temporarily pretend we have an extra
    /// hypothesis `assumption_type` and try to prove the goal. The proof term
    /// uses `bvar(0)` for the assumption (it will be under a lambda binder).
    ///
    /// Returns the lambda body (proof of goal that may reference bvar 0) or None.
    pub(super) fn try_prove_under_assumption(
        &self,
        assumption_type: &Expr,
        goal_class: &LogicalForm,
        goal_expr: &Expr,
        depth: u32,
    ) -> Option<Expr> {
        let assumption_in_scope = assumption_type.lift(1);
        let (goal_expr_in_scope, goal_class_in_scope) = self.goal_in_new_binder(goal_expr);
        let _ = goal_class;
        self.try_prove_under_assumption_in_scope(
            &assumption_in_scope,
            &goal_class_in_scope,
            &goal_expr_in_scope,
            depth,
        )
    }

    pub(super) fn try_prove_under_assumption_in_scope(
        &self,
        assumption_type: &Expr,
        goal_class: &LogicalForm,
        goal_expr: &Expr,
        depth: u32,
    ) -> Option<Expr> {
        let assumption_key = ExprKey::from_expr(assumption_type);
        let goal_key = ExprKey::from_expr(goal_expr);
        if assumption_key.is_some() && assumption_key == goal_key {
            return Some(Expr::bvar(0));
        }

        if let Some(false_proof) = self.try_assumption_arithmetic_false(assumption_type) {
            if matches!(goal_class, LogicalForm::False) {
                return Some(false_proof);
            }
            return Some(mk_false_elim(goal_expr, &false_proof));
        }

        const MAX_INNER_SEARCH_DEPTH: u32 = 45;
        let inner_depth = depth.saturating_add(1).max(MAX_INNER_SEARCH_DEPTH);
        if let Ok((_, proof)) = self.build_prop_proof_inner(goal_class, goal_expr, inner_depth) {
            return Some(proof);
        }

        let assumption = Expr::bvar(0);
        if let Some(proof) =
            self.try_assumption_guided_equality_term(assumption_type, &assumption, goal_class)
        {
            return Some(proof);
        }

        let assumption_class = self.classify_prop(assumption_type);
        if let LogicalForm::And(ref left, ref right) = assumption_class {
            let left_key = ExprKey::from_expr(left);
            let right_key = ExprKey::from_expr(right);
            if goal_key.is_some() && goal_key == left_key {
                return Some(mk_and_left(&Expr::bvar(0)));
            }
            if goal_key.is_some() && goal_key == right_key {
                return Some(mk_and_right(&Expr::bvar(0)));
            }

            if let Some(proof) =
                try_and_eq_trans(&assumption_class, goal_class, &Expr::bvar(0), self)
            {
                return Some(proof);
            }
            if let Some(proof) =
                self.try_contradiction_from_and_assumption(left, right, goal_expr, goal_class)
            {
                return Some(proof);
            }
        }

        let raw_assumption_class = classify_expr(assumption_type);
        if let LogicalForm::Iff(ref iff_p, ref iff_q) = raw_assumption_class {
            let iff_p_key = ExprKey::from_expr(iff_p);
            let iff_q_key = ExprKey::from_expr(iff_q);
            if goal_key.is_some() && goal_key == iff_q_key {
                let p_class = self.classify_prop(iff_p);
                if let Ok((_, p_proof)) = self.build_prop_proof_inner(&p_class, iff_p, inner_depth)
                {
                    return Some(mk_iff_mp(iff_p, iff_q, &Expr::bvar(0), &p_proof));
                }
            }
            if goal_key.is_some() && goal_key == iff_p_key {
                let q_class = self.classify_prop(iff_q);
                if let Ok((_, q_proof)) = self.build_prop_proof_inner(&q_class, iff_q, inner_depth)
                {
                    return Some(mk_iff_mpr(iff_p, iff_q, &Expr::bvar(0), &q_proof));
                }
            }
        }

        if let Some(proof) =
            self.try_eq_rewrite_under_assumption(assumption_type, goal_class, goal_expr, depth)
        {
            return Some(proof);
        }

        if depth < 3 {
            if let LogicalForm::Or(ref left, ref right) = assumption_class {
                let left_proof =
                    self.try_prove_under_assumption(left, goal_class, goal_expr, depth + 1);
                if let Some(left_body) = left_proof {
                    let right_proof =
                        self.try_prove_under_assumption(right, goal_class, goal_expr, depth + 1);
                    if let Some(right_body) = right_proof {
                        let f_inl = Expr::lam(BinderInfo::Default, left.clone(), left_body);
                        let f_inr = Expr::lam(BinderInfo::Default, right.clone(), right_body);
                        let motive = mk_constant_or_motive(left, right, goal_expr);
                        let assumption = Expr::bvar(0);
                        return Some(mk_or_rec(left, right, &motive, &f_inl, &f_inr, &assumption));
                    }
                }
            }
        }

        if assumption_key.is_some() {
            if let Some(proof) = self.try_assumption_absurd(assumption_type, goal_expr) {
                return Some(proof);
            }
            if let Some(proof) = self.try_assumption_modus_ponens(assumption_type, goal_expr) {
                return Some(proof);
            }
            if let Some(proof) = self.try_neg_assumption_absurd(assumption_type, goal_expr) {
                return Some(proof);
            }
            if let Some(proof) =
                self.try_negated_conjunction_hypothesis(assumption_type, goal_class)
            {
                return Some(proof);
            }
        }

        if depth < 3 {
            match goal_class {
                LogicalForm::And(ref p, ref q) => {
                    let p_class = self.classify_prop(p);
                    let q_class = self.classify_prop(q);
                    let left = self.try_prove_under_assumption_in_scope(
                        assumption_type,
                        &p_class,
                        p,
                        depth + 1,
                    );
                    let right = self.try_prove_under_assumption_in_scope(
                        assumption_type,
                        &q_class,
                        q,
                        depth + 1,
                    );
                    if let (Some(lp), Some(rp)) = (left, right) {
                        return Some(mk_and_intro(p, q, &lp, &rp));
                    }
                }
                LogicalForm::Or(ref p, ref q) => {
                    let p_class = self.classify_prop(p);
                    if let Some(lp) = self.try_prove_under_assumption_in_scope(
                        assumption_type,
                        &p_class,
                        p,
                        depth + 1,
                    ) {
                        return Some(mk_or_inl(p, q, &lp));
                    }
                    let q_class = self.classify_prop(q);
                    if let Some(rp) = self.try_prove_under_assumption_in_scope(
                        assumption_type,
                        &q_class,
                        q,
                        depth + 1,
                    ) {
                        return Some(mk_or_inr(p, q, &rp));
                    }
                }
                LogicalForm::Implies(ref p, ref q) => {
                    let q_class = self.classify_prop(q);
                    let nested_assumptions = vec![
                        LocalAssumption::introduced(p),
                        LocalAssumption::lifted(assumption_type, &Expr::bvar(0), 1),
                    ];
                    let body = self.with_lifted_bound_exists_witnesses(1, || {
                        self.try_prove_with_local_assumptions(
                            &nested_assumptions,
                            &q_class,
                            q,
                            depth + 1,
                        )
                    })?;
                    return Some(Expr::lam(BinderInfo::Default, p.clone(), body));
                }
                LogicalForm::Not(ref p) => {
                    let false_expr = mk_false_const();
                    let nested_assumptions = vec![
                        LocalAssumption::introduced(p),
                        LocalAssumption::lifted(assumption_type, &Expr::bvar(0), 1),
                    ];
                    let body = self.with_lifted_bound_exists_witnesses(1, || {
                        self.try_prove_with_local_assumptions(
                            &nested_assumptions,
                            &LogicalForm::False,
                            &false_expr,
                            depth + 1,
                        )
                    })?;
                    return Some(Expr::lam(BinderInfo::Default, p.clone(), body));
                }
                _ => {}
            }
        }

        None
    }
}
