// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Local-assumption proof search for nested propositional continuations.

use clean_kernel::{BinderInfo, Expr};

use super::disjunction::{mk_and_intro, mk_and_left, mk_and_right, mk_or_inl, mk_or_inr};
use super::prop_strategies::mk_false_const;
use super::translate::ExprKey;
use super::{LogicalForm, SmtBridge};

const MAX_LOCAL_ASSUMPTION_DEPTH: u32 = 8;
const MAX_INNER_SEARCH_DEPTH: u32 = 45;

#[derive(Clone)]
pub(super) struct LocalAssumption {
    ty: Expr,
    proof: Expr,
}

impl LocalAssumption {
    pub(super) fn introduced(ty: &Expr) -> Self {
        Self {
            ty: ty.lift(1),
            proof: Expr::bvar(0),
        }
    }

    pub(super) fn lifted(ty: &Expr, proof: &Expr, amount: u32) -> Self {
        Self {
            ty: ty.lift(amount),
            proof: proof.lift(amount),
        }
    }
}

impl<'env> SmtBridge<'env> {
    pub(super) fn goal_in_new_binder(&self, goal_expr: &Expr) -> (Expr, LogicalForm) {
        let lifted_goal_expr = goal_expr.lift(1);
        let lifted_goal_class = self.classify_prop(&lifted_goal_expr);
        (lifted_goal_expr, lifted_goal_class)
    }

    pub(super) fn try_prove_with_local_assumptions(
        &self,
        assumptions: &[LocalAssumption],
        goal_class: &LogicalForm,
        goal_expr: &Expr,
        depth: u32,
    ) -> Option<Expr> {
        if depth > MAX_LOCAL_ASSUMPTION_DEPTH {
            return None;
        }

        if let Some(proof) = self.try_local_assumption_match(assumptions, goal_expr) {
            return Some(proof);
        }

        let inner_depth = depth.saturating_add(1).max(MAX_INNER_SEARCH_DEPTH);
        if let Ok((_, proof)) = self.build_prop_proof_inner(goal_class, goal_expr, inner_depth) {
            return Some(proof);
        }

        for assumption in assumptions {
            if let Some(proof) = self.try_assumption_guided_equality_term(
                &assumption.ty,
                &assumption.proof,
                goal_class,
            ) {
                return Some(proof);
            }
        }

        for (assumption_idx, assumption) in assumptions.iter().enumerate() {
            let assumption_class = self.classify_prop(&assumption.ty);
            let LogicalForm::Exists { binder_type, body } = assumption_class else {
                continue;
            };

            if let Some(proof) = self.try_local_exists_elim(
                assumptions,
                assumption_idx,
                &binder_type,
                &body,
                &assumption.proof,
                goal_expr,
                depth,
            ) {
                return Some(proof);
            }
        }

        match goal_class {
            LogicalForm::And(left, right) => {
                let left_class = self.classify_prop(left);
                let right_class = self.classify_prop(right);
                let left_proof = self.try_prove_with_local_assumptions(
                    assumptions,
                    &left_class,
                    left,
                    depth + 1,
                )?;
                let right_proof = self.try_prove_with_local_assumptions(
                    assumptions,
                    &right_class,
                    right,
                    depth + 1,
                )?;
                Some(mk_and_intro(left, right, &left_proof, &right_proof))
            }
            LogicalForm::Or(left, right) => {
                let left_class = self.classify_prop(left);
                if let Some(left_proof) =
                    self.try_prove_with_local_assumptions(assumptions, &left_class, left, depth + 1)
                {
                    return Some(mk_or_inl(left, right, &left_proof));
                }

                let right_class = self.classify_prop(right);
                self.try_prove_with_local_assumptions(assumptions, &right_class, right, depth + 1)
                    .map(|right_proof| mk_or_inr(left, right, &right_proof))
            }
            LogicalForm::Implies(ante, cons) => {
                let cons_class = self.classify_prop(cons);
                let nested_assumptions = self.lift_local_assumptions(assumptions, 1, ante);
                let body = self.with_lifted_bound_exists_witnesses(1, || {
                    self.try_prove_with_local_assumptions(
                        &nested_assumptions,
                        &cons_class,
                        cons,
                        depth + 1,
                    )
                })?;
                Some(Expr::lam(BinderInfo::Default, ante.clone(), body))
            }
            LogicalForm::Not(inner) => {
                let nested_assumptions = self.lift_local_assumptions(assumptions, 1, inner);
                let false_expr = mk_false_const();
                let body = self.with_lifted_bound_exists_witnesses(1, || {
                    self.try_prove_with_local_assumptions(
                        &nested_assumptions,
                        &LogicalForm::False,
                        &false_expr,
                        depth + 1,
                    )
                })?;
                Some(Expr::lam(BinderInfo::Default, inner.clone(), body))
            }
            LogicalForm::Forall { binder_type, body } => {
                let body_class = self.classify_prop(body);
                let lifted_assumptions = assumptions
                    .iter()
                    .map(|assumption| LocalAssumption::lifted(&assumption.ty, &assumption.proof, 1))
                    .collect::<Vec<_>>();
                let body_proof = self.with_lifted_bound_exists_witnesses(1, || {
                    self.try_prove_with_local_assumptions(
                        &lifted_assumptions,
                        &body_class,
                        body,
                        depth + 1,
                    )
                })?;
                Some(Expr::lam(
                    BinderInfo::Default,
                    binder_type.clone(),
                    body_proof,
                ))
            }
            LogicalForm::Exists { binder_type, body } => {
                let tc = self.make_tc();
                let mut candidates = self.goal_scoped_witness_candidates(binder_type);
                for assumption in assumptions {
                    if self.witness_type_matches(&tc, &assumption.ty, binder_type) {
                        candidates.push(assumption.proof.clone());
                    }
                }

                let mut seen = std::collections::HashSet::new();
                for witness in candidates {
                    // Preserve unkeyable witnesses (Let/Proj/Sort) instead of
                    // silently dropping them from nested Exists search.
                    if let Some(key) = ExprKey::from_expr(&witness) {
                        if !seen.insert(key) {
                            continue;
                        }
                    }

                    let instantiated_body = body.instantiate(&witness);
                    let instantiated_class = self.classify_prop(&instantiated_body);
                    let body_proof = self.try_prove_with_local_assumptions(
                        assumptions,
                        &instantiated_class,
                        &instantiated_body,
                        depth + 1,
                    )?;
                    let proof = self
                        .mk_exists_intro_term(
                            Some(goal_expr),
                            binder_type,
                            body,
                            &witness,
                            &body_proof,
                        )
                        .ok()?;
                    return Some(proof);
                }
                None
            }
            _ => None,
        }
    }

    fn try_local_assumption_match(
        &self,
        assumptions: &[LocalAssumption],
        goal_expr: &Expr,
    ) -> Option<Expr> {
        let goal_key = ExprKey::from_expr(goal_expr);
        for assumption in assumptions {
            let assumption_key = ExprKey::from_expr(&assumption.ty);
            if goal_key.is_some() && goal_key == assumption_key {
                return Some(assumption.proof.clone());
            }

            let assumption_class = self.classify_prop(&assumption.ty);
            if let LogicalForm::And(left, right) = assumption_class {
                let left_key = ExprKey::from_expr(&left);
                if goal_key.is_some() && goal_key == left_key {
                    return Some(mk_and_left(&assumption.proof));
                }
                let right_key = ExprKey::from_expr(&right);
                if goal_key.is_some() && goal_key == right_key {
                    return Some(mk_and_right(&assumption.proof));
                }
            }
        }
        None
    }

    fn try_local_exists_elim(
        &self,
        assumptions: &[LocalAssumption],
        exists_idx: usize,
        binder_type: &Expr,
        body: &Expr,
        hyp_proof: &Expr,
        goal_expr: &Expr,
        depth: u32,
    ) -> Option<Expr> {
        self.with_lifted_bound_exists_witnesses(2, || {
            let lifted_binder_type = binder_type.lift(2);
            let lifted_goal_expr = goal_expr.lift(2);
            let lifted_goal_class = self.classify_prop(&lifted_goal_expr);
            self.with_bound_exists_witness(&lifted_binder_type, &Expr::bvar(1), || {
                let mut nested_assumptions = Vec::with_capacity(assumptions.len());
                nested_assumptions.push(LocalAssumption::introduced(body));
                nested_assumptions.extend(
                    assumptions
                        .iter()
                        .enumerate()
                        .filter(|(idx, _)| *idx != exists_idx)
                        .map(|(_, assumption)| {
                            LocalAssumption::lifted(&assumption.ty, &assumption.proof, 2)
                        }),
                );

                let continuation_body = self.try_prove_with_local_assumptions(
                    &nested_assumptions,
                    &lifted_goal_class,
                    &lifted_goal_expr,
                    depth + 1,
                )?;

                self.mk_exists_elim_term(
                    Some(&assumptions[exists_idx].ty),
                    binder_type,
                    body,
                    goal_expr,
                    hyp_proof,
                    &continuation_body,
                )
                .ok()
            })
        })
    }

    fn lift_local_assumptions(
        &self,
        assumptions: &[LocalAssumption],
        amount: u32,
        assumption_type: &Expr,
    ) -> Vec<LocalAssumption> {
        let mut nested = Vec::with_capacity(assumptions.len() + 1);
        nested.push(LocalAssumption::introduced(assumption_type));
        nested.extend(
            assumptions.iter().map(|assumption| {
                LocalAssumption::lifted(&assumption.ty, &assumption.proof, amount)
            }),
        );
        nested
    }
}
