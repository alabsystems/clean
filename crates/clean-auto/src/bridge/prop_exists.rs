// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Existential witness reconstruction for propositional bridge proofs.
//!
//! This is a bounded sound slice for `#2442`: when the goal is `∃ x : α, P x`,
//! reconstruct `Exists.intro` only from witnesses that are already valid in the
//! goal context or are closed monomorphic constants from the environment. It
//! also reconstructs `Exists.elim` from tracked existential hypotheses when a
//! bounded continuation proof closes the current goal.

use crate::proof::ProofStep;
use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Expr, ExprKind, Level, TypeChecker};

use super::expr_classifier::LogicalForm;
use super::translate::ExprKey;
use super::{BridgeError, BridgeResult, SmtBridge};

/// Extract the head constant name from an expression (the outermost `Const`
/// after stripping all `App` wrappers). Used as a fast pre-filter for type
/// matching — types with different head constants cannot be definitionally equal
/// without reduction through a type alias.
fn expr_head_name(e: &Expr) -> Option<&Name> {
    match e.get_app_fn().kind() {
        ExprKind::Const(name, _) => Some(name),
        _ => None,
    }
}

fn expr_may_delta_reduce(expr: &Expr, bridge: &SmtBridge<'_>) -> bool {
    let mut stack = vec![expr];
    while let Some(current) = stack.pop() {
        match current.kind() {
            ExprKind::Const(name, _)
                if bridge
                    .env
                    .get_const(name)
                    .is_some_and(|info| info.reducibility.should_unfold(Default::default())) =>
            {
                return true;
            }
            ExprKind::App(fun, arg) => {
                stack.push(fun);
                stack.push(arg);
            }
            ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
                stack.push(ty);
                stack.push(body);
            }
            ExprKind::Let(_, ty, val, body, _) => {
                stack.push(ty);
                stack.push(val);
                stack.push(body);
            }
            ExprKind::Proj(_, _, inner) | ExprKind::MData(_, inner) | ExprKind::Squash(inner) => {
                stack.push(inner)
            }
            ExprKind::BVar(_) | ExprKind::FVar(_) | ExprKind::Sort(_) | ExprKind::Lit(_) => {}
            _ => {}
        }
    }
    false
}

struct BoundExistsWitnessRestore<'a, 'env> {
    bridge: &'a SmtBridge<'env>,
    saved: Vec<(Expr, Expr)>,
}

impl Drop for BoundExistsWitnessRestore<'_, '_> {
    fn drop(&mut self) {
        *self.bridge.bound_exists_witnesses.borrow_mut() = std::mem::take(&mut self.saved);
    }
}

impl<'env> SmtBridge<'env> {
    fn types_def_eq(&self, tc: &TypeChecker<'env>, lhs: &Expr, rhs: &Expr) -> bool {
        tc.is_def_eq(lhs, rhs) || tc.is_def_eq(rhs, lhs)
    }

    fn extract_exists_universe(exists_expr: &Expr) -> Option<Level> {
        match exists_expr.strip_mdata().get_app_fn().strip_mdata().kind() {
            ExprKind::Const(name, levels)
                if *name == Name::from_string("Exists") && levels.len() == 1 =>
            {
                Some(levels[0].clone())
            }
            _ => None,
        }
    }

    fn exists_universe(
        &self,
        exists_expr: Option<&Expr>,
        binder_type: &Expr,
    ) -> BridgeResult<Level> {
        if let Some(level) = exists_expr.and_then(Self::extract_exists_universe) {
            return Ok(level);
        }
        self.sort_level_of_type(binder_type)
    }

    pub(super) fn build_exists_proof(
        &self,
        goal_expr: &Expr,
        binder_type: &Expr,
        body: &Expr,
        depth: u32,
    ) -> BridgeResult<(ProofStep, Expr)> {
        let witness_candidates = self.goal_scoped_witness_candidates(binder_type);

        for witness in witness_candidates {
            let instantiated_body = body.instantiate(&witness);
            let instantiated_class = self.classify_prop(&instantiated_body);
            if let Ok((_, body_proof)) =
                self.build_prop_proof_inner(&instantiated_class, &instantiated_body, depth + 1)
            {
                let proof = self.mk_exists_intro_term(
                    Some(goal_expr),
                    binder_type,
                    body,
                    &witness,
                    &body_proof,
                )?;
                return Ok((ProofStep::Propositional("Exists.intro".into()), proof));
            }
        }

        Err(BridgeError::UnsupportedExpr {
            context: "propositional: no in-scope or closed witness proves Exists body".into(),
        })
    }

    pub(super) fn try_exists_elim(
        &self,
        goal_class: &LogicalForm,
        goal_expr: &Expr,
        depth: u32,
    ) -> BridgeResult<(ProofStep, Expr)> {
        for (fvar_id, hyp_type) in self.iter_guided_hypotheses() {
            if self.exists_elim_active.borrow().contains(&fvar_id) {
                continue;
            }

            let hyp_class = self.classify_prop(hyp_type);
            let LogicalForm::Exists { binder_type, body } = hyp_class else {
                continue;
            };

            self.exists_elim_active.borrow_mut().push(fvar_id);
            let continuation_body = self.try_exists_elim_continuation(
                &binder_type,
                &body,
                goal_class,
                goal_expr,
                depth,
            );
            self.exists_elim_active
                .borrow_mut()
                .retain(|&id| id != fvar_id);

            if let Some(continuation_body) = continuation_body {
                let proof = self.mk_exists_elim_term(
                    Some(hyp_type),
                    &binder_type,
                    &body,
                    goal_expr,
                    &Expr::fvar(fvar_id),
                    &continuation_body,
                )?;
                return Ok((ProofStep::Propositional("Exists.elim".into()), proof));
            }
        }

        Err(BridgeError::UnsupportedExpr {
            context: "exists_elim: no applicable existential hypothesis".into(),
        })
    }

    pub(super) fn goal_scoped_witness_candidates(&self, binder_type: &Expr) -> Vec<Expr> {
        let tc = self.make_tc();
        let mut candidates = Vec::new();

        for (candidate_type, witness) in self.bound_exists_witnesses.borrow().iter() {
            if self.witness_type_matches(&tc, candidate_type, binder_type) {
                candidates.push(witness.clone());
            }
        }

        if let Some(local_ctx) = &self.local_ctx {
            for decl in local_ctx.iter() {
                let expr = Expr::fvar(decl.id);
                if self.expr_matches_type(&tc, &expr, binder_type) {
                    candidates.push(expr);
                }
            }
        }

        for expr in self.term_to_expr.values() {
            let expr = expr.strip_mdata();
            if self.expr_is_goal_scoped(expr) && self.expr_matches_type(&tc, expr, binder_type) {
                candidates.push(expr.clone());
            }
        }

        // Pre-filter environment constants using structural matching to avoid
        // expensive is_def_eq on every monomorphic constant. For Mathlib-scale
        // environments (50k+ constants), this reduces from O(constants * is_def_eq)
        // to O(constants * ExprKey) + O(matches * is_def_eq).
        let binder_key = ExprKey::from_expr(binder_type);
        let binder_may_delta_reduce = expr_may_delta_reduce(binder_type, self);
        let binder_head = expr_head_name(binder_type);
        for constant in self.env.constants() {
            if !constant.level_params.is_empty() {
                continue;
            }
            let const_type = &constant.type_;
            let const_key = ExprKey::from_expr(const_type);
            let const_may_delta_reduce = expr_may_delta_reduce(const_type, self);
            match (&binder_key, &const_key) {
                // Both keys available and equal: structural match implies
                // definitional equality — include without expensive is_def_eq.
                (Some(bk), Some(ck)) if bk == ck => {
                    candidates.push(Expr::const_(constant.name.clone(), vec![]));
                }
                // Only skip structural mismatches when neither side contains
                // unfoldable definitions. Reducible aliases such as
                // `A_alias := A` must still fall back to is_def_eq.
                (Some(_), Some(_)) if !binder_may_delta_reduce && !const_may_delta_reduce => {
                    continue;
                }
                // ExprKey unavailable for one or both: fall back to head-name
                // comparison as a cheaper pre-filter before is_def_eq.
                _ => {
                    if let (Some(bh), Some(ch)) = (binder_head, expr_head_name(const_type)) {
                        if bh != ch && !binder_may_delta_reduce && !const_may_delta_reduce {
                            continue;
                        }
                    }
                    let expr = Expr::const_(constant.name.clone(), vec![]);
                    if self.types_def_eq(&tc, const_type, binder_type) {
                        candidates.push(expr);
                    }
                }
            }
        }

        let mut deduped = Vec::new();
        let mut seen = std::collections::HashSet::new();
        for candidate in candidates {
            if let Some(key) = ExprKey::from_expr(&candidate) {
                if seen.insert(key) {
                    deduped.push(candidate);
                }
            } else {
                // No structural key available (Sort, Let, Proj, extension
                // expressions) — include unconditionally rather than silently
                // dropping valid witness candidates.
                deduped.push(candidate);
            }
        }
        deduped
    }

    fn expr_matches_type(&self, tc: &TypeChecker<'env>, expr: &Expr, expected_type: &Expr) -> bool {
        tc.infer_type(expr)
            .map(|ty| self.types_def_eq(tc, &ty, expected_type))
            .unwrap_or(false)
    }

    pub(super) fn witness_type_matches(
        &self,
        tc: &TypeChecker<'env>,
        candidate_type: &Expr,
        expected_type: &Expr,
    ) -> bool {
        let candidate_key = ExprKey::from_expr(candidate_type);
        let expected_key = ExprKey::from_expr(expected_type);
        if candidate_key.is_some() && candidate_key == expected_key {
            return true;
        }

        if candidate_type.has_loose_bvars() || expected_type.has_loose_bvars() {
            return false;
        }

        self.types_def_eq(tc, candidate_type, expected_type)
    }

    pub(super) fn mk_exists_intro_term(
        &self,
        exists_expr: Option<&Expr>,
        binder_type: &Expr,
        body: &Expr,
        witness: &Expr,
        body_proof: &Expr,
    ) -> BridgeResult<Expr> {
        let universe = self.exists_universe(exists_expr, binder_type)?;
        let exists_intro = Expr::const_(Name::from_string("Exists.intro"), vec![universe]);
        let predicate = Expr::lam(BinderInfo::Default, binder_type.clone(), body.clone());
        Ok(Expr::app(
            Expr::app(
                Expr::app(Expr::app(exists_intro, binder_type.clone()), predicate),
                witness.clone(),
            ),
            body_proof.clone(),
        ))
    }

    pub(super) fn mk_exists_elim_term(
        &self,
        exists_expr: Option<&Expr>,
        binder_type: &Expr,
        body: &Expr,
        goal_expr: &Expr,
        hyp_proof: &Expr,
        continuation_body: &Expr,
    ) -> BridgeResult<Expr> {
        let universe = self.exists_universe(exists_expr, binder_type)?;
        let exists_elim = Expr::const_(Name::from_string("Exists.elim"), vec![universe]);
        let predicate = Expr::lam(BinderInfo::Default, binder_type.clone(), body.clone());
        let continuation = Expr::lam(
            BinderInfo::Default,
            binder_type.clone(),
            Expr::lam(BinderInfo::Default, body.clone(), continuation_body.clone()),
        );
        Ok(Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(Expr::app(exists_elim, binder_type.clone()), predicate),
                    goal_expr.clone(),
                ),
                hyp_proof.clone(),
            ),
            continuation,
        ))
    }

    fn try_exists_elim_continuation(
        &self,
        binder_type: &Expr,
        body: &Expr,
        _goal_class: &LogicalForm,
        goal_expr: &Expr,
        depth: u32,
    ) -> Option<Expr> {
        self.with_lifted_bound_exists_witnesses(2, || {
            // Lift binder_type by 2 to match the continuation lambda depth:
            // the continuation is `fun (x : binder_type) (h : body) => ...`,
            // so bvar(1) = x lives 2 binders deeper than the caller context.
            let lifted_binder_type = binder_type.lift(2);
            let lifted_goal_expr = goal_expr.lift(2);
            let lifted_goal_class = self.classify_prop(&lifted_goal_expr);
            self.with_bound_exists_witness(&lifted_binder_type, &Expr::bvar(1), || {
                let assumption_type = body.lift(1);
                if let Some(proof) = self.try_prove_under_assumption_in_scope(
                    &assumption_type,
                    &lifted_goal_class,
                    &lifted_goal_expr,
                    depth + 1,
                ) {
                    return Some(proof);
                }

                self.try_exists_goal_from_witness(
                    &lifted_goal_expr,
                    &lifted_binder_type,
                    &assumption_type,
                    &lifted_goal_class,
                    depth + 1,
                )
            })
        })
    }

    fn try_exists_goal_from_witness(
        &self,
        goal_expr: &Expr,
        witness_type: &Expr,
        assumption_type: &Expr,
        goal_class: &LogicalForm,
        depth: u32,
    ) -> Option<Expr> {
        let LogicalForm::Exists {
            binder_type: goal_binder_type,
            body: goal_body,
        } = goal_class
        else {
            return None;
        };

        let tc = self.make_tc();
        if !self.witness_type_matches(&tc, witness_type, goal_binder_type) {
            return None;
        }

        // `goal_class` here already lives in the continuation context
        // `(witness, assumption)`, so reusing the opened witness must
        // instantiate the existential binder with `bvar(1)` rather than just
        // shifting the body deeper.
        let instantiated_goal_body = goal_body.instantiate(&Expr::bvar(1));
        let instantiated_goal_class = self.classify_prop(&instantiated_goal_body);
        let body_proof = self.try_prove_under_assumption_in_scope(
            assumption_type,
            &instantiated_goal_class,
            &instantiated_goal_body,
            depth + 1,
        )?;

        self.mk_exists_intro_term(
            Some(goal_expr),
            goal_binder_type,
            goal_body,
            &Expr::bvar(1),
            &body_proof,
        )
        .ok()
    }

    pub(super) fn with_bound_exists_witness<T>(
        &self,
        witness_type: &Expr,
        witness: &Expr,
        f: impl FnOnce() -> T,
    ) -> T {
        let saved = self.bound_exists_witnesses.borrow().clone();
        let _restore = BoundExistsWitnessRestore {
            bridge: self,
            saved,
        };
        self.bound_exists_witnesses
            .borrow_mut()
            .push((witness_type.clone(), witness.clone()));
        f()
    }

    pub(super) fn with_lifted_bound_exists_witnesses<T>(
        &self,
        amount: u32,
        f: impl FnOnce() -> T,
    ) -> T {
        if amount == 0 || self.bound_exists_witnesses.borrow().is_empty() {
            return f();
        }

        let saved = self.bound_exists_witnesses.borrow().clone();
        let lifted = saved
            .iter()
            .map(|(ty, witness)| (ty.lift(amount), witness.lift(amount)))
            .collect();
        let _restore = BoundExistsWitnessRestore {
            bridge: self,
            saved,
        };
        *self.bound_exists_witnesses.borrow_mut() = lifted;
        f()
    }

    fn expr_is_goal_scoped(&self, expr: &Expr) -> bool {
        if expr.has_loose_bvars() {
            return false;
        }

        match expr.kind() {
            ExprKind::FVar(fvar_id) => self
                .local_ctx
                .as_ref()
                .is_some_and(|ctx| ctx.get(*fvar_id).is_some()),
            ExprKind::Const(_, _) | ExprKind::Lit(_) | ExprKind::Sort(_) => true,
            _ => !expr.has_fvar_quick(),
        }
    }
}
