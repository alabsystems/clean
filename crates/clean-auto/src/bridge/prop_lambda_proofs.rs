// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Lambda-based proof builders for Implies and Not goals (#2442 Phase 2B).
//!
//! Extracted from `prop_reconstruction.rs` for file size compliance.
//! These methods construct `fun (x : T) => body` proof terms.

use crate::proof::ProofStep;
use clean_kernel::{BinderInfo, Expr};

use super::disjunction::{mk_absurd, mk_false_elim};
use super::expr_classifier::LogicalForm;
use super::prop_local_assumptions::LocalAssumption;
use super::prop_strategies::mk_false_const;
use super::translate::ExprKey;
use super::{BridgeError, BridgeResult, SmtBridge};

impl<'env> SmtBridge<'env> {
    /// Build a proof for `P → Q` (#2442 Phase 2B).
    ///
    /// Strategies (in order):
    /// 1. Q provable from existing hypotheses → `fun (_ : P) => q_proof`
    /// 2. P structurally equals Q → `fun (hp : P) => hp` (identity, bvar 0)
    /// 3. Modus ponens with lambda param: `h : P → Q'` where `Q' = Q`
    ///    → `fun (hp : P) => h hp` (bvar 0)
    /// 4. Equality-only: combine the lambda param with guided hypotheses to
    ///    build a native equality chain (for example `fun hp : a=b ∧ b=c => Eq.trans hp.1 hp.2`)
    /// 5. Build False from lambda param + ¬P hypothesis, then False.elim to get Q
    /// 6. Q provable with lambda param as a local assumption via recursive search
    pub(super) fn build_implies_proof(
        &self,
        p: &Expr,
        q: &Expr,
        depth: u32,
    ) -> BridgeResult<(ProofStep, Expr)> {
        // Strategy 1: Q provable from existing hypotheses (lambda ignores param)
        let q_class = self.classify_prop(q);
        if let Ok((_, q_proof)) = self.build_prop_proof_inner(&q_class, q, depth + 1) {
            let proof = Expr::lam(BinderInfo::Default, p.clone(), q_proof);
            return Ok((ProofStep::Propositional("Implies.lam".into()), proof));
        }

        // Strategy 2: P = Q (identity function)
        let p_key = ExprKey::from_expr(p);
        let q_key = ExprKey::from_expr(q);
        if p_key.is_some() && p_key == q_key {
            let proof = Expr::lam(BinderInfo::Default, p.clone(), Expr::bvar(0));
            return Ok((ProofStep::Propositional("Implies.id".into()), proof));
        }

        // Strategy 3: Modus ponens using lambda parameter.
        // If h : P → Q' exists where Q' matches Q, build fun (hp : P) => h hp
        // where hp is bvar(0) inside the lambda body.
        if let Some(proof) = self.try_implies_modus_ponens_with_bvar(p, q) {
            return Ok((ProofStep::Propositional("Implies.mp_bvar".into()), proof));
        }

        // Strategy 4: If Q is an equality, allow the lambda parameter to
        // contribute equality evidence alongside the guided hypotheses.
        let hp = Expr::bvar(0);
        if let Some(body) = self.try_assumption_guided_equality_term(p, &hp, &q_class) {
            let proof = Expr::lam(BinderInfo::Default, p.clone(), body);
            return Ok((
                ProofStep::Propositional("Implies.assumption_eq".into()),
                proof,
            ));
        }

        // Strategy 5: Build False from lambda param + ¬P hypothesis, then
        // use False.elim to get Q. Builds: fun (hp : P) => False.elim Q (absurd hp h_neg)
        if let Some(proof) = self.try_implies_via_absurd(p, q) {
            return Ok((
                ProofStep::Propositional("Implies.absurd_elim".into()),
                proof,
            ));
        }

        // Strategy 6: recursively search with the lambda parameter available as
        // a local assumption, so compound consequents can use both the new
        // assumption and any outer continuation witnesses.
        let local_assumptions = [LocalAssumption::introduced(p)];
        let body = self.with_lifted_bound_exists_witnesses(1, || {
            self.try_prove_with_local_assumptions(&local_assumptions, &q_class, q, depth + 1)
        });
        if let Some(body) = body {
            let proof = Expr::lam(BinderInfo::Default, p.clone(), body);
            return Ok((
                ProofStep::Propositional("Implies.assumption_search".into()),
                proof,
            ));
        }

        Err(BridgeError::UnsupportedExpr {
            context:
                "propositional: Implies(P, Q) — Q not provable from hypotheses or lambda param"
                    .into(),
        })
    }

    /// Build a proof for `¬P` (= `P → False`) (#2442 Phase 2B).
    ///
    /// Strategies (in order):
    /// 1. False is directly available as hypothesis → `fun (_ : P) => h_false`
    /// 2. ¬P hypothesis exists matching P → `fun (hp : P) => absurd hp h_neg`
    ///    Uses bvar(0) for the lambda parameter in the absurd proof.
    /// 3. Derive False from lambda param via existing contradiction pair
    pub(super) fn build_not_proof(&self, p: &Expr, depth: u32) -> BridgeResult<(ProofStep, Expr)> {
        // Strategy 1: False hypothesis available
        if let Some((fvar_id, _)) = self.find_hypothesis_by_form(&LogicalForm::False) {
            let false_proof = Expr::fvar(fvar_id);
            let proof = Expr::lam(BinderInfo::Default, p.clone(), false_proof);
            return Ok((ProofStep::Propositional("Not.lam_false".into()), proof));
        }

        // Strategy 2: h_neg : ¬P in hypotheses, use absurd with lambda param.
        // Build: fun (hp : P) => absurd hp h_neg
        // In the lambda body, hp is bvar(0). h_neg is fvar (unaffected by lambda).
        let p_key = ExprKey::from_expr(p);
        if p_key.is_some() {
            for (neg_fvar, neg_type) in self.iter_guided_hypotheses() {
                let neg_class = self.classify_prop(neg_type);
                if let LogicalForm::Not(ref inner) = neg_class {
                    let inner_key = ExprKey::from_expr(inner);
                    if p_key == inner_key {
                        // Build: fun (hp : P) => absurd hp h_neg : False
                        // absurd : {a : Prop} → {b : Prop} → a → ¬a → b
                        // Here a = P, b = False (since ¬P = P → False, the target is False)
                        let hp = Expr::bvar(0);
                        let h_neg = Expr::fvar(neg_fvar);
                        let false_expr = mk_false_const();
                        let body = mk_absurd(p, &false_expr, &hp, &h_neg);
                        let proof = Expr::lam(BinderInfo::Default, p.clone(), body);
                        return Ok((ProofStep::Propositional("Not.lam_absurd".into()), proof));
                    }
                }
            }
        }

        // Strategy 3: temporarily assume P and try to derive False from the
        // assumption shape plus the existing guided hypotheses.
        let false_expr = mk_false_const();
        if let Some(body) =
            self.try_prove_under_assumption(p, &LogicalForm::False, &false_expr, depth + 1)
        {
            let proof = Expr::lam(BinderInfo::Default, p.clone(), body);
            return Ok((ProofStep::Propositional("Not.assumption".into()), proof));
        }

        Err(BridgeError::UnsupportedExpr {
            context: "propositional: Not(P) requires False or ¬P hypothesis".into(),
        })
    }

    /// Try modus ponens using the lambda parameter (bvar 0).
    ///
    /// For goal `P → Q`, searches for hypothesis `h : P → Q'` where `Q'` matches Q.
    /// Builds: `fun (hp : P) => h hp` where hp = bvar(0).
    fn try_implies_modus_ponens_with_bvar(&self, p: &Expr, q: &Expr) -> Option<Expr> {
        let p_key = ExprKey::from_expr(p);
        let q_key = ExprKey::from_expr(q);
        if p_key.is_none() || q_key.is_none() {
            return None;
        }
        for (fvar_id, hyp_type) in self.iter_guided_hypotheses() {
            let hyp_class = self.classify_prop(hyp_type);
            if let LogicalForm::Implies(ref ante, ref cons) = hyp_class {
                let ante_key = ExprKey::from_expr(ante);
                let cons_key = ExprKey::from_expr(cons);
                if ante_key == p_key && cons_key == q_key {
                    // h : P → Q, hp : P ⊢ h hp : Q
                    let hp = Expr::bvar(0);
                    let h = Expr::fvar(fvar_id);
                    let body = Expr::app(h, hp);
                    return Some(Expr::lam(BinderInfo::Default, p.clone(), body));
                }
            }
        }
        None
    }

    /// Try proving `P → Q` via absurd: if ¬P exists, derive False from hp + ¬P,
    /// then False.elim to get Q.
    ///
    /// Builds: `fun (hp : P) => False.elim Q (absurd hp h_neg)`
    fn try_implies_via_absurd(&self, p: &Expr, q: &Expr) -> Option<Expr> {
        let p_key = ExprKey::from_expr(p);
        p_key.as_ref()?;
        for (neg_fvar, neg_type) in self.iter_guided_hypotheses() {
            let neg_class = self.classify_prop(neg_type);
            if let LogicalForm::Not(ref inner) = neg_class {
                let inner_key = ExprKey::from_expr(inner);
                if p_key == inner_key {
                    let hp = Expr::bvar(0);
                    let h_neg = Expr::fvar(neg_fvar);
                    let false_expr = mk_false_const();
                    let false_proof = mk_absurd(p, &false_expr, &hp, &h_neg);
                    let body = mk_false_elim(q, &false_proof);
                    return Some(Expr::lam(BinderInfo::Default, p.clone(), body));
                }
            }
        }
        None
    }
}
