// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Trail-guided equality reconstruction from tracked hypotheses.

use crate::proof::ProofStep;
use crate::smt::TermId;
use clean_kernel::Expr;

use super::chain_search::bfs_chain_search;
use super::disjunction::{mk_and_left, mk_and_right};
use super::{BridgeError, BridgeResult, LogicalForm, SmtBridge};

#[derive(Clone)]
struct EqualityHypothesisEdge {
    lhs: TermId,
    rhs: TermId,
    proof_step: ProofStep,
    proof_term: Expr,
}

impl<'env> SmtBridge<'env> {
    pub(super) fn try_guided_hypothesis_equality_proof(
        &self,
        t1: TermId,
        t2: TermId,
        lhs_expr: &Expr,
        rhs_expr: &Expr,
        eq_ty: &Expr,
    ) -> BridgeResult<Option<(ProofStep, Expr)>> {
        let edges = self.collect_guided_equality_hypothesis_edges()?;
        self.try_guided_equality_proof_from_edges(t1, t2, lhs_expr, rhs_expr, eq_ty, &edges)
    }

    pub(super) fn try_assumption_guided_equality_term(
        &self,
        assumption_type: &Expr,
        assumption_proof: &Expr,
        goal_class: &LogicalForm,
    ) -> Option<Expr> {
        let LogicalForm::Eq { ty, lhs, rhs } = goal_class else {
            return None;
        };

        let t1 = self.lookup_existing_term(lhs).ok()?;
        let t2 = self.lookup_existing_term(rhs).ok()?;
        let mut edges = self.collect_guided_equality_hypothesis_edges().ok()?;
        self.collect_equality_hypothesis_edges_from_expr(
            assumption_type,
            assumption_proof.clone(),
            ProofStep::Propositional("assumption".into()),
            &mut edges,
        )
        .ok()?;
        self.try_guided_equality_proof_from_edges(t1, t2, lhs, rhs, ty, &edges)
            .ok()?
            .map(|(_, proof_term)| proof_term)
    }

    fn try_guided_equality_proof_from_edges(
        &self,
        t1: TermId,
        t2: TermId,
        lhs_expr: &Expr,
        rhs_expr: &Expr,
        eq_ty: &Expr,
        edges: &[EqualityHypothesisEdge],
    ) -> BridgeResult<Option<(ProofStep, Expr)>> {
        if edges.is_empty() {
            return Ok(None);
        }

        if let Some(edge) = edges.iter().find(|edge| edge.lhs == t1 && edge.rhs == t2) {
            return Ok(Some((edge.proof_step.clone(), edge.proof_term.clone())));
        }
        if let Some(edge) = edges.iter().find(|edge| edge.lhs == t2 && edge.rhs == t1) {
            let proof_step = ProofStep::symm(edge.proof_step.clone());
            let proof_term = self.mk_eq_symm(eq_ty, rhs_expr, lhs_expr, &edge.proof_term)?;
            return Ok(Some((proof_step, proof_term)));
        }

        let mut adjacency: std::collections::HashMap<TermId, Vec<(TermId, (usize, bool))>> =
            std::collections::HashMap::new();
        for (idx, edge) in edges.iter().enumerate() {
            adjacency
                .entry(edge.lhs)
                .or_default()
                .push((edge.rhs, (idx, false)));
            adjacency
                .entry(edge.rhs)
                .or_default()
                .push((edge.lhs, (idx, true)));
        }

        Ok(bfs_chain_search(t1, t2, &adjacency, |path| {
            self.build_guided_path_proof(t1, path, edges, eq_ty)
        }))
    }

    fn collect_guided_equality_hypothesis_edges(
        &self,
    ) -> BridgeResult<Vec<EqualityHypothesisEdge>> {
        let mut edges = Vec::new();
        for (fvar, hyp_expr) in self.iter_guided_hypotheses() {
            self.collect_equality_hypothesis_edges_from_expr(
                hyp_expr,
                Expr::fvar(fvar),
                ProofStep::hypothesis(fvar),
                &mut edges,
            )?;
        }
        Ok(edges)
    }

    fn collect_equality_hypothesis_edges_from_expr(
        &self,
        hyp_expr: &Expr,
        proof_term: Expr,
        proof_step: ProofStep,
        edges: &mut Vec<EqualityHypothesisEdge>,
    ) -> BridgeResult<()> {
        match self.classify_prop(hyp_expr) {
            LogicalForm::Eq { lhs, rhs, .. } => {
                let lhs_term = self.lookup_existing_term(&lhs)?;
                let rhs_term = self.lookup_existing_term(&rhs)?;
                edges.push(EqualityHypothesisEdge {
                    lhs: lhs_term,
                    rhs: rhs_term,
                    proof_step,
                    proof_term,
                });
            }
            LogicalForm::And(left, right) => {
                crate::bridge::stack_safe(|| {
                    self.collect_equality_hypothesis_edges_from_expr(
                        &left,
                        mk_and_left(&proof_term),
                        proof_step.clone(),
                        edges,
                    )?;
                    self.collect_equality_hypothesis_edges_from_expr(
                        &right,
                        mk_and_right(&proof_term),
                        proof_step,
                        edges,
                    )?;
                    Ok(())
                })?;
            }
            _ => {}
        }
        Ok(())
    }

    fn lookup_existing_term(&self, expr: &Expr) -> BridgeResult<TermId> {
        let Some(key) = self.expr_to_key(expr.strip_mdata()) else {
            return Err(BridgeError::TranslationFailed {
                context: format!("missing expr key for guided equality hypothesis {expr:?}"),
            });
        };
        self.expr_to_term
            .get(&key)
            .copied()
            .ok_or_else(|| BridgeError::TranslationFailed {
                context: format!(
                    "guided equality hypothesis term was not registered before reconstruction: {expr:?}"
                ),
            })
    }

    fn guided_edge_proof(
        &self,
        edge: &EqualityHypothesisEdge,
        needs_symm: bool,
        eq_ty: &Expr,
    ) -> Option<(ProofStep, Expr, TermId)> {
        if needs_symm {
            let lhs_expr = self.term_to_expr.get(&edge.lhs)?;
            let rhs_expr = self.term_to_expr.get(&edge.rhs)?;
            Some((
                ProofStep::symm(edge.proof_step.clone()),
                self.mk_eq_symm(eq_ty, lhs_expr, rhs_expr, &edge.proof_term)
                    .ok()?,
                edge.lhs,
            ))
        } else {
            Some((edge.proof_step.clone(), edge.proof_term.clone(), edge.rhs))
        }
    }

    fn build_guided_path_proof(
        &self,
        start: TermId,
        path: &[(usize, bool)],
        edges: &[EqualityHypothesisEdge],
        eq_ty: &Expr,
    ) -> Option<(ProofStep, Expr)> {
        let &(edge_idx, needs_symm) = path.first()?;
        let edge = edges.get(edge_idx)?;
        let (mut current_step, mut current_term, mut chain_current) =
            self.guided_edge_proof(edge, needs_symm, eq_ty)?;
        let chain_start_expr = self.term_to_expr.get(&start).cloned()?;

        for &(edge_idx, needs_symm) in &path[1..] {
            let edge = edges.get(edge_idx)?;
            let (next_step, next_term, next_dest) =
                self.guided_edge_proof(edge, needs_symm, eq_ty)?;
            let b_expr = self.term_to_expr.get(&chain_current).cloned()?;
            let c_expr = self.term_to_expr.get(&next_dest).cloned()?;

            current_step = ProofStep::trans(current_step, next_step);
            current_term = self
                .mk_eq_trans(
                    eq_ty,
                    &chain_start_expr,
                    &b_expr,
                    &c_expr,
                    &current_term,
                    &next_term,
                )
                .ok()?;
            chain_current = next_dest;
        }

        Some((current_step, current_term))
    }
}
