// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use std::collections::HashSet;

use crate::proof::ProofStep;
use crate::smt::TermId;
use clean_kernel::Expr;

use super::super::arith_chain::{mk_nat_ground_le, mk_nat_ground_lt, ArithSort, CmpOp};
use super::super::{BridgeResult, LogicalForm, SmtBridge};

#[derive(Clone)]
pub(super) struct ArithmeticHypothesisEdge {
    pub(super) lhs: TermId,
    pub(super) rhs: TermId,
    pub(super) rhs_expr: Expr,
    pub(super) op: CmpOp,
    pub(super) proof_step: ProofStep,
    pub(super) proof_term: Expr,
}

impl<'env> SmtBridge<'env> {
    pub(super) fn guided_arithmetic_terms(&self) -> BridgeResult<HashSet<TermId>> {
        let mut result = HashSet::new();
        for (_, hyp_expr) in self.iter_guided_hypotheses() {
            self.collect_guided_arithmetic_terms_from_expr(hyp_expr, &mut result)?;
        }
        Ok(result)
    }

    fn collect_guided_arithmetic_terms_from_expr(
        &self,
        hyp_expr: &Expr,
        terms: &mut HashSet<TermId>,
    ) -> BridgeResult<()> {
        match self.classify_prop(hyp_expr) {
            LogicalForm::Le { lhs, rhs, .. }
            | LogicalForm::Lt { lhs, rhs, .. }
            | LogicalForm::Ge { lhs, rhs, .. }
            | LogicalForm::Gt { lhs, rhs, .. } => {
                terms.insert(self.lookup_existing_arithmetic_term(&lhs)?);
                terms.insert(self.lookup_existing_arithmetic_term(&rhs)?);
            }
            LogicalForm::And(left, right) => {
                self.collect_guided_arithmetic_terms_from_expr(&left, terms)?;
                self.collect_guided_arithmetic_terms_from_expr(&right, terms)?;
            }
            _ => {}
        }
        Ok(())
    }

    pub(super) fn collect_guided_arithmetic_hypothesis_edges(
        &self,
        goal_sort: ArithSort,
    ) -> BridgeResult<Vec<ArithmeticHypothesisEdge>> {
        let mut edges = Vec::new();
        for (fvar, hyp_expr) in self.iter_guided_hypotheses() {
            self.collect_arithmetic_hypothesis_edges_from_expr(
                hyp_expr,
                Expr::fvar(fvar),
                ProofStep::hypothesis(fvar),
                goal_sort,
                &mut edges,
            )?;
        }
        self.collect_ground_arithmetic_edges(goal_sort, &mut edges);
        Ok(edges)
    }

    fn collect_ground_arithmetic_edges(
        &self,
        goal_sort: ArithSort,
        edges: &mut Vec<ArithmeticHypothesisEdge>,
    ) {
        if goal_sort != ArithSort::Nat {
            return;
        }

        let terms: Vec<(TermId, Expr)> = self
            .term_to_expr
            .iter()
            .filter(|(term, _)| self.arithmetic_sort_for_term(**term) == Some(goal_sort))
            .map(|(term, expr)| (*term, expr.clone()))
            .collect();

        let mut seen = HashSet::new();
        for (lhs_term, lhs_expr) in &terms {
            for (rhs_term, rhs_expr) in &terms {
                if lhs_term == rhs_term {
                    continue;
                }

                if let Some(proof_term) = mk_nat_ground_le(lhs_expr, rhs_expr) {
                    if seen.insert((*lhs_term, *rhs_term, CmpOp::Le)) {
                        edges.push(ArithmeticHypothesisEdge {
                            lhs: *lhs_term,
                            rhs: *rhs_term,
                            rhs_expr: rhs_expr.clone(),
                            op: CmpOp::Le,
                            proof_step: ProofStep::Propositional("arith.nat_ground_le".into()),
                            proof_term,
                        });
                    }
                }

                if let Some(proof_term) = mk_nat_ground_lt(lhs_expr, rhs_expr) {
                    if seen.insert((*lhs_term, *rhs_term, CmpOp::Lt)) {
                        edges.push(ArithmeticHypothesisEdge {
                            lhs: *lhs_term,
                            rhs: *rhs_term,
                            rhs_expr: rhs_expr.clone(),
                            op: CmpOp::Lt,
                            proof_step: ProofStep::Propositional("arith.nat_ground_lt".into()),
                            proof_term,
                        });
                    }
                }
            }
        }
    }
}
