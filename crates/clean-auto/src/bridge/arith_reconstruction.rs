// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Arithmetic proof reconstruction from stored proof-trail payloads (#2442).

#[path = "arith_reconstruction_edges.rs"]
mod edges;

use std::collections::{HashMap, HashSet};

use super::arith_chain::{
    combine_ops, detect_sort, mk_chain_step, mk_le_antisymm, mk_le_of_lt, mk_le_refl,
    mk_lt_irrefl_false, mk_nat_ground_le, mk_nat_ground_lt, ArithSort, CmpOp,
};
use super::chain_search::bfs_chain_search_from_starts;
use super::disjunction::{mk_and_left, mk_and_right};
use super::{BridgeError, BridgeResult, LogicalForm, SmtBridge};
use crate::proof::ProofStep;
use crate::smt::{ProofTrailEntry, TermId, TheoryLiteral};
use clean_kernel::Expr;
use edges::ArithmeticHypothesisEdge;

impl<'env> SmtBridge<'env> {
    pub(super) fn build_direct_arithmetic_goal_proof(
        &self,
        goal_class: &LogicalForm,
    ) -> BridgeResult<(ProofStep, Expr)> {
        match goal_class {
            LogicalForm::Le { ty, lhs, rhs } => {
                self.build_direct_arithmetic_comparison_proof(ty, lhs, rhs, CmpOp::Le)
            }
            LogicalForm::Lt { ty, lhs, rhs } => {
                self.build_direct_arithmetic_comparison_proof(ty, lhs, rhs, CmpOp::Lt)
            }
            // GE.ge a b unfolds to LE.le b a, GT.gt a b unfolds to LT.lt b a.
            // Swapped Le/Lt proof terms still type-check because Ge/Gt are definitional abbreviations in Lean 4.
            LogicalForm::Ge { ty, lhs, rhs } => {
                self.build_direct_arithmetic_comparison_proof(ty, rhs, lhs, CmpOp::Le)
            }
            LogicalForm::Gt { ty, lhs, rhs } => {
                self.build_direct_arithmetic_comparison_proof(ty, rhs, lhs, CmpOp::Lt)
            }
            _ => Err(BridgeError::UnsupportedExpr {
                context: "direct arithmetic reconstruction only handles comparison goals".into(),
            }),
        }
    }

    pub(super) fn build_arithmetic_goal_proof(
        &self,
        goal_class: &LogicalForm,
        _goal_expr: &Expr,
    ) -> BridgeResult<(ProofStep, Expr)> {
        match goal_class {
            LogicalForm::Le { ty, lhs, rhs } => {
                self.build_arithmetic_comparison_proof(ty, lhs, rhs, CmpOp::Le)
            }
            LogicalForm::Lt { ty, lhs, rhs } => {
                self.build_arithmetic_comparison_proof(ty, lhs, rhs, CmpOp::Lt)
            }
            // GE/GT are definitional abbreviations: GE.ge a b = LE.le b a, GT.gt a b = LT.lt b a. Swap and delegate.
            LogicalForm::Ge { ty, lhs, rhs } => {
                self.build_arithmetic_comparison_proof(ty, rhs, lhs, CmpOp::Le)
            }
            LogicalForm::Gt { ty, lhs, rhs } => {
                self.build_arithmetic_comparison_proof(ty, rhs, lhs, CmpOp::Lt)
            }
            LogicalForm::False => self.build_arithmetic_false_proof(),
            _ => Err(BridgeError::UnsupportedExpr {
                context: "arithmetic reconstruction only handles comparison goals".into(),
            }),
        }
    }

    fn build_direct_arithmetic_comparison_proof(
        &self,
        ty: &Expr,
        lhs: &Expr,
        rhs: &Expr,
        goal_op: CmpOp,
    ) -> BridgeResult<(ProofStep, Expr)> {
        let sort = detect_sort(ty).ok_or_else(|| BridgeError::UnsupportedExpr {
            context: format!("arithmetic comparison sort not supported: {ty:?}"),
        })?;

        if sort == ArithSort::Nat {
            let ground_proof = match goal_op {
                CmpOp::Le => mk_nat_ground_le(lhs, rhs),
                CmpOp::Lt => mk_nat_ground_lt(lhs, rhs),
            };
            if let Some(proof_term) = ground_proof {
                let proof_step = match goal_op {
                    CmpOp::Le => "arith.nat_ground_le",
                    CmpOp::Lt => "arith.nat_ground_lt",
                };
                return Ok((ProofStep::Propositional(proof_step.into()), proof_term));
            }
        }

        if goal_op == CmpOp::Le && lhs == rhs {
            return Ok((
                ProofStep::Propositional("arith.le_refl".into()),
                mk_le_refl(sort, lhs),
            ));
        }

        Err(BridgeError::ProofTraceFailed(
            "direct arithmetic reconstruction requires a ground Nat comparison or reflexive <= goal"
                .into(),
        ))
    }

    pub(super) fn build_arithmetic_equality_proof(
        &self,
        eq_ty: &Expr,
        lhs: &Expr,
        rhs: &Expr,
    ) -> BridgeResult<(ProofStep, Expr)> {
        let sort = detect_sort(eq_ty).ok_or_else(|| BridgeError::UnsupportedExpr {
            context: format!("arithmetic equality sort not supported: {eq_ty:?}"),
        })?;
        let lhs_term = self.lookup_existing_arithmetic_term(lhs)?;
        let rhs_term = self.lookup_existing_arithmetic_term(rhs)?;
        let edges = self.collect_guided_arithmetic_hypothesis_edges(sort)?;

        let Some((_, hab)) =
            self.build_arithmetic_chain(lhs_term, rhs_term, lhs, sort, CmpOp::Le, &edges)
        else {
            return Err(BridgeError::ProofTraceFailed(format!(
                "missing arithmetic <= chain from {lhs:?} to {rhs:?}"
            )));
        };
        let Some((_, hba)) =
            self.build_arithmetic_chain(rhs_term, lhs_term, rhs, sort, CmpOp::Le, &edges)
        else {
            return Err(BridgeError::ProofTraceFailed(format!(
                "missing arithmetic <= chain from {rhs:?} to {lhs:?}"
            )));
        };

        Ok((
            ProofStep::Propositional("arith.le_antisymm".into()),
            mk_le_antisymm(sort, lhs, rhs, &hab, &hba),
        ))
    }

    fn build_arithmetic_comparison_proof(
        &self,
        ty: &Expr,
        lhs: &Expr,
        rhs: &Expr,
        goal_op: CmpOp,
    ) -> BridgeResult<(ProofStep, Expr)> {
        let sort = detect_sort(ty).ok_or_else(|| BridgeError::UnsupportedExpr {
            context: format!("arithmetic comparison sort not supported: {ty:?}"),
        })?;
        let lhs_term = self.lookup_existing_arithmetic_term(lhs)?;
        let rhs_term = self.lookup_existing_arithmetic_term(rhs)?;

        if let Ok(proof) = self.build_direct_arithmetic_comparison_proof(ty, lhs, rhs, goal_op) {
            return Ok(proof);
        }

        let edges = self.collect_guided_arithmetic_hypothesis_edges(sort)?;
        self.build_arithmetic_chain(lhs_term, rhs_term, lhs, sort, goal_op, &edges)
            .ok_or_else(|| {
                BridgeError::ProofTraceFailed(format!("no arithmetic chain for {lhs:?}"))
            })
    }

    fn build_arithmetic_false_proof(&self) -> BridgeResult<(ProofStep, Expr)> {
        let mut arithmetic_terms = self.trail_arithmetic_terms();
        arithmetic_terms.extend(self.guided_arithmetic_terms()?);
        for term in arithmetic_terms {
            let Some(sort) = self.arithmetic_sort_for_term(term) else {
                continue;
            };
            let Some(start_expr) = self.term_to_expr.get(&term) else {
                continue;
            };
            let edges = self.collect_guided_arithmetic_hypothesis_edges(sort)?;
            if let Some((_, cycle_proof)) =
                self.build_arithmetic_chain(term, term, start_expr, sort, CmpOp::Lt, &edges)
            {
                return Ok((
                    ProofStep::Propositional("arith.lt_irrefl_false".into()),
                    mk_lt_irrefl_false(sort, start_expr, &cycle_proof),
                ));
            }
        }

        Err(BridgeError::ProofTraceFailed(
            "no arithmetic strict cycle available for False goal".into(),
        ))
    }

    fn collect_arithmetic_hypothesis_edges_from_expr(
        &self,
        hyp_expr: &Expr,
        proof_term: Expr,
        proof_step: ProofStep,
        goal_sort: ArithSort,
        edges: &mut Vec<ArithmeticHypothesisEdge>,
    ) -> BridgeResult<()> {
        match self.classify_prop(hyp_expr) {
            LogicalForm::Le { ty, lhs, rhs } if detect_sort(&ty) == Some(goal_sort) => {
                let lhs_term = self.lookup_existing_arithmetic_term(&lhs)?;
                let rhs_term = self.lookup_existing_arithmetic_term(&rhs)?;
                edges.push(ArithmeticHypothesisEdge {
                    lhs: lhs_term,
                    rhs: rhs_term,
                    rhs_expr: rhs,
                    op: CmpOp::Le,
                    proof_step,
                    proof_term,
                });
            }
            LogicalForm::Lt { ty, lhs, rhs } if detect_sort(&ty) == Some(goal_sort) => {
                let lhs_term = self.lookup_existing_arithmetic_term(&lhs)?;
                let rhs_term = self.lookup_existing_arithmetic_term(&rhs)?;
                edges.push(ArithmeticHypothesisEdge {
                    lhs: lhs_term,
                    rhs: rhs_term,
                    rhs_expr: rhs,
                    op: CmpOp::Lt,
                    proof_step,
                    proof_term,
                });
            }
            LogicalForm::Ge { ty, lhs, rhs } if detect_sort(&ty) == Some(goal_sort) => {
                let lhs_term = self.lookup_existing_arithmetic_term(&rhs)?;
                let rhs_term = self.lookup_existing_arithmetic_term(&lhs)?;
                edges.push(ArithmeticHypothesisEdge {
                    lhs: lhs_term,
                    rhs: rhs_term,
                    rhs_expr: lhs,
                    op: CmpOp::Le,
                    proof_step,
                    proof_term,
                });
            }
            LogicalForm::Gt { ty, lhs, rhs } if detect_sort(&ty) == Some(goal_sort) => {
                let lhs_term = self.lookup_existing_arithmetic_term(&rhs)?;
                let rhs_term = self.lookup_existing_arithmetic_term(&lhs)?;
                edges.push(ArithmeticHypothesisEdge {
                    lhs: lhs_term,
                    rhs: rhs_term,
                    rhs_expr: lhs,
                    op: CmpOp::Lt,
                    proof_step,
                    proof_term,
                });
            }
            LogicalForm::And(left, right) => {
                crate::bridge::stack_safe(|| {
                    self.collect_arithmetic_hypothesis_edges_from_expr(
                        &left,
                        mk_and_left(&proof_term),
                        proof_step.clone(),
                        goal_sort,
                        edges,
                    )?;
                    self.collect_arithmetic_hypothesis_edges_from_expr(
                        &right,
                        mk_and_right(&proof_term),
                        proof_step,
                        goal_sort,
                        edges,
                    )?;
                    Ok(())
                })?;
            }
            _ => {}
        }
        Ok(())
    }

    fn build_arithmetic_chain(
        &self,
        start: TermId,
        target: TermId,
        start_expr: &Expr,
        sort: ArithSort,
        goal_op: CmpOp,
        edges: &[ArithmeticHypothesisEdge],
    ) -> Option<(ProofStep, Expr)> {
        if edges.is_empty() {
            return None;
        }

        // Pre-build adjacency map: lhs → [(edge_index, rhs, op)].
        // Makes neighbor lookup O(degree) instead of O(|edges|) per BFS node.
        let mut adj: HashMap<TermId, Vec<(usize, TermId, CmpOp)>> = HashMap::new();
        for (idx, edge) in edges.iter().enumerate() {
            adj.entry(edge.lhs)
                .or_default()
                .push((idx, edge.rhs, edge.op));
        }

        type BfsKey = (TermId, CmpOp);
        let mut state_adjacency: HashMap<BfsKey, Vec<(BfsKey, usize)>> = HashMap::new();
        for (&lhs, neighbors) in &adj {
            for current_op in [CmpOp::Le, CmpOp::Lt] {
                let edges_for_state = state_adjacency.entry((lhs, current_op)).or_default();
                for &(idx, rhs, op) in neighbors {
                    edges_for_state.push(((rhs, combine_ops(current_op, op)), idx));
                }
            }
        }

        let starts = adj
            .get(&start)
            .into_iter()
            .flat_map(|neighbors| neighbors.iter().map(|&(idx, rhs, op)| ((rhs, op), idx)))
            .collect::<Vec<_>>();

        bfs_chain_search_from_starts(
            std::iter::empty::<BfsKey>(),
            starts,
            &state_adjacency,
            |(node, _)| *node == target,
            |path| self.build_arithmetic_path_proof(start_expr, sort, goal_op, path, edges),
        )
    }

    fn build_arithmetic_path_proof(
        &self,
        start_expr: &Expr,
        sort: ArithSort,
        goal_op: CmpOp,
        path: &[usize],
        edges: &[ArithmeticHypothesisEdge],
    ) -> Option<(ProofStep, Expr)> {
        let first = edges.get(*path.first()?)?;
        if path.len() == 1 {
            return Self::finalize_arithmetic_path_proof(
                sort,
                goal_op,
                first.op,
                start_expr,
                &first.rhs_expr,
                first.proof_step.clone(),
                first.proof_term.clone(),
            );
        }

        let mut current_step = first.proof_step.clone();
        let mut current_term = first.proof_term.clone();
        let mut chain_current = first.rhs;
        let mut chain_op = first.op;

        for edge_idx in &path[1..] {
            let edge = edges.get(*edge_idx)?;
            let mid_expr = self.term_to_expr.get(&chain_current)?;
            current_term = mk_chain_step(
                sort,
                start_expr,
                mid_expr,
                &edge.rhs_expr,
                chain_op,
                edge.op,
                &current_term,
                &edge.proof_term,
            );
            current_step = ProofStep::trans(current_step, edge.proof_step.clone());
            chain_current = edge.rhs;
            chain_op = combine_ops(chain_op, edge.op);
        }

        let target_expr = self.term_to_expr.get(&chain_current)?;
        Self::finalize_arithmetic_path_proof(
            sort,
            goal_op,
            chain_op,
            start_expr,
            target_expr,
            current_step,
            current_term,
        )
    }

    fn finalize_arithmetic_path_proof(
        sort: ArithSort,
        goal_op: CmpOp,
        chain_op: CmpOp,
        lhs_expr: &Expr,
        rhs_expr: &Expr,
        proof_step: ProofStep,
        proof_term: Expr,
    ) -> Option<(ProofStep, Expr)> {
        match (goal_op, chain_op) {
            (goal, chain) if goal == chain => Some((proof_step, proof_term)),
            (CmpOp::Le, CmpOp::Lt) => mk_le_of_lt(sort, lhs_expr, rhs_expr, &proof_term)
                .map(|weakened| (ProofStep::Propositional("arith.le_of_lt".into()), weakened)),
            _ => None,
        }
    }

    fn lookup_existing_arithmetic_term(&self, expr: &Expr) -> BridgeResult<TermId> {
        let Some(key) = self.expr_to_key(expr.strip_mdata()) else {
            return Err(BridgeError::TranslationFailed {
                context: format!("missing arithmetic expr key for {expr:?}"),
            });
        };
        self.expr_to_term
            .get(&key)
            .copied()
            .ok_or_else(|| BridgeError::TranslationFailed {
                context: format!(
                    "arithmetic reconstruction term was not registered before proof search: {expr:?}"
                ),
            })
    }

    fn arithmetic_sort_for_term(&self, term: TermId) -> Option<ArithSort> {
        self.term_to_type.get(&term).and_then(detect_sort)
    }

    fn trail_arithmetic_terms(&self) -> HashSet<TermId> {
        let mut result = HashSet::new();
        let mut record_lit = |lit: &TheoryLiteral| match lit {
            TheoryLiteral::Lt(lhs, rhs) | TheoryLiteral::Le(lhs, rhs) => {
                result.insert(*lhs);
                result.insert(*rhs);
            }
            TheoryLiteral::Eq(_, _)
            | TheoryLiteral::Neq(_, _)
            | TheoryLiteral::Bool(_)
            | TheoryLiteral::NegBool(_) => {}
        };

        for entry in self.proof_trail() {
            match entry {
                ProofTrailEntry::TheoryConflict {
                    conflict_theory_lits,
                    ..
                } => {
                    for lit in conflict_theory_lits {
                        record_lit(lit);
                    }
                }
                ProofTrailEntry::TheoryPropagation {
                    implied_theory_lit,
                    explanation_theory_lits,
                    ..
                } => {
                    if let Some(lit) = implied_theory_lit {
                        record_lit(lit);
                    }
                    for lit in explanation_theory_lits {
                        record_lit(lit);
                    }
                }
            }
        }

        result
    }
}
