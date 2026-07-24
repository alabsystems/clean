// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! LRA Farkas chain topology and transitivity-building logic.
//!
//! Extracted from `theory_lemma_lra` to keep file sizes manageable.
//! Handles finding directed paths through arithmetic bounds and building
//! iterated transitivity proofs (le_trans, lt_trans, etc.).

use ay_core::TermId;
use clean_kernel::Expr;

use super::expr_builders_arith::{self, CmpOp};
use super::theory_lemma_lra::ActiveBound;
use super::{ReconstructResult, ReconstructionContext, ReconstructionError};

/// Parsed arithmetic bound from a Farkas clause literal.
#[derive(Debug)]
pub(super) struct BoundInfo {
    pub(super) sort: ay::Sort,
    pub(super) op: CmpOp,
    pub(super) lhs_term: TermId,
    pub(super) rhs_term: TermId,
    pub(super) lhs_expr: Expr,
    pub(super) rhs_expr: Expr,
}

impl<'a> ReconstructionContext<'a> {
    fn unexpected_chain_sort_boundary(
        &self,
        step_index: u32,
        sort: &ay::Sort,
    ) -> ReconstructionError {
        ReconstructionError::trust_boundary(
            step_index,
            "LRA",
            format!("unexpected non-arithmetic sort {sort:?} in LRA chain"),
        )
    }

    /// Two-bound chain: check forward and reverse chaining.
    ///
    /// For cyclic chains (start == end), uses `lt_irrefl` to derive `False`
    /// without `trustedArith`. For concrete endpoints, uses the kernel-verified
    /// closers; otherwise reports a trust boundary.
    pub(super) fn try_two_bound_chain(
        &self,
        bounds: &[ActiveBound<'_>],
        clause_len: usize,
        step_index: u32,
    ) -> ReconstructResult<Option<Expr>> {
        let (b0, b1) = (bounds[0], bounds[1]);
        if b0.sort() != b1.sort() {
            return Ok(None);
        }
        let (h0, h1) = (b0.hypothesis(clause_len), b1.hypothesis(clause_len));

        if b0.rhs_term() == b1.lhs_term() {
            let result_op = expr_builders_arith::combine_ops(b0.op(), b1.op());
            let proof = expr_builders_arith::mk_chain_step_for_sort(
                b0.sort(),
                b0.lhs_expr(),
                b0.rhs_expr(),
                b1.rhs_expr(),
                b0.op(),
                b1.op(),
                &h0,
                &h1,
            )
            .ok_or_else(|| self.unexpected_chain_sort_boundary(step_index, b0.sort()))?;
            // Cycle detection: if chain returns to start, use lt_irrefl
            if b0.lhs_term() == b1.rhs_term() && result_op == CmpOp::Lt {
                if let Some(false_proof) =
                    expr_builders_arith::mk_lt_irrefl_false(b0.sort(), b0.lhs_expr(), &proof)
                {
                    return Ok(Some(false_proof));
                }
            }
            return self
                .close_chain_non_cyclic(
                    step_index,
                    b0.sort(),
                    result_op,
                    b0.lhs_term(),
                    b1.rhs_term(),
                    b0.lhs_expr(),
                    b1.rhs_expr(),
                    &proof,
                )
                .map(Some);
        }

        if b1.rhs_term() == b0.lhs_term() {
            let result_op = expr_builders_arith::combine_ops(b1.op(), b0.op());
            let proof = expr_builders_arith::mk_chain_step_for_sort(
                b0.sort(),
                b1.lhs_expr(),
                b1.rhs_expr(),
                b0.rhs_expr(),
                b1.op(),
                b0.op(),
                &h1,
                &h0,
            )
            .ok_or_else(|| self.unexpected_chain_sort_boundary(step_index, b0.sort()))?;
            // Cycle detection: if chain returns to start, use lt_irrefl
            if b1.lhs_term() == b0.rhs_term() && result_op == CmpOp::Lt {
                if let Some(false_proof) =
                    expr_builders_arith::mk_lt_irrefl_false(b0.sort(), b1.lhs_expr(), &proof)
                {
                    return Ok(Some(false_proof));
                }
            }
            return self
                .close_chain_non_cyclic(
                    step_index,
                    b0.sort(),
                    result_op,
                    b1.lhs_term(),
                    b0.rhs_term(),
                    b1.lhs_expr(),
                    b0.rhs_expr(),
                    &proof,
                )
                .map(Some);
        }

        Ok(None)
    }

    /// N-bound chain: find a directed path and build iterated transitivity.
    ///
    /// Handles both open chains (unique start node) and cyclic chains (all nodes
    /// appear as both LHS and RHS). For cyclic chains with at least one strict
    /// bound (`<`), uses `lt_irrefl` to derive `False` without `trustedArith`.
    pub(super) fn try_n_bound_chain(
        &self,
        bounds: &[ActiveBound<'_>],
        clause_len: usize,
        step_index: u32,
    ) -> ReconstructResult<Option<Expr>> {
        let n = bounds.len();
        if n < 2 {
            return Ok(None);
        }
        let sort = bounds[0].sort();
        if !bounds.iter().all(|b| b.sort() == sort) {
            return Ok(None);
        }

        let Some((chain, is_cycle)) = self.find_chain_order(bounds) else {
            return Ok(None);
        };
        self.build_chain_proof(bounds, sort, clause_len, &chain, is_cycle, step_index)
    }

    /// Find an ordered traversal through bounds, returning (chain_indices, is_cycle).
    fn find_chain_order(&self, bounds: &[ActiveBound<'_>]) -> Option<(Vec<usize>, bool)> {
        use std::collections::{HashMap, HashSet};

        let n = bounds.len();
        let mut forward: HashMap<TermId, Vec<(TermId, usize)>> = HashMap::new();
        let mut in_degree: HashMap<TermId, usize> = HashMap::new();
        let mut out_degree: HashMap<TermId, usize> = HashMap::new();
        let mut nodes = HashSet::new();
        for (i, b) in bounds.iter().enumerate() {
            forward
                .entry(b.lhs_term())
                .or_default()
                .push((b.rhs_term(), i));
            *out_degree.entry(b.lhs_term()).or_insert(0) += 1;
            *in_degree.entry(b.rhs_term()).or_insert(0) += 1;
            nodes.insert(b.lhs_term());
            nodes.insert(b.rhs_term());
        }
        for neighbors in forward.values_mut() {
            neighbors.reverse();
        }

        let mut start = None;
        let mut end = None;
        for node in nodes {
            let out = out_degree.get(&node).copied().unwrap_or(0);
            let in_ = in_degree.get(&node).copied().unwrap_or(0);
            if out == in_ + 1 {
                if start.replace(node).is_some() {
                    return None;
                }
            } else if in_ == out + 1 {
                if end.replace(node).is_some() {
                    return None;
                }
            } else if in_ != out {
                return None;
            }
        }

        let is_cycle = start.is_none() && end.is_none();
        if !is_cycle && (start.is_none() || end.is_none()) {
            return None;
        }
        let start = start.unwrap_or(bounds[0].lhs_term());

        let mut term_stack = vec![start];
        let mut edge_stack = Vec::with_capacity(n);
        let mut chain_rev = Vec::with_capacity(n);
        while let Some(&current) = term_stack.last() {
            if let Some((next_term, idx)) = forward
                .get_mut(&current)
                .and_then(|neighbors| neighbors.pop())
            {
                term_stack.push(next_term);
                edge_stack.push(idx);
            } else {
                term_stack.pop();
                if let Some(idx) = edge_stack.pop() {
                    chain_rev.push(idx);
                }
            }
        }
        if chain_rev.len() != n {
            return None;
        }
        chain_rev.reverse();
        Some((chain_rev, is_cycle))
    }

    /// Build a chain proof from ordered bound indices, closing with lt_irrefl or a trust boundary.
    fn build_chain_proof(
        &self,
        bounds: &[ActiveBound<'_>],
        sort: &ay::Sort,
        clause_len: usize,
        chain: &[usize],
        is_cycle: bool,
        step_index: u32,
    ) -> ReconstructResult<Option<Expr>> {
        let first_ci = chain[0];
        let mut proof = bounds[first_ci].hypothesis(clause_len);
        let start_expr = bounds[first_ci].lhs_expr();
        let mut current_rhs = bounds[first_ci].rhs_expr();
        let mut current_op = bounds[first_ci].op();

        for &ci in &chain[1..] {
            let h = bounds[ci].hypothesis(clause_len);
            let next_rhs = bounds[ci].rhs_expr();
            let next_op = bounds[ci].op();
            let result_op = expr_builders_arith::combine_ops(current_op, next_op);
            proof = expr_builders_arith::mk_chain_step_for_sort(
                sort,
                start_expr,
                current_rhs,
                next_rhs,
                current_op,
                next_op,
                &proof,
                &h,
            )
            .ok_or_else(|| self.unexpected_chain_sort_boundary(step_index, sort))?;
            current_rhs = next_rhs;
            current_op = result_op;
        }

        if is_cycle && current_op == CmpOp::Lt {
            if let Some(fp) = expr_builders_arith::mk_lt_irrefl_false(sort, start_expr, &proof) {
                return Ok(Some(fp));
            }
        }
        let last_ci = chain[chain.len() - 1];
        self.close_chain_non_cyclic(
            step_index,
            sort,
            current_op,
            bounds[first_ci].lhs_term(),
            bounds[last_ci].rhs_term(),
            start_expr,
            current_rhs,
            &proof,
        )
        .map(Some)
    }
}

#[cfg(test)]
mod tests;
