// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Concrete additive closeout helpers for LRA Farkas reconstruction.

use clean_kernel::Expr;

use super::expr_builders_arith::{self, CmpOp};
use super::theory_lemma_lra::ActiveBound;
use super::theory_lemma_lra_additive::{
    mk_add_cmp_add_left, mk_add_cmp_add_right, mk_chain_step, mk_sort_add,
};
use super::{ReconstructResult, ReconstructionContext};

impl<'a> ReconstructionContext<'a> {
    /// Try to build an N-bound additive combination proof.
    ///
    /// Requires: N>=2 bounds, all Le/Lt, same sort (Int/Real), concrete integer
    /// endpoints on at least 2 bounds with violated additive sum. When some
    /// bounds have symbolic endpoints, the concrete-only subset is tried.
    pub(super) fn try_additive_le(
        &self,
        bounds: &[ActiveBound<'_>],
        clause_len: usize,
        step_index: u32,
    ) -> ReconstructResult<Option<Expr>> {
        if bounds.len() < 2 {
            return Ok(None);
        }

        // All bounds must be Le or Lt, same sort (Int or Real)
        let sort = bounds[0].sort();
        if !matches!(sort, ay::Sort::Int | ay::Sort::Real) {
            return Ok(None);
        }
        for b in bounds {
            if b.sort() != sort {
                return Ok(None);
            }
            if !matches!(b.op(), CmpOp::Le | CmpOp::Lt) {
                return Ok(None);
            }
        }

        // Extract concrete Int values for all endpoints.
        // Try ay term-level first, then Int-level Expr, then Real-level Expr.
        let concrete: Vec<_> = bounds
            .iter()
            .map(|b| {
                let lhs_val = self
                    .extract_concrete_int(b.lhs_term())
                    .cloned()
                    .or_else(|| expr_builders_arith::extract_concrete_int_from_expr(b.lhs_expr()))
                    .or_else(|| {
                        super::expr_builders_real_downcast::extract_concrete_int_from_real_expr(
                            b.lhs_expr(),
                        )
                    });
                let rhs_val = self
                    .extract_concrete_int(b.rhs_term())
                    .cloned()
                    .or_else(|| expr_builders_arith::extract_concrete_int_from_expr(b.rhs_expr()))
                    .or_else(|| {
                        super::expr_builders_real_downcast::extract_concrete_int_from_real_expr(
                            b.rhs_expr(),
                        )
                    });
                lhs_val.zip(rhs_val)
            })
            .collect();

        // When some bounds have symbolic endpoints, fall back to the concrete-
        // only subset. The EM case split binds all hypotheses at the base case
        // depth, so unused symbolic hypotheses remain harmlessly in scope.
        let effective_bounds: Vec<ActiveBound<'_>>;
        let effective_concrete: Vec<(num_bigint::BigInt, num_bigint::BigInt)>;
        if concrete.iter().all(|c| c.is_some()) {
            effective_bounds = bounds.to_vec();
            effective_concrete = concrete
                .into_iter()
                .map(|c| c.expect("invariant: all concrete after all-Some check"))
                .collect();
        } else {
            let pairs: Vec<_> = bounds
                .iter()
                .zip(concrete.iter())
                .filter_map(|(&b, c)| c.as_ref().map(|cv| (b, cv.clone())))
                .collect();
            if pairs.len() < 2 {
                return Ok(None);
            }
            effective_bounds = pairs.iter().map(|(b, _)| *b).collect();
            effective_concrete = pairs.into_iter().map(|(_, c)| c).collect();
        }

        // Track the combined op: any Lt makes the result Lt
        let combined_op = effective_bounds.iter().fold(CmpOp::Le, |acc, b| {
            expr_builders_arith::combine_ops(acc, b.op())
        });

        // Check if the summed bound is violated
        let mut sum_lhs = effective_concrete[0].0.clone();
        let mut sum_rhs = effective_concrete[0].1.clone();
        for c in &effective_concrete[1..] {
            sum_lhs = &sum_lhs + &c.0;
            sum_rhs = &sum_rhs + &c.1;
        }
        let violated = match combined_op {
            CmpOp::Le => sum_lhs > sum_rhs,
            CmpOp::Lt => sum_lhs >= sum_rhs,
        };
        if !violated {
            return Ok(None);
        }

        // Sort-dispatched builder closures
        let mk_add = |a: &Expr, b: &Expr| -> Expr {
            mk_sort_add(sort, a, b).expect("invariant: sort is Int or Real")
        };
        let mk_acl = |op: CmpOp, a: &Expr, b: &Expr, h: &Expr, c: &Expr| -> Expr {
            mk_add_cmp_add_left(sort, op, a, b, h, c).expect("invariant: sort is Int or Real")
        };
        let mk_acr = |op: CmpOp, a: &Expr, b: &Expr, h: &Expr, c: &Expr| -> Expr {
            mk_add_cmp_add_right(sort, op, a, b, h, c).expect("invariant: sort is Int or Real")
        };
        let mk_cs =
            |lo: CmpOp, ro: CmpOp, a: &Expr, b: &Expr, c: &Expr, h1: &Expr, h2: &Expr| -> Expr {
                mk_chain_step(sort, lo, ro, a, b, c, h1, h2)
                    .expect("invariant: sort is Int or Real")
            };

        // Hypothesis bvars use the original clause position, not the active-bound
        // position, because zero-coefficient literals are still part of the EM
        // case split even though the contradiction builder ignores them.

        // Base case: combine first two bounds
        let eb = &effective_bounds;
        let (a, b_rhs) = (eb[0].lhs_expr(), eb[0].rhs_expr());
        let (c, d) = (eb[1].lhs_expr(), eb[1].rhs_expr());
        let h0 = eb[0].hypothesis(clause_len);
        let h1 = eb[1].hypothesis(clause_len);

        let step1 = mk_acl(eb[0].op(), a, b_rhs, &h0, c);
        let step2 = mk_acr(eb[1].op(), c, d, &h1, b_rhs);

        let mut acc_lhs = mk_add(c, a);
        let mut acc_rhs = mk_add(d, b_rhs);
        let sum_mid = mk_add(c, b_rhs);
        let mut acc_op = expr_builders_arith::combine_ops(eb[0].op(), eb[1].op());

        let mut acc_proof = mk_cs(
            eb[0].op(),
            eb[1].op(),
            &acc_lhs,
            &sum_mid,
            &acc_rhs,
            &step1,
            &step2,
        );

        // Iterative accumulation for bounds 2..n
        for bound in eb.iter().skip(2) {
            let (ai, bi) = (bound.lhs_expr(), bound.rhs_expr());
            let hi = bound.hypothesis(clause_len);

            let step_a = mk_acr(acc_op, &acc_lhs, &acc_rhs, &acc_proof, ai);
            let step_b = mk_acl(bound.op(), ai, bi, &hi, &acc_rhs);

            let new_lhs = mk_add(&acc_lhs, ai);
            let mid = mk_add(&acc_rhs, ai);
            let new_rhs = mk_add(&acc_rhs, bi);

            acc_proof = mk_cs(
                acc_op,
                bound.op(),
                &new_lhs,
                &mid,
                &new_rhs,
                &step_a,
                &step_b,
            );
            acc_op = expr_builders_arith::combine_ops(acc_op, bound.op());
            acc_lhs = new_lhs;
            acc_rhs = new_rhs;
        }

        // Sort-dispatched closing step
        let false_proof = match sort {
            ay::Sort::Int => expr_builders_arith::mk_int_concrete_false(
                combined_op,
                &acc_lhs,
                &acc_rhs,
                &acc_proof,
            ),
            ay::Sort::Real => {
                return Ok(
                    super::expr_builders_real_downcast::close_real_additive_via_int_downcast(
                        &effective_bounds,
                        combined_op,
                        clause_len,
                    ),
                );
            }
            _ => return Ok(None),
        };

        let _ = step_index;
        Ok(Some(false_proof))
    }
}
