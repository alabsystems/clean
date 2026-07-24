// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! LRA Farkas chain closeout helpers.

use ay_core::TermId;
use clean_kernel::name::Name;
use clean_kernel::Expr;

use super::expr_builders_arith::{self, CmpOp};
use super::theory_lemma_lra_chain_expr::{
    close_real_chain_by_expr, is_concrete_violation_by_kernel_expr,
};
use super::theory_lemma_lra_sum_nf;
use super::{ReconstructResult, ReconstructionContext, ReconstructionError};

impl<'a> ReconstructionContext<'a> {
    /// Extract a concrete integer value from a term, accepting both
    /// `Constant::Int` and integer-valued `Constant::Rational` (denom=1).
    pub(super) fn extract_concrete_int(&self, term: TermId) -> Option<&num_bigint::BigInt> {
        use super::trace::ConstantView;
        match self.trace().as_constant(term)? {
            ConstantView::Int(n) => Some(n),
            ConstantView::Rational(r) => {
                if r.0.denom() == &num_bigint::BigInt::from(1) {
                    Some(r.0.numer())
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    /// Check if chain endpoints are concrete numeric values and the bound is
    /// violated. Handles both `Constant::Int` and integer-valued
    /// `Constant::Rational` (common in Real-sort chains from ay's LRA theory).
    pub(super) fn is_concrete_violation(
        &self,
        start_term: TermId,
        end_term: TermId,
        op: CmpOp,
    ) -> bool {
        let start_val = match self.extract_concrete_int(start_term) {
            Some(v) => v,
            None => return false,
        };
        let end_val = match self.extract_concrete_int(end_term) {
            Some(v) => v,
            None => return false,
        };
        match op {
            CmpOp::Le => start_val > end_val,
            CmpOp::Lt => start_val >= end_val,
        }
    }

    /// Close a non-cyclic chain by proving `False` from `chain_proof : op(start, end)`.
    ///
    /// Tiers (highest priority first): Int concrete -> Real non-neg ->
    /// Real any-int -> Real Expr-level -> Int/Real NF closeout -> TrustBoundary.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn close_chain_non_cyclic(
        &self,
        step_index: u32,
        sort: &ay::Sort,
        op: CmpOp,
        start_term: TermId,
        end_term: TermId,
        start_expr: &Expr,
        end_expr: &Expr,
        chain_proof: &Expr,
    ) -> ReconstructResult<Expr> {
        // Int sort with concrete endpoints: kernel-verified via NonNeg.casesOn.
        // Try ay term-level check first; fall back to kernel Expr-level check
        // for cases where ay represents constants as named variables mapped to
        // concrete kernel expressions (e.g., mk_var("const5") -> Int.ofNat 5).
        if matches!(sort, ay::Sort::Int)
            && (self.is_concrete_violation(start_term, end_term, op)
                || is_concrete_violation_by_kernel_expr(start_expr, end_expr, op))
        {
            return Ok(expr_builders_arith::mk_int_concrete_false(
                op,
                start_expr,
                end_expr,
                chain_proof,
            ));
        }
        // Real sort with concrete non-negative endpoints: kernel-verified via
        // Nat.ble evaluation + Real.not_ofNat_le/lt bridge axioms.
        if matches!(sort, ay::Sort::Real) {
            if let Some((m, n)) = self.extract_concrete_nonneg_pair(start_term, end_term, op) {
                return Ok(expr_builders_arith::mk_real_concrete_false(
                    op,
                    m,
                    n,
                    chain_proof,
                ));
            }
        }
        // Real sort with any concrete integer endpoints (including negative):
        // kernel-verified via Real.not_ofInt_le/lt bridge axioms +
        // NonNeg.casesOn on the Int-level contradiction.
        if matches!(sort, ay::Sort::Real) {
            if let Some((a_int, b_int)) = self.extract_concrete_int_exprs(start_term, end_term, op)
            {
                return Ok(expr_builders_arith::mk_real_ofint_concrete_false(
                    op,
                    &a_int,
                    &b_int,
                    chain_proof,
                ));
            }
        }
        // Real sort Expr-level fallback: when ay represents concrete numbers as
        // named variables (e.g., mk_var("5") -> Real.ofNat 5), the ay term-level
        // extraction above returns None. Try extracting concrete values from the
        // kernel Expr patterns instead - the same 3-tier strategy the additive
        // path already uses. Part of #302.
        if matches!(sort, ay::Sort::Real) {
            if let Some(false_proof) =
                close_real_chain_by_expr(op, start_expr, end_expr, chain_proof)
            {
                return Ok(false_proof);
            }
        }
        // NF closeout for symbolic chain endpoints. Additive normal-form
        // cancellation exposes concrete contradictions in chains like
        // x+3 <= x+1 by cancelling shared addends. Int chains use the
        // accumulator directly; Real chains downcast to Int first. #2422.
        if let Some(false_proof) =
            try_chain_nf_closeout(sort, op, start_expr, end_expr, chain_proof)
        {
            return Ok(false_proof);
        }
        // Remaining intentional frontier after the concrete, Expr-level, and
        // additive-NF closeout tiers have all failed.
        Err(ReconstructionError::trust_boundary(
            step_index,
            "LRA",
            format!(
                "non-cyclic {op:?} chain over {sort:?} has no kernel closing proof for these endpoints"
            ),
        ))
    }

    /// Extract concrete non-negative Nat values from chain endpoints for Real sort.
    ///
    /// Returns `Some((start_nat, end_nat))` when both endpoints are non-negative
    /// integer-valued constants and the bound is violated (start > end for Le,
    /// start >= end for Lt).
    fn extract_concrete_nonneg_pair(
        &self,
        start_term: TermId,
        end_term: TermId,
        op: CmpOp,
    ) -> Option<(u64, u64)> {
        let start_val = self.extract_concrete_int(start_term)?;
        let end_val = self.extract_concrete_int(end_term)?;
        if start_val.sign() == num_bigint::Sign::Minus || end_val.sign() == num_bigint::Sign::Minus
        {
            return None;
        }
        let start_nat: u64 = start_val.try_into().ok()?;
        let end_nat: u64 = end_val.try_into().ok()?;
        match op {
            CmpOp::Le if start_nat > end_nat => Some((start_nat, end_nat)),
            CmpOp::Lt if start_nat >= end_nat => Some((start_nat, end_nat)),
            _ => None,
        }
    }

    /// Extract concrete Int expressions from chain endpoints for Real.ofInt closing.
    ///
    /// Returns `Some((a_int_expr, b_int_expr))` when both endpoints are concrete
    /// integer-valued constants (including negative) and the bound is violated.
    /// The returned expressions have type `Int` (for use with the bridge axioms).
    fn extract_concrete_int_exprs(
        &self,
        start_term: TermId,
        end_term: TermId,
        op: CmpOp,
    ) -> Option<(Expr, Expr)> {
        let start_val = self.extract_concrete_int(start_term)?;
        let end_val = self.extract_concrete_int(end_term)?;
        let violated = match op {
            CmpOp::Le => start_val > end_val,
            CmpOp::Lt => start_val >= end_val,
        };
        if !violated {
            return None;
        }
        let to_int_expr = |val: &num_bigint::BigInt| -> Option<Expr> {
            if val.sign() != num_bigint::Sign::Minus {
                let nat_val: u64 = val.try_into().ok()?;
                Some(Expr::app(
                    Expr::const_(Name::from_string("Int.ofNat"), vec![]),
                    Expr::nat_lit(nat_val),
                ))
            } else {
                let abs_minus_one: u64 = (-val - 1u64).try_into().ok()?;
                Some(Expr::app(
                    Expr::const_(Name::from_string("Int.negSucc"), vec![]),
                    Expr::nat_lit(abs_minus_one),
                ))
            }
        };
        Some((to_int_expr(start_val)?, to_int_expr(end_val)?))
    }
}

/// NF closeout for symbolic arithmetic chain endpoints.
///
/// Int: flattens `Int.add` trees and cancels shared atoms directly.
/// Real: downcasts to `Real.ofInt(Int.add(...))` then applies Int NF.
fn try_chain_nf_closeout(
    sort: &ay::Sort,
    op: CmpOp,
    lhs: &Expr,
    rhs: &Expr,
    proof: &Expr,
) -> Option<Expr> {
    match sort {
        ay::Sort::Int => theory_lemma_lra_sum_nf::try_close_int_additive_nf(op, lhs, rhs, proof),
        ay::Sort::Real => {
            let (a, b, h) =
                super::expr_builders_real_downcast::downcast_real_hyp_to_int(op, lhs, rhs, proof)?;
            theory_lemma_lra_sum_nf::try_close_int_additive_nf(op, &a, &b, &h)
        }
        _ => None,
    }
}
