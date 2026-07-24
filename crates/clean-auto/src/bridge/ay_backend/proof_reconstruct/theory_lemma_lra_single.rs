// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Single-bound contradiction helpers for LRA Farkas reconstruction.

use clean_kernel::Expr;

use super::expr_builders_arith::{self, CmpOp};
use super::theory_lemma_lra::ActiveBound;
use super::{ReconstructResult, ReconstructionContext, ReconstructionError};

impl<'a> ReconstructionContext<'a> {
    pub(super) fn try_any_single_bound_contradiction(
        &self,
        bounds: &[ActiveBound<'_>],
        clause_len: usize,
        step_index: u32,
    ) -> ReconstructResult<Option<Expr>> {
        for &bound in bounds {
            let proof = bound.hypothesis(clause_len);
            if bound.lhs_term() == bound.rhs_term() && bound.op() == CmpOp::Lt {
                if let Some(false_proof) =
                    expr_builders_arith::mk_lt_irrefl_false(bound.sort(), bound.lhs_expr(), &proof)
                {
                    return Ok(Some(false_proof));
                }
            }
            match self.close_chain_non_cyclic(
                step_index,
                bound.sort(),
                bound.op(),
                bound.lhs_term(),
                bound.rhs_term(),
                bound.lhs_expr(),
                bound.rhs_expr(),
                &proof,
            ) {
                Ok(false_proof) => return Ok(Some(false_proof)),
                Err(ReconstructionError::TrustBoundary { .. }) => {}
                Err(err) => return Err(err),
            }
        }
        Ok(None)
    }
}
