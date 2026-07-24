// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use ay_core::{ProofId, TermId};
use clean_kernel::{Expr, FVarId};

use super::{ReconstructResult, ReconstructionContext, ReconstructionError};

impl<'a> ReconstructionContext<'a> {
    /// Reconstruct an Assume step.
    ///
    /// An assumption in the ay proof corresponds to either:
    /// 1. A hypothesis from the tactic context (FVar proof)
    /// 2. The negated goal assertion
    /// 3. A compound input assertion (gets a fresh proof-witness FVar)
    pub(super) fn reconstruct_assume(
        &mut self,
        term_id: TermId,
        _step_id: ProofId,
        negated_goal: &Expr,
    ) -> ReconstructResult<Expr> {
        let assumed_prop = self.translate_term(term_id)?;

        let var_name: Option<String> = self
            .trace
            .as_ref()
            .and_then(|t| t.as_var_name(term_id).map(|s| s.to_string()));
        if let Some(name) = &var_name {
            if let Some((_fvar_id, proof_expr, _prop_ty)) = self.var_map.get_hypothesis(name) {
                return Ok(proof_expr.clone());
            }
        }

        if let Some((_fvar_id, proof_expr, _prop_ty)) =
            self.var_map.find_hypothesis_by_prop(&assumed_prop)
        {
            return Ok(proof_expr.clone());
        }

        if assumed_prop == *negated_goal {
            let (_, proof_expr) = self.negated_goal_proof.get_or_insert_with(|| {
                let fvar_id = FVarId::new(u64::MAX);
                debug_assert!(fvar_id.is_sentinel());
                (fvar_id, Expr::fvar(fvar_id))
            });
            return Ok(proof_expr.clone());
        }

        self.allocate_compound_witness(assumed_prop)
    }

    fn allocate_compound_witness(&mut self, assumed_prop: Expr) -> ReconstructResult<Expr> {
        let witness_idx = self.compound_witness_count;
        self.compound_witness_count += 1;
        let witness_id = FVarId::new(u64::MAX - 1 - u64::from(witness_idx));
        if !witness_id.is_sentinel() {
            return Err(ReconstructionError::SentinelRangeExhausted {
                witness_count: witness_idx,
            });
        }
        self.compound_witnesses.push((witness_id, assumed_prop));
        Ok(Expr::fvar(witness_id))
    }
}
