// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! LRA Farkas theory lemma reconstruction.
//!
//! Reconstructs LRA (Linear Real/Integer Arithmetic) theory lemmas using
//! Classical.em case splits on each negated bound, with Farkas combination
//! proofs for the arithmetic base case.
//!
//! # Proof Structure
//!
//! Clause: `[¬l₁, ¬l₂, ..., ¬lₙ]` where each `lᵢ` is an arithmetic bound
//! (e.g., `x ≤ 3`, `5 ≤ x`). The Farkas certificate `[λ₁, ..., λₙ]` proves
//! that the conjunction of all `lᵢ` is infeasible.
//!
//! The proof uses nested `Classical.em` case splits:
//! - If any bound doesn't hold: inject its negation into the clause
//! - If ALL bounds hold: derive `False` via Farkas combination, then `False.elim`
//!
//! # Supported Arithmetic Proofs
//!
//! - **N-bound transitivity chain**: builds an iterated chain using `le_trans`,
//!   `lt_trans`, etc. Closes via `lt_irrefl`, `NonNeg.casesOn`, or Real axioms.
//! - **N-bound additive combination**: sums concrete Int bounds using
//!   `add_le_add_left/right`, closes via `NonNeg.casesOn`. Zero-coefficient
//!   bounds are filtered out. Weighted variant scales by Farkas coefficients.
//! - **Fallback**: `Err(TrustBoundary)` when no chain, additive, or weighted proof closes the Farkas bounds.
use ay_core::{ProofId, TermId};
use clean_kernel::name::Name;
use clean_kernel::{Expr, Level};

use self::partition::connected_bound_components;
use super::em_combinator::EmSplitItem;
use super::expr_builders_arith::{self, CmpOp};
use super::farkas_certificate::FarkasCertificate;
use super::theory_lemma_lra_additive::{combine_scaled_bounds, SortCmpAcc};
use super::theory_lemma_lra_chain::BoundInfo;
use super::theory_lemma_lra_sum_nf;
use super::theory_lemma_lra_weighted::build_weighted_additive_accumulator;
use super::{ReconstructResult, ReconstructionContext, ReconstructionError};

mod partition;

/// Active Farkas bound together with its original clause position.
#[derive(Clone, Copy, Debug)]
pub(super) struct ActiveBound<'a> {
    pub(super) clause_idx: usize,
    pub(super) bound: &'a BoundInfo,
}

impl<'a> ActiveBound<'a> {
    pub(super) fn hypothesis(self, clause_len: usize) -> Expr {
        Expr::bvar((clause_len - 1 - self.clause_idx) as u32)
    }

    pub(super) fn sort(self) -> &'a ay::Sort {
        &self.bound.sort
    }

    pub(super) fn op(self) -> CmpOp {
        self.bound.op
    }

    pub(super) fn lhs_term(self) -> TermId {
        self.bound.lhs_term
    }

    pub(super) fn rhs_term(self) -> TermId {
        self.bound.rhs_term
    }

    pub(super) fn lhs_expr(self) -> &'a Expr {
        &self.bound.lhs_expr
    }

    pub(super) fn rhs_expr(self) -> &'a Expr {
        &self.bound.rhs_expr
    }
}

impl<'a> ReconstructionContext<'a> {
    /// Reconstruct an LRA Farkas theory lemma.
    ///
    /// The `cert` parameter is a pre-validated `FarkasCertificate` that owns
    /// active clause indices and exact coefficients. Clause-length and validity
    /// checks were done at certificate construction time.
    pub(super) fn reconstruct_lra_farkas(
        &self,
        clause: &[TermId],
        cert: &FarkasCertificate,
        props: &[Expr],
        target: &Expr,
        step_id: ProofId,
    ) -> ReconstructResult<Expr> {
        let trace = self.trace();
        for (i, &lit) in clause.iter().enumerate() {
            if trace.as_not(lit).is_none() {
                return Err(ReconstructionError::UnsupportedStep {
                    step_index: step_id.0,
                    description: format!("Farkas clause literal {} is not negated", i),
                });
            }
        }

        let bounds = self.parse_farkas_bounds(clause);
        let active_bounds: Vec<ActiveBound<'_>> = cert
            .active_indices()
            .iter()
            .map(|&clause_idx| {
                bounds.get(clause_idx).and_then(|bound| {
                    bound
                        .as_ref()
                        .map(|bound| ActiveBound { clause_idx, bound })
                })
            })
            .collect::<Option<_>>()
            .ok_or_else(|| ReconstructionError::UnsupportedStep {
                step_index: step_id.0,
                description: "Farkas clause contains a non-arithmetic active literal".to_string(),
            })?;
        let items: Vec<EmSplitItem> = (0..clause.len())
            .map(|i| EmSplitItem { clause_idx: i })
            .collect();
        self.build_em_case_split(clause, props, target, &items, step_id, 0, &|_depth| {
            if let Some(false_proof) =
                self.try_farkas_combination(clause.len(), &active_bounds, cert, step_id)?
            {
                return Ok(mk_false_elim(target, &false_proof));
            }
            Err(ReconstructionError::trust_boundary(
                step_id.0,
                "LRA",
                "non-chainable Farkas fallback: no transitivity chain, additive combination, or weighted proof found for active bounds",
            ))
        })
    }

    fn parse_farkas_bounds(&self, clause: &[TermId]) -> Vec<Option<BoundInfo>> {
        let trace = self.trace();
        clause
            .iter()
            .map(|&lit| {
                let inner = trace.as_not(lit)?;
                self.parse_bound(inner)
            })
            .collect()
    }

    fn parse_bound(&self, term_id: TermId) -> Option<BoundInfo> {
        let trace = self.trace();
        let (name, args) = trace.as_named_app(term_id)?;
        if args.len() != 2 {
            return None;
        }
        // Normalize >=|> to <=|< with swapped arguments.
        // ay's decompose_arithmetic_eq/decompose_disequality create raw
        // Symbol::Named(">="|">") terms via mk_app, bypassing the normalizing
        // mk_ge/mk_gt. See ay-core/src/term/preprocess.rs:34,79.
        let (op, lhs, rhs) = if name == "<=" {
            (CmpOp::Le, args[0], args[1])
        } else if name == "<" {
            (CmpOp::Lt, args[0], args[1])
        } else if name == ">=" {
            (CmpOp::Le, args[1], args[0])
        } else if name == ">" {
            (CmpOp::Lt, args[1], args[0])
        } else {
            return None;
        };
        let sort = trace.sort(lhs).clone();
        let lhs_expr = self.term_cache.get(&lhs)?.clone();
        let rhs_expr = self.term_cache.get(&rhs)?.clone();
        Some(BoundInfo {
            sort,
            op,
            lhs_term: lhs,
            rhs_term: rhs,
            lhs_expr,
            rhs_expr,
        })
    }

    /// Try to build an actual Farkas combination proof at the base case.
    ///
    /// Dispatch order:
    /// 1. Single-bound contradiction for the trivial N=1 case
    /// 2. Chain proof (transitivity): works for any N bounds forming a directed path
    /// 3. Additive proof: N-bound all-≤ Int with concrete endpoints
    /// 4. Weighted additive proof for positive integer Farkas coefficients
    /// 5. Single-bound contradiction fallback for concrete contradictory tails
    /// 6. Connected subset replay for disconnected active bounds
    /// 7. None → caller surfaces trust boundary error
    fn try_farkas_combination(
        &self,
        clause_len: usize,
        bounds: &[ActiveBound<'_>],
        cert: &FarkasCertificate,
        step_id: ProofId,
    ) -> ReconstructResult<Option<Expr>> {
        if let Some(false_proof) =
            self.try_farkas_combination_connected(bounds, clause_len, cert, step_id)?
        {
            return Ok(Some(false_proof));
        }

        Ok(None)
    }

    fn try_farkas_combination_connected(
        &self,
        bounds: &[ActiveBound<'_>],
        clause_len: usize,
        cert: &FarkasCertificate,
        step_id: ProofId,
    ) -> ReconstructResult<Option<Expr>> {
        if let Some(false_proof) =
            self.try_farkas_combination_inner(bounds, clause_len, cert, step_id)?
        {
            return Ok(Some(false_proof));
        }

        if bounds.len() < 3 {
            return Ok(None);
        }

        // When the full active set does not reconstruct, a smaller connected
        // sub-problem may still prove `False`. This keeps the search bounded to
        // independent arithmetic components instead of enumerating all subsets.
        let mut components = connected_bound_components(bounds)
            .into_iter()
            .filter(|component| component.len() >= 2 && component.len() < bounds.len())
            .collect::<Vec<_>>();
        components.sort_by_key(|component| std::cmp::Reverse(component.len()));

        for component in components {
            if let Some(false_proof) =
                self.try_farkas_combination_inner(&component, clause_len, cert, step_id)?
            {
                return Ok(Some(false_proof));
            }
        }

        Ok(None)
    }

    fn try_farkas_combination_inner(
        &self,
        bounds: &[ActiveBound<'_>],
        clause_len: usize,
        cert: &FarkasCertificate,
        step_id: ProofId,
    ) -> ReconstructResult<Option<Expr>> {
        let n = bounds.len();
        if n == 0 {
            return Ok(None);
        }

        if n == 1 {
            return self.try_single_bound_contradiction(bounds[0], clause_len, step_id.0);
        }

        // Path 1: Transitivity chain
        let chain_result = if n == 2 {
            self.try_two_bound_chain(bounds, clause_len, step_id.0)?
        } else {
            self.try_n_bound_chain(bounds, clause_len, step_id.0)?
        };
        if chain_result.is_some() {
            return Ok(chain_result);
        }

        // Path 2: N-bound additive Le/Lt (Int or Real, concrete endpoints)
        if let Some(false_proof) = self.try_additive_le(bounds, clause_len, step_id.0)? {
            return Ok(Some(false_proof));
        }

        // Path 2.5: Symbolic additive closeout via Int normal-form
        // cancellation. When the concrete fast path fails, Int bounds can use
        // their native accumulator directly; Real bounds first downcast each
        // active hypothesis into the Int proof layer.
        if matches!(bounds[0].sort(), ay::Sort::Int | ay::Sort::Real)
            && bounds
                .iter()
                .all(|b| matches!(b.op(), CmpOp::Le | CmpOp::Lt))
        {
            let combined = match bounds[0].sort() {
                ay::Sort::Int => {
                    let mut accs: Vec<SortCmpAcc> = bounds
                        .iter()
                        .map(|b| SortCmpAcc {
                            lhs: b.lhs_expr().clone(),
                            rhs: b.rhs_expr().clone(),
                            op: b.op(),
                            proof: b.hypothesis(clause_len),
                        })
                        .collect();
                    combine_scaled_bounds(bounds[0].sort(), &mut accs)
                }
                ay::Sort::Real => build_weighted_additive_accumulator(
                    bounds[0].sort(),
                    bounds,
                    &vec![1; bounds.len()],
                    clause_len,
                ),
                _ => None,
            };
            if let Some(combined) = combined {
                if let Some(false_proof) = theory_lemma_lra_sum_nf::try_close_int_additive_nf(
                    combined.op,
                    &combined.lhs,
                    &combined.rhs,
                    &combined.proof,
                ) {
                    return Ok(Some(false_proof));
                }
            }
        }

        // Path 3: Weighted additive — try when unweighted sum is not
        // contradictory but certificate-weighted sum is. Part of #2581.
        if let Some(false_proof) =
            self.try_weighted_additive_le(bounds, clause_len, cert, step_id)?
        {
            return Ok(Some(false_proof));
        }

        // A concrete contradiction on any active bound is enough to close the
        // clause. Keep this after the weighted additive lane so the public
        // `attempt_reconstruction()` surface can still exercise the weighted
        // replay proof path when non-unit Farkas coefficients matter.
        if let Some(false_proof) =
            self.try_any_single_bound_contradiction(bounds, clause_len, step_id.0)?
        {
            return Ok(Some(false_proof));
        }

        Ok(None)
    }

    fn try_single_bound_contradiction(
        &self,
        bound: ActiveBound<'_>,
        clause_len: usize,
        step_index: u32,
    ) -> ReconstructResult<Option<Expr>> {
        let proof = bound.hypothesis(clause_len);
        if bound.lhs_term() == bound.rhs_term() && bound.op() == CmpOp::Lt {
            if let Some(false_proof) =
                expr_builders_arith::mk_lt_irrefl_false(bound.sort(), bound.lhs_expr(), &proof)
            {
                return Ok(Some(false_proof));
            }
        }
        self.close_chain_non_cyclic(
            step_index,
            bound.sort(),
            bound.op(),
            bound.lhs_term(),
            bound.rhs_term(),
            bound.lhs_expr(),
            bound.rhs_expr(),
            &proof,
        )
        .map(Some)
    }
}

/// Build `@False.elim.{0} target false_proof : target`.
fn mk_false_elim(target: &Expr, false_proof: &Expr) -> Expr {
    Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("False.elim"), vec![Level::zero()]),
            target.clone(),
        ),
        false_proof.clone(),
    )
}
