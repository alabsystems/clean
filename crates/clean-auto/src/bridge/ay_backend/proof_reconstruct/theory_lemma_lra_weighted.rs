// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Weighted additive Farkas replay for bridge LRA reconstruction.
//!
//! When the unweighted additive sum is not contradictory but the certificate-
//! weighted sum IS, this module scales each bound by its positive Farkas
//! coefficient via repeated addition, then combines the scaled bounds.
//!
//! After building the weighted accumulator, reconstruction first tries a direct
//! concrete contradiction on integer endpoints. If that fails, the weighted
//! Int accumulator falls through to symbolic additive closeout via
//! normal-form cancellation.
//!
//! Supports both integer and fractional rational coefficients. Fractional
//! coefficients are rationalized to positive integers by multiplying all
//! coefficients by the LCM of their denominators (Part of #302).
//!
//! Part of #2581. Design: `designs/2026-03-12-2581-weighted-additive-farkas-replay.md`

use ay_core::ProofId;
use clean_kernel::Expr;
use num_rational::Rational64;

use super::expr_builders_arith::{self, CmpOp};
use super::farkas_certificate::FarkasCertificate;
use super::theory_lemma_lra::ActiveBound;
use super::theory_lemma_lra_additive::{combine_scaled_bounds, scale_bound, SortCmpAcc};
use super::theory_lemma_lra_sum_nf;
use super::{ReconstructResult, ReconstructionContext};

pub(super) fn build_weighted_additive_accumulator(
    sort: &ay::Sort,
    bounds: &[ActiveBound<'_>],
    coeffs: &[u64],
    clause_len: usize,
) -> Option<SortCmpAcc> {
    if bounds.len() != coeffs.len() || bounds.is_empty() {
        return None;
    }

    let int_sort = ay::Sort::Int;
    let mut scaled: Vec<SortCmpAcc> = Vec::with_capacity(bounds.len());
    match sort {
        ay::Sort::Int => {
            for (&bound, &coeff) in bounds.iter().zip(coeffs.iter()) {
                let hyp = bound.hypothesis(clause_len);
                let acc = scale_bound(
                    &int_sort,
                    bound.op(),
                    bound.lhs_expr(),
                    bound.rhs_expr(),
                    &hyp,
                    coeff,
                )?;
                scaled.push(acc);
            }
        }
        ay::Sort::Real => {
            for (&bound, &coeff) in bounds.iter().zip(coeffs.iter()) {
                let downcasted =
                    super::expr_builders_real_downcast::downcast_real_active_bound_to_int(
                        bound, clause_len,
                    )?;
                let acc = scale_bound(
                    &int_sort,
                    downcasted.op,
                    &downcasted.lhs,
                    &downcasted.rhs,
                    &downcasted.proof,
                    coeff,
                )?;
                scaled.push(acc);
            }
        }
        _ => return None,
    }

    combine_scaled_bounds(&int_sort, &mut scaled)
}

#[cfg(test)]
pub(super) fn build_weighted_additive_false(
    sort: &ay::Sort,
    bounds: &[ActiveBound<'_>],
    coeffs: &[u64],
    clause_len: usize,
) -> Option<Expr> {
    let acc = build_weighted_additive_accumulator(sort, bounds, coeffs, clause_len)?;
    Some(expr_builders_arith::mk_int_concrete_false(
        acc.op, &acc.lhs, &acc.rhs, &acc.proof,
    ))
}

impl<'a> ReconstructionContext<'a> {
    /// Try to build a weighted N-bound additive combination proof.
    ///
    /// Requires: N >= 2 bounds, all Le/Lt, same sort (Int or Real), and
    /// positive coefficients. Concrete integer endpoints enable a direct
    /// contradiction check; otherwise the combined Int accumulator falls
    /// through to symbolic additive closeout. Fractional rational
    /// coefficients are scaled to positive integers via LCM of denominators
    /// (Part of #302).
    pub(super) fn try_weighted_additive_le(
        &self,
        bounds: &[ActiveBound<'_>],
        clause_len: usize,
        cert: &FarkasCertificate,
        _step_id: ProofId,
    ) -> ReconstructResult<Option<Expr>> {
        if bounds.len() < 2 {
            return Ok(None);
        }

        // Skip when all coefficients are unit — the unweighted path already tried.
        if cert.all_unit() {
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

        // Pair coefficients with bounds via the certificate's O(n) lookup
        // instead of the previous O(n^2) scan over raw trace data.
        let paired: Vec<_> = bounds
            .iter()
            .filter_map(|bound| {
                cert.coefficient_for(bound.clause_idx)
                    .map(|coeff| (*bound, coeff))
            })
            .collect();
        if paired.len() != bounds.len() {
            return Ok(None); // coefficient mismatch
        }

        // Try direct positive-integer conversion first; if any coefficient
        // is fractional, rationalize by scaling all by LCM of denominators.
        let int_coeffs: Vec<u64> = match paired
            .iter()
            .map(|(_, coeff)| to_positive_int(*coeff))
            .collect::<Option<Vec<_>>>()
        {
            Some(c) => c,
            None => match rationalize_to_positive_ints(&paired) {
                Some(c) => c,
                None => return Ok(None),
            },
        };

        // Skip if all coefficients are 1 — the unweighted path already tried.
        if int_coeffs.iter().all(|&c| c == 1) {
            return Ok(None);
        }

        let Some(acc) = build_weighted_additive_accumulator(sort, bounds, &int_coeffs, clause_len)
        else {
            return Ok(None);
        };

        // Extract concrete endpoints and compute weighted sums.
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
            .collect::<Vec<_>>();
        if concrete.iter().all(Option::is_some) {
            let concrete: Vec<_> = concrete.into_iter().flatten().collect();
            let mut weighted_lhs = num_bigint::BigInt::from(0);
            let mut weighted_rhs = num_bigint::BigInt::from(0);
            for ((lhs, rhs), &coeff) in concrete.iter().zip(int_coeffs.iter()) {
                let k = num_bigint::BigInt::from(coeff);
                weighted_lhs += &k * lhs;
                weighted_rhs += &k * rhs;
            }

            let violated = match acc.op {
                CmpOp::Le => weighted_lhs > weighted_rhs,
                CmpOp::Lt => weighted_lhs >= weighted_rhs,
            };
            if violated {
                return Ok(Some(expr_builders_arith::mk_int_concrete_false(
                    acc.op, &acc.lhs, &acc.rhs, &acc.proof,
                )));
            }
        }

        Ok(theory_lemma_lra_sum_nf::try_close_int_additive_nf(
            acc.op, &acc.lhs, &acc.rhs, &acc.proof,
        ))
    }
}

/// Convert a Rational64 to a positive u64 if it is a positive integer.
fn to_positive_int(r: Rational64) -> Option<u64> {
    if *r.denom() != 1 {
        return None;
    }
    let n = *r.numer();
    if n <= 0 {
        return None;
    }
    u64::try_from(n).ok()
}

/// Scale positive rational coefficients to positive integers by multiplying
/// all by the LCM of their denominators. Returns `None` if any coefficient is
/// non-positive or if integer overflow occurs during scaling.
fn rationalize_to_positive_ints(paired: &[(ActiveBound<'_>, Rational64)]) -> Option<Vec<u64>> {
    let zero = Rational64::from_integer(0);
    if paired.iter().any(|(_, coeff)| *coeff <= zero) {
        return None;
    }

    let lcm_denom = paired
        .iter()
        .map(|(_, coeff)| *coeff.denom())
        .try_fold(1i64, lcm_i64)?;

    let scale = Rational64::from_integer(lcm_denom);
    paired
        .iter()
        .map(|(_, coeff)| to_positive_int(*coeff * scale))
        .collect()
}

fn gcd_i64(mut a: i64, mut b: i64) -> i64 {
    a = a.abs();
    b = b.abs();
    while b != 0 {
        let t = b;
        b = a % b;
        a = t;
    }
    a
}

fn lcm_i64(a: i64, b: i64) -> Option<i64> {
    if a == 0 || b == 0 {
        return Some(0);
    }
    (a / gcd_i64(a, b)).checked_mul(b)
}
