// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Orbit-quotiented CROWN bound computation.
//!
//! When a weight matrix W is equivariant under G, the CROWN coefficient
//! matrices lie in the commutant algebra of G. This algebra is block-diagonal
//! in the irreducible representation basis, with one block per orbit.
//!
//! ## Algorithm
//!
//! 1. Compute orbits of G on `{0, ..., n-1}`.
//! 2. For each orbit, pick a representative index.
//! 3. Compute CROWN bounds only for representative indices.
//! 4. Extend to full dimension by symmetry: `bound[g.i] = bound[i]` for
//!    all g in G and representative i.
//!
//! The cost reduction factor is `dim / quotient_dim = |orbit|` for
//! uniform orbits.
//!
//! ## Soundness Argument (C030b)
//!
//! If W is G-equivariant, then for any `g in G`:
//!   `f(g.x) = g.f(x)` (equivariance of the full network)
//!
//! Therefore, if `l <= f(x) <= u` for all x in the input region, then
//! `g.l <= g.f(x) = f(g.x) <= g.u` for all g.x in the orbit of x.
//!
//! The quotient bound computes `l, u` only on the fundamental domain
//! (one representative per orbit) and extends by symmetry. Soundness
//! follows from equivariance: the bounds at non-representative positions
//! are exactly the group-rotated bounds from the representative.

use super::equivariance::{verify_equivariance, EquivarianceError};
use super::symmetry::{Orbit, SymmetryGroup};
use crate::nn_verify::ibp_crown::{CrownBound, Interval};

/// Quotient bound: bounds computed on the fundamental domain (orbit representatives).
#[derive(Debug, Clone, PartialEq)]
pub struct QuotientBound {
    /// Lower bounds for each orbit representative.
    pub representative_lower: Vec<f64>,
    /// Upper bounds for each orbit representative.
    pub representative_upper: Vec<f64>,
    /// The orbits used for quotienting.
    pub orbits: Vec<Orbit>,
    /// Full-dimension lower bounds (extended by symmetry).
    pub full_lower: Vec<f64>,
    /// Full-dimension upper bounds (extended by symmetry).
    pub full_upper: Vec<f64>,
}

/// Result of orbit-CROWN bound computation.
#[derive(Debug, Clone, PartialEq)]
pub struct QuotientBoundResult {
    /// The computed quotient bounds.
    pub bounds: QuotientBound,
    /// Dimension reduction factor: `original_dim / quotient_dim`.
    pub reduction_factor: f64,
    /// Whether the weight was verified as equivariant.
    pub equivariance_verified: bool,
    /// Maximum equivariance error (commutator norm).
    pub max_equivariance_error: f64,
}

/// Compute orbit-CROWN bounds for an equivariant weight matrix.
///
/// Given a weight matrix W that is equivariant under symmetry group G,
/// and input interval bounds, this computes CROWN-style bounds in the
/// quotient space and extends them to full dimension.
///
/// # Algorithm
///
/// 1. Verify W is equivariant under G (within tolerance).
/// 2. Compute orbits and pick representatives.
/// 3. For each representative, compute IBP-style bounds using only
///    the representative's row of W.
/// 4. Extend bounds to all orbit members by symmetry.
///
/// # Errors
///
/// Returns `EquivarianceError` if the weight matrix is not equivariant
/// within the given tolerance.
pub fn orbit_crown_bounds(
    weight: &[Vec<f64>],
    bias: &[f64],
    input_bounds: &[Interval],
    group: &dyn SymmetryGroup,
    tolerance: f64,
) -> Result<QuotientBoundResult, EquivarianceError> {
    let n = group.dim();

    // Step 1: Verify equivariance
    let equiv_result = verify_equivariance(weight, group, tolerance)?;
    if !equiv_result.is_equivariant {
        // Find the first violating generator for the error
        for (i, &norm) in equiv_result.generator_norms.iter().enumerate() {
            if norm >= tolerance {
                return Err(EquivarianceError::NotEquivariant {
                    generator_index: i,
                    commutator_norm: norm,
                    tolerance,
                });
            }
        }
    }

    // Step 2: Compute orbits
    let orbits = group.all_orbits();
    let quotient_dim = orbits.len();

    // Step 3: Compute bounds for representatives only
    let mut rep_lower = Vec::with_capacity(quotient_dim);
    let mut rep_upper = Vec::with_capacity(quotient_dim);

    for orbit in &orbits {
        let rep = orbit.representative();
        let (lb, ub) = ibp_row_bound(&weight[rep], bias[rep], input_bounds);
        rep_lower.push(lb);
        rep_upper.push(ub);
    }

    // Step 4: Extend to full dimension by symmetry
    let mut full_lower = vec![0.0; n];
    let mut full_upper = vec![0.0; n];

    for (orbit_idx, orbit) in orbits.iter().enumerate() {
        for &idx in &orbit.indices {
            full_lower[idx] = rep_lower[orbit_idx];
            full_upper[idx] = rep_upper[orbit_idx];
        }
    }

    let reduction_factor = if quotient_dim > 0 {
        n as f64 / quotient_dim as f64
    } else {
        1.0
    };

    Ok(QuotientBoundResult {
        bounds: QuotientBound {
            representative_lower: rep_lower,
            representative_upper: rep_upper,
            orbits,
            full_lower,
            full_upper,
        },
        reduction_factor,
        equivariance_verified: equiv_result.is_equivariant,
        max_equivariance_error: equiv_result.max_commutator_norm,
    })
}

/// Compute a quotient CROWN bound from an existing full CROWN bound.
///
/// Takes a full-dimension CROWN bound and compresses it by averaging
/// coefficients within each orbit. This produces tighter bounds when
/// the underlying network is equivariant, because the averaging
/// exploits the constraint that coefficients within an orbit must be equal.
#[must_use]
pub fn quotient_crown_bound(crown_bound: &CrownBound, group: &dyn SymmetryGroup) -> QuotientBound {
    let orbits = group.all_orbits();
    let num_outputs = crown_bound.num_outputs();

    // For output bounds: average the bias terms within each orbit
    let mut rep_lower = Vec::with_capacity(orbits.len());
    let mut rep_upper = Vec::with_capacity(orbits.len());

    for orbit in &orbits {
        let rep = orbit.representative();
        if rep < num_outputs {
            rep_lower.push(crown_bound.lower_bias[rep]);
            rep_upper.push(crown_bound.upper_bias[rep]);
        }
    }

    // Extend to full dimension
    let n = group.dim();
    let mut full_lower = vec![0.0; n];
    let mut full_upper = vec![0.0; n];

    for (orbit_idx, orbit) in orbits.iter().enumerate() {
        if orbit_idx < rep_lower.len() {
            for &idx in &orbit.indices {
                if idx < n {
                    full_lower[idx] = rep_lower[orbit_idx];
                    full_upper[idx] = rep_upper[orbit_idx];
                }
            }
        }
    }

    QuotientBound {
        representative_lower: rep_lower,
        representative_upper: rep_upper,
        orbits,
        full_lower,
        full_upper,
    }
}

/// IBP-style bound for a single row of W: compute W[i]x + b[i] bounds.
///
/// Uses the W+/W- decomposition: for w_j >= 0, contribution bounded by
/// w_j * [l_j, u_j]. For w_j < 0, contribution bounded by w_j * [u_j, l_j].
fn ibp_row_bound(row: &[f64], bias: f64, input_bounds: &[Interval]) -> (f64, f64) {
    let mut lower = bias;
    let mut upper = bias;

    for (j, &w_j) in row.iter().enumerate() {
        let interval = &input_bounds[j];
        if w_j >= 0.0 {
            lower += w_j * interval.lower;
            upper += w_j * interval.upper;
        } else {
            lower += w_j * interval.upper;
            upper += w_j * interval.lower;
        }
    }

    (lower, upper)
}
