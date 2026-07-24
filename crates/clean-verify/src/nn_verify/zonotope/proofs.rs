// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Formal constructive proof witnesses for zonotope theorems (T01--T08).
//!
//! Each theorem is discharged by executable witness construction over concrete
//! zonotope values. All eight theorem statuses are tracked as
//! [`ProofStatus::DerivedPending`].

use super::concrete::ConcreteZonotope;
use super::relu::{classify_relu, zonotope_relu, ReluCase};
use crate::spec::ProofStatus;

const PROOF_TOL: f64 = 1e-9;

/// Runtime witness for a zonotope proof verification.
#[must_use]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ProofWitness {
    /// Theorem identifier (for example, `"T01"`).
    pub id: &'static str,
    /// Human-readable theorem description.
    pub description: &'static str,
    /// Whether the constructive witness verified successfully.
    pub verified: bool,
    /// Formal proof status in the proof library.
    pub proof_status: ProofStatus,
}

/// **T01 (Interval Hull Soundness):**
/// If `x in Z`, then `x in hull(Z)`.
///
/// Proof:
/// For `x = c + sum_i eps_i g_i` with `|eps_i| <= 1`,
/// `|x_j - c_j| = |sum_i eps_i g_{i,j}| <= sum_i |eps_i| |g_{i,j}| <= sum_i |g_{i,j}|`.
/// Hence `c_j - sum_i |g_{i,j}| <= x_j <= c_j + sum_i |g_{i,j}|`, which is exactly
/// the interval hull bound in dimension `j`.
pub const T01_PROOF_STATUS: ProofStatus = ProofStatus::DerivedPending;

/// **T02 (Linear Transform Exactness):**
/// If `x in Z`, then `W*x + b in W*Z + b`.
///
/// Proof:
/// Write `x = c + sum_i eps_i g_i` with `|eps_i| <= 1`. Then
/// `W*x + b = W*c + b + sum_i eps_i (W*g_i)`. The transformed zonotope has
/// center `W*c + b` and generators `W*g_i`, so the same coefficients witness
/// membership exactly.
pub const T02_PROOF_STATUS: ProofStatus = ProofStatus::DerivedPending;

/// **T03 (ReLU Overapproximation Soundness):**
/// For `x in Z`, `relu(x) in zonotope_relu(Z)`.
///
/// Proof:
/// Case analysis on each interval hull coordinate `[l_j, u_j]`.
/// If `l_j >= 0`, ReLU is identity. If `u_j <= 0`, ReLU is zero.
/// If `l_j < 0 < u_j`, the lambda-relaxation uses
/// `lambda = u_j / (u_j - l_j)` and `mu = (1 - lambda) u_j / 2`.
/// The transformed coordinate is `lambda * x_j + mu + eta_j * mu` for some
/// `eta_j in [-1, 1]`, and `relu(x_j)` lies in that interval.
pub const T03_PROOF_STATUS: ProofStatus = ProofStatus::DerivedPending;

/// **T04 (Lambda-Relaxation Tightness):**
/// For a crossing interval `[l, u]`, the lambda-relaxation is minimal.
///
/// Proof:
/// The upper facet must contain `(l, 0)` and `(u, u)`, so it is the unique line
/// through those endpoints. The lower facet is `y = 0`. Any smaller vertical gap
/// would exclude one endpoint or a point on the ReLU graph.
pub const T04_PROOF_STATUS: ProofStatus = ProofStatus::DerivedPending;

/// **T05 (ReLU Always-Active Exactness):**
/// If every interval lower bound is non-negative, `zonotope_relu(Z) = Z`.
///
/// Proof:
/// When `l_j >= 0` in every dimension, `relu(x_j) = x_j` for all `x in Z`.
/// The implementation leaves the center and generators unchanged and adds no
/// fresh error generators.
pub const T05_PROOF_STATUS: ProofStatus = ProofStatus::DerivedPending;

/// **T06 (ReLU Always-Inactive Exactness):**
/// If every interval upper bound is non-positive, `zonotope_relu(Z)` is the origin.
///
/// Proof:
/// When `u_j <= 0` in every dimension, `relu(x_j) = 0`.
/// The implementation zeroes the center and every generator component.
pub const T06_PROOF_STATUS: ProofStatus = ProofStatus::DerivedPending;

/// **T07 (Affine+ReLU Composition Soundness):**
/// Exact affine propagation composed with sound ReLU propagation is sound.
///
/// Proof:
/// By T02, `W*x + b` is contained in the affine-transformed zonotope.
/// By T03, `relu(W*x + b)` is contained in the ReLU overapproximation of that
/// zonotope. Composition preserves soundness.
pub const T07_PROOF_STATUS: ProofStatus = ProofStatus::DerivedPending;

/// **T08 (Minkowski Sum Soundness):**
/// If `x1 in Z1` and `x2 in Z2`, then `x1 + x2 in Z1 + Z2`.
///
/// Proof:
/// Write `x1 = c1 + sum_i eps_i g_i` and `x2 = c2 + sum_j eta_j h_j`.
/// Then `x1 + x2 = (c1 + c2) + sum_i eps_i g_i + sum_j eta_j h_j`.
/// The Minkowski-sum zonotope uses center `c1 + c2` and concatenates both
/// generator lists, so the concatenated coefficient vector is a witness.
pub const T08_PROOF_STATUS: ProofStatus = ProofStatus::DerivedPending;

/// Verify T01 using a concrete coefficient witness.
pub fn verify_t01_interval_hull_sound(
    zonotope: &ConcreteZonotope,
    coefficients: &[f64],
) -> ProofWitness {
    let verified = match zonotope.sample_point(coefficients) {
        Ok(point) if coeffs_in_unit_box(coefficients) => {
            let (lower, upper) = zonotope.to_interval();
            point.iter().enumerate().all(|(j, &x_j)| {
                let radius: f64 = zonotope.generators.iter().map(|g| g[j].abs()).sum();
                (x_j - zonotope.center[j]).abs() <= radius + PROOF_TOL
                    && x_j >= lower[j] - PROOF_TOL
                    && x_j <= upper[j] + PROOF_TOL
            })
        }
        Ok(_) => true,
        Err(_) => false,
    };

    ProofWitness {
        id: "T01",
        description: "Interval Hull Soundness",
        verified,
        proof_status: T01_PROOF_STATUS,
    }
}

/// Verify T02 using the same coefficients before and after the affine map.
pub fn verify_t02_linear_transform_exact(
    zonotope: &ConcreteZonotope,
    weight: &[&[f64]],
    bias: &[f64],
    coefficients: &[f64],
) -> ProofWitness {
    let verified = if !affine_shape_matches(zonotope, weight, bias) {
        false
    } else {
        match zonotope.sample_point(coefficients) {
            Ok(point) if coeffs_in_unit_box(coefficients) => {
                let transformed = zonotope.linear_transform(weight, bias);
                let expected = affine_point(weight, bias, &point);
                match transformed.sample_point(coefficients) {
                    Ok(actual) => {
                        vector_approx_eq(&actual, &expected) && transformed.hull_contains(&expected)
                    }
                    Err(_) => false,
                }
            }
            Ok(_) => true,
            Err(_) => false,
        }
    };

    ProofWitness {
        id: "T02",
        description: "Linear Transform Exactness",
        verified,
        proof_status: T02_PROOF_STATUS,
    }
}

/// Verify T03 by constructing explicit lambda-relaxation witness coefficients.
pub fn verify_t03_relu_overapprox_sound(
    zonotope: &ConcreteZonotope,
    coefficients: &[f64],
) -> ProofWitness {
    let verified = match zonotope.sample_point(coefficients) {
        Ok(point) if coeffs_in_unit_box(coefficients) => {
            let relu_zonotope = zonotope_relu(zonotope);
            let relu_point: Vec<f64> = point.iter().map(|&x| x.max(0.0)).collect();
            match relu_witness_coefficients(zonotope, &point, coefficients) {
                Some(witness_coeffs) => match relu_zonotope.sample_point(&witness_coeffs) {
                    Ok(actual) => {
                        vector_approx_eq(&actual, &relu_point)
                            && relu_zonotope.hull_contains(&relu_point)
                    }
                    Err(_) => false,
                },
                None => false,
            }
        }
        Ok(_) => true,
        Err(_) => false,
    };

    ProofWitness {
        id: "T03",
        description: "ReLU Overapproximation Soundness",
        verified,
        proof_status: T03_PROOF_STATUS,
    }
}

/// Verify T04 on a crossing interval `[lower, upper]`.
pub fn verify_t04_relu_lambda_relaxation_tight(lower: f64, upper: f64) -> ProofWitness {
    let verified = if !(lower < 0.0 && 0.0 < upper) {
        true
    } else {
        let lambda = upper / (upper - lower);
        let mu = (1.0 - lambda) * upper / 2.0;
        let upper_intercept_from_lower = -lambda * lower;
        let upper_intercept_from_upper = upper - lambda * upper;
        approx_eq(lambda * lower + upper_intercept_from_lower, 0.0)
            && approx_eq(lambda * upper + upper_intercept_from_lower, upper)
            && approx_eq(upper_intercept_from_lower, upper_intercept_from_upper)
            && approx_eq(2.0 * mu, upper_intercept_from_lower)
            && lambda > 0.0
            && lambda < 1.0
            && mu > 0.0
    };

    ProofWitness {
        id: "T04",
        description: "Lambda-Relaxation Tightness",
        verified,
        proof_status: T04_PROOF_STATUS,
    }
}

/// Verify T05 by checking that ReLU is the identity on an always-active zonotope.
pub fn verify_t05_relu_always_active_exact(zonotope: &ConcreteZonotope) -> ProofWitness {
    let (lower, _) = zonotope.to_interval();
    let verified = if lower.iter().all(|&l| l >= 0.0) {
        let relu_zonotope = zonotope_relu(zonotope);
        relu_zonotope.num_generators() == zonotope.num_generators()
            && zonotope_approx_eq(&relu_zonotope, zonotope)
    } else {
        true
    };

    ProofWitness {
        id: "T05",
        description: "ReLU Always-Active Exactness",
        verified,
        proof_status: T05_PROOF_STATUS,
    }
}

/// Verify T06 by checking that ReLU collapses an always-inactive zonotope to the origin.
pub fn verify_t06_relu_always_inactive_exact(zonotope: &ConcreteZonotope) -> ProofWitness {
    let (_, upper) = zonotope.to_interval();
    let verified = if upper.iter().all(|&u| u <= 0.0) {
        is_origin_zonotope(&zonotope_relu(zonotope))
    } else {
        true
    };

    ProofWitness {
        id: "T06",
        description: "ReLU Always-Inactive Exactness",
        verified,
        proof_status: T06_PROOF_STATUS,
    }
}

/// Verify T07 by composing the T02 and T03 witnesses.
pub fn verify_t07_affine_relu_composition_sound(
    zonotope: &ConcreteZonotope,
    weight: &[&[f64]],
    bias: &[f64],
    coefficients: &[f64],
) -> ProofWitness {
    let verified = if !affine_shape_matches(zonotope, weight, bias)
        || coefficients.len() != zonotope.num_generators()
    {
        false
    } else if !coeffs_in_unit_box(coefficients) {
        true
    } else {
        let affine_witness =
            verify_t02_linear_transform_exact(zonotope, weight, bias, coefficients);
        let affine_zonotope = zonotope.linear_transform(weight, bias);
        let relu_witness = verify_t03_relu_overapprox_sound(&affine_zonotope, coefficients);
        affine_witness.verified && relu_witness.verified
    };

    ProofWitness {
        id: "T07",
        description: "Affine+ReLU Composition Soundness",
        verified,
        proof_status: T07_PROOF_STATUS,
    }
}

/// Verify T08 by concatenating the two membership witnesses.
pub fn verify_t08_minkowski_sum_sound(
    left: &ConcreteZonotope,
    right: &ConcreteZonotope,
    left_coefficients: &[f64],
    right_coefficients: &[f64],
) -> ProofWitness {
    let verified = if left.dim() != right.dim() {
        false
    } else {
        match (
            left.sample_point(left_coefficients),
            right.sample_point(right_coefficients),
        ) {
            (Ok(left_point), Ok(right_point))
                if coeffs_in_unit_box(left_coefficients)
                    && coeffs_in_unit_box(right_coefficients) =>
            {
                match left.minkowski_sum(right) {
                    Ok(sum_zonotope) => {
                        let sum_point: Vec<f64> = left_point
                            .iter()
                            .zip(right_point.iter())
                            .map(|(x, y)| x + y)
                            .collect();
                        let witness_coeffs: Vec<f64> = left_coefficients
                            .iter()
                            .copied()
                            .chain(right_coefficients.iter().copied())
                            .collect();
                        match sum_zonotope.sample_point(&witness_coeffs) {
                            Ok(actual) => {
                                vector_approx_eq(&actual, &sum_point)
                                    && sum_zonotope.hull_contains(&sum_point)
                            }
                            Err(_) => false,
                        }
                    }
                    Err(_) => false,
                }
            }
            (Ok(_), Ok(_)) => true,
            _ => false,
        }
    };

    ProofWitness {
        id: "T08",
        description: "Minkowski Sum Soundness",
        verified,
        proof_status: T08_PROOF_STATUS,
    }
}

/// Summary of all zonotope theorem statuses in this module.
#[must_use]
pub fn proof_statuses() -> Vec<(&'static str, &'static str, ProofStatus)> {
    vec![
        ("T01", "Interval Hull Soundness", T01_PROOF_STATUS),
        ("T02", "Linear Transform Exactness", T02_PROOF_STATUS),
        ("T03", "ReLU Overapproximation Soundness", T03_PROOF_STATUS),
        ("T04", "Lambda-Relaxation Tightness", T04_PROOF_STATUS),
        ("T05", "ReLU Always-Active Exactness", T05_PROOF_STATUS),
        ("T06", "ReLU Always-Inactive Exactness", T06_PROOF_STATUS),
        ("T07", "Affine+ReLU Composition Soundness", T07_PROOF_STATUS),
        ("T08", "Minkowski Sum Soundness", T08_PROOF_STATUS),
    ]
}

#[must_use]
fn approx_eq(left: f64, right: f64) -> bool {
    (left - right).abs() <= PROOF_TOL
}

#[must_use]
fn vector_approx_eq(left: &[f64], right: &[f64]) -> bool {
    left.len() == right.len()
        && left
            .iter()
            .zip(right.iter())
            .all(|(&lhs, &rhs)| approx_eq(lhs, rhs))
}

#[must_use]
fn zonotope_approx_eq(left: &ConcreteZonotope, right: &ConcreteZonotope) -> bool {
    vector_approx_eq(&left.center, &right.center)
        && left.generators.len() == right.generators.len()
        && left
            .generators
            .iter()
            .zip(right.generators.iter())
            .all(|(lhs, rhs)| vector_approx_eq(lhs, rhs))
}

#[must_use]
fn coeffs_in_unit_box(coefficients: &[f64]) -> bool {
    coefficients
        .iter()
        .all(|&coefficient| (-1.0 - PROOF_TOL..=1.0 + PROOF_TOL).contains(&coefficient))
}

#[must_use]
fn affine_shape_matches(zonotope: &ConcreteZonotope, weight: &[&[f64]], bias: &[f64]) -> bool {
    weight.len() == bias.len() && weight.iter().all(|row| row.len() == zonotope.dim())
}

#[must_use]
fn affine_point(weight: &[&[f64]], bias: &[f64], point: &[f64]) -> Vec<f64> {
    weight
        .iter()
        .zip(bias.iter())
        .map(|(row, &offset)| {
            offset
                + row
                    .iter()
                    .zip(point.iter())
                    .map(|(w, x)| w * x)
                    .sum::<f64>()
        })
        .collect()
}

#[must_use]
fn relu_witness_coefficients(
    zonotope: &ConcreteZonotope,
    point: &[f64],
    coefficients: &[f64],
) -> Option<Vec<f64>> {
    if point.len() != zonotope.dim() || coefficients.len() != zonotope.num_generators() {
        return None;
    }

    let (lower, upper) = zonotope.to_interval();
    let mut witness = coefficients.to_vec();
    for j in 0..zonotope.dim() {
        if classify_relu(lower[j], upper[j]) != ReluCase::Crossing {
            continue;
        }
        let lambda = upper[j] / (upper[j] - lower[j]);
        let mu = (1.0 - lambda) * upper[j] / 2.0;
        if mu <= 0.0 {
            return None;
        }
        let relu_value = point[j].max(0.0);
        let eta = (relu_value - (lambda * point[j] + mu)) / mu;
        if !(-1.0 - PROOF_TOL..=1.0 + PROOF_TOL).contains(&eta) {
            return None;
        }
        witness.push(eta.clamp(-1.0, 1.0));
    }
    Some(witness)
}

#[must_use]
fn is_origin_zonotope(zonotope: &ConcreteZonotope) -> bool {
    zonotope.center.iter().all(|&value| approx_eq(value, 0.0))
        && zonotope
            .generators
            .iter()
            .all(|generator| generator.iter().all(|&value| approx_eq(value, 0.0)))
}
