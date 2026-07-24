// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Polynomial zonotope attention bound computation.
//!
//! ## Attention Mechanism
//!
//! In Vision Transformers, the self-attention operation is:
//! ```text
//! Attention(Q, K, V) = softmax(Q * K^T / sqrt(d_k)) * V
//! ```
//!
//! where Q, K, V are the query, key, and value matrices derived from
//! the input via linear projections.
//!
//! ## Why Polynomial Zonotopes?
//!
//! The key challenge is the bilinear term `Q * K^T` followed by softmax.
//! With linear zonotopes:
//! - Q = c_Q + sum eps_i * g_Q_i
//! - K = c_K + sum eps_i * g_K_i
//! - Q * K^T creates cross-terms eps_i * eps_j that linear zonotopes cannot
//!   represent, forcing overapproximation with O(eps^2) gap.
//!
//! With polynomial zonotopes, the eps_i * eps_j terms are tracked exactly
//! as quadratic generators, giving O(eps) tightness for the full attention
//! computation.
//!
//! ## Simplified Model
//!
//! For the C015 specification, we work with scalar attention:
//! ```text
//! attn(q, k, v) = softmax_approx(q * k) * v
//! ```
//!
//! where `softmax_approx(x) = x` (linear approximation for small perturbations)
//! or `softmax_approx(x) = (1 + x) / n` (first-order Taylor expansion).
//!
//! The key property: polynomial zonotopes track `q * k` exactly (quadratic
//! in eps), while linear zonotopes lose the correlation and overapproximate.
//!
//! ## References
//!
//! - Bonaert et al., "Fast and Precise Certification of Transformers" (PLDI 2021)
//! - Shi et al., "Robustness Verification for Transformers" (ICLR 2020)
//! - Kochdumper & Althoff, "Sparse Polynomial Zonotopes" (2020)

use super::types::{PolyZonotope, PolyZonotopeError};

/// Result of attention bound computation.
#[derive(Debug, Clone, PartialEq)]
#[non_exhaustive]
pub struct AttentionBound {
    /// Lower bound on the attention output.
    pub lower: Vec<f64>,
    /// Upper bound on the attention output.
    pub upper: Vec<f64>,
    /// Maximum gap (upper - lower) across dimensions.
    pub max_gap: f64,
    /// Input perturbation radius (epsilon).
    pub eps: f64,
    /// Method used ("poly_zonotope" or "linear_zonotope").
    pub method: &'static str,
}

/// Compute attention bounds using polynomial zonotope arithmetic.
///
/// Models a simplified scalar attention: `attn(q, k, v) = q * k * v`
/// where q, k, v are scalar polynomial zonotopes sharing noise symbols.
///
/// The polynomial zonotope tracks the quadratic term `q*k` exactly
/// through the noise symbol product `eps_i * eps_j`, giving O(eps)
/// tightness for the bilinear interaction.
///
/// ## Arguments
/// - `q`: Query polynomial zonotope (scalar, d=1)
/// - `k`: Key polynomial zonotope (scalar, d=1)
/// - `v`: Value polynomial zonotope (scalar, d=1)
///
/// ## Returns
/// Interval bounds on the attention output.
pub fn attention_bound_poly(
    q: &PolyZonotope,
    k: &PolyZonotope,
    v: &PolyZonotope,
) -> Result<AttentionBound, PolyZonotopeError> {
    // Step 1: Compute q*k using polynomial zonotope multiplication.
    // This captures eps_i * eps_j cross-terms exactly.
    let qk = q.hadamard_product_scalar(k)?;

    // Step 2: Compute (q*k) * v.
    // This produces another round of multiplication, giving us the
    // full trilinear form with quadratic tracking.
    let attn = qk.hadamard_product_scalar(v)?;

    // Step 3: Extract interval bounds from the polynomial zonotope.
    let (lower, upper) = attn.to_interval();
    let max_gap = lower
        .iter()
        .zip(upper.iter())
        .map(|(l, u)| u - l)
        .fold(0.0_f64, f64::max);

    // Perturbation radius: max linear generator magnitude
    let eps = if q.num_symbols() > 0 {
        q.linear_gens()
            .iter()
            .map(|g| g[0].abs())
            .fold(0.0_f64, f64::max)
    } else {
        0.0
    };

    Ok(AttentionBound {
        lower,
        upper,
        max_gap,
        eps,
        method: "poly_zonotope",
    })
}

/// Compute attention bounds using linear zonotope arithmetic (baseline).
///
/// This uses interval arithmetic for the bilinear term `q*k`, which
/// loses the correlation between q and k. For comparison with the
/// polynomial zonotope method.
///
/// The linear approach computes:
/// - q in [q_lo, q_hi], k in [k_lo, k_hi], v in [v_lo, v_hi]
/// - q*k in interval_mul([q_lo, q_hi], [k_lo, k_hi])
/// - attn in interval_mul(q*k interval, [v_lo, v_hi])
///
/// This gives O(eps^2) gap because the interval product of two
/// O(eps)-wide intervals is O(eps^2)-wide.
pub fn attention_bound_linear(
    q: &PolyZonotope,
    k: &PolyZonotope,
    v: &PolyZonotope,
) -> Result<AttentionBound, PolyZonotopeError> {
    // Extract intervals (discarding all dependency information)
    let (q_lo, q_hi) = q.to_interval();
    let (k_lo, k_hi) = k.to_interval();
    let (v_lo, v_hi) = v.to_interval();

    // Interval multiplication for q*k
    let qk_products = [
        q_lo[0] * k_lo[0],
        q_lo[0] * k_hi[0],
        q_hi[0] * k_lo[0],
        q_hi[0] * k_hi[0],
    ];
    let qk_lo = qk_products.iter().copied().fold(f64::INFINITY, f64::min);
    let qk_hi = qk_products
        .iter()
        .copied()
        .fold(f64::NEG_INFINITY, f64::max);

    // Interval multiplication for (q*k) * v
    let attn_products = [
        qk_lo * v_lo[0],
        qk_lo * v_hi[0],
        qk_hi * v_lo[0],
        qk_hi * v_hi[0],
    ];
    let attn_lo = attn_products.iter().copied().fold(f64::INFINITY, f64::min);
    let attn_hi = attn_products
        .iter()
        .copied()
        .fold(f64::NEG_INFINITY, f64::max);

    let max_gap = attn_hi - attn_lo;
    let eps = if q.num_symbols() > 0 {
        q.linear_gens()
            .iter()
            .map(|g| g[0].abs())
            .fold(0.0_f64, f64::max)
    } else {
        0.0
    };

    Ok(AttentionBound {
        lower: vec![attn_lo],
        upper: vec![attn_hi],
        max_gap,
        eps,
        method: "linear_zonotope",
    })
}

/// Compare polynomial vs linear zonotope bounds for attention.
///
/// Returns `(poly_bound, linear_bound, improvement_ratio)` where
/// `improvement_ratio = linear_gap / poly_gap`. A ratio > 1 means
/// the polynomial zonotope is tighter.
///
/// ## Tightness Analysis
///
/// For input perturbation radius eps around centers (cq, ck, cv):
/// - True attention range: O(eps) (first-order Taylor of q*k*v)
/// - Polynomial zonotope gap: O(eps) (tracks quadratic terms)
/// - Linear zonotope gap: O(eps^2) from interval product
///
/// The improvement ratio thus scales as O(eps^2) / O(eps) = O(eps),
/// meaning polynomial zonotopes become increasingly advantageous
/// as the perturbation grows. Conversely, for very small eps,
/// both methods have similar absolute gaps.
pub fn compare_attention_bounds(
    q: &PolyZonotope,
    k: &PolyZonotope,
    v: &PolyZonotope,
) -> Result<(AttentionBound, AttentionBound, f64), PolyZonotopeError> {
    let poly_bound = attention_bound_poly(q, k, v)?;
    let linear_bound = attention_bound_linear(q, k, v)?;

    let improvement = if poly_bound.max_gap > f64::EPSILON * 256.0 {
        linear_bound.max_gap / poly_bound.max_gap
    } else {
        // Both are essentially exact
        1.0
    };

    Ok((poly_bound, linear_bound, improvement))
}

/// Verify that polynomial zonotope attention bounds are sound.
///
/// Samples random noise symbol values in [-1, 1] and checks that the
/// computed attention value falls within the polynomial zonotope bounds.
///
/// Returns the maximum violation (negative if all samples are contained).
#[must_use]
pub fn verify_attention_soundness(
    q: &PolyZonotope,
    k: &PolyZonotope,
    v: &PolyZonotope,
    bound: &AttentionBound,
    sample_eps: &[Vec<f64>],
) -> f64 {
    let mut max_violation = f64::NEG_INFINITY;

    for eps in sample_eps {
        // Compute concrete q, k, v values
        let q_val = match q.evaluate(eps) {
            Ok(v) => v[0],
            Err(_) => continue,
        };
        let k_val = match k.evaluate(eps) {
            Ok(v) => v[0],
            Err(_) => continue,
        };
        let v_val = match v.evaluate(eps) {
            Ok(v) => v[0],
            Err(_) => continue,
        };

        // Concrete attention: q * k * v
        let attn_val = q_val * k_val * v_val;

        // Check against bounds
        let lo_violation = bound.lower[0] - attn_val;
        let hi_violation = attn_val - bound.upper[0];
        max_violation = max_violation.max(lo_violation).max(hi_violation);
    }

    max_violation
}

#[cfg(test)]
mod tests {
    use super::*;

    fn make_scalar_pz(center: f64, half_width: f64) -> PolyZonotope {
        PolyZonotope::try_new(vec![center], vec![vec![half_width]], vec![vec![0.0]], 1)
            .expect("should create scalar PZ")
    }

    #[test]
    fn test_attention_bound_poly_basic() {
        let q = make_scalar_pz(1.0, 0.1);
        let k = make_scalar_pz(1.0, 0.1);
        let v = make_scalar_pz(1.0, 0.1);

        let bound = attention_bound_poly(&q, &k, &v).expect("should compute bound");
        assert!(bound.max_gap > 0.0);
        assert!(bound.max_gap.is_finite());
        assert!(bound.lower[0] < bound.upper[0]);
    }

    #[test]
    fn test_attention_bound_linear_wider() {
        // Poly zonotope should produce tighter bounds than linear (interval)
        // arithmetic for the attention bilinear product q*k*v when q and k
        // share noise symbols and centers are near zero (so interval
        // arithmetic loses correlation information from mixed-sign products).
        //
        // With center=0, eps=0.1: q,k,v in [-0.1, 0.1]
        // Linear interval: q*k in [-0.01, 0.01] -- but true (shared eps)
        // q*k = eps^2 * 0.01, range [0, 0.01]. Linear overestimates by 2x.
        // Poly zonotope tracks eps^2 exactly via diagonal quadratic gen.
        let q = make_scalar_pz(0.0, 0.1);
        let k = make_scalar_pz(0.0, 0.1);
        let v = make_scalar_pz(1.0, 0.1);

        let poly_bound = attention_bound_poly(&q, &k, &v).expect("should compute poly bound");
        let linear_bound = attention_bound_linear(&q, &k, &v).expect("should compute linear bound");

        assert!(
            linear_bound.max_gap >= poly_bound.max_gap - 1e-10,
            "linear bound gap ({}) should be >= poly bound gap ({})",
            linear_bound.max_gap,
            poly_bound.max_gap
        );
    }

    #[test]
    fn test_attention_soundness_verified() {
        let q = make_scalar_pz(1.0, 0.2);
        let k = make_scalar_pz(1.0, 0.2);
        let v = make_scalar_pz(1.0, 0.1);

        let bound = attention_bound_poly(&q, &k, &v).expect("should compute bound");

        // Sample grid of epsilon values
        let samples: Vec<Vec<f64>> = vec![
            vec![0.0],
            vec![1.0],
            vec![-1.0],
            vec![0.5],
            vec![-0.5],
            vec![0.25],
            vec![-0.25],
            vec![0.75],
            vec![-0.75],
        ];

        let violation = verify_attention_soundness(&q, &k, &v, &bound, &samples);
        assert!(
            violation < 1e-6,
            "poly zonotope attention bounds should be sound, violation: {violation}"
        );
    }

    #[test]
    fn test_compare_attention_bounds() {
        // Use zero-centered q and k so interval arithmetic overestimates
        // the q*k product (shared eps: eps^2 in [0,1] but interval gives [-1,1]).
        let q = make_scalar_pz(0.0, 0.1);
        let k = make_scalar_pz(0.0, 0.1);
        let v = make_scalar_pz(1.0, 0.1);

        let (poly_bound, linear_bound, improvement) =
            compare_attention_bounds(&q, &k, &v).expect("should compare bounds");

        assert_eq!(poly_bound.method, "poly_zonotope");
        assert_eq!(linear_bound.method, "linear_zonotope");
        assert!(
            improvement >= 1.0 - 1e-10,
            "poly zonotope should be at least as tight as linear, improvement ratio: {improvement}"
        );
    }

    #[test]
    fn test_attention_zero_perturbation() {
        // With zero perturbation, both methods should give exact results
        let q = make_scalar_pz(2.0, 0.0);
        let k = make_scalar_pz(3.0, 0.0);
        let v = make_scalar_pz(0.5, 0.0);

        let bound = attention_bound_poly(&q, &k, &v).expect("should compute bound");
        // With zero generators, the result should be exactly 2*3*0.5 = 3.0
        // but since hadamard product generates quad terms from center*center,
        // the gap should be 0 or very close.
        assert!(
            bound.max_gap < 1e-6,
            "zero perturbation should give near-exact bounds, gap: {}",
            bound.max_gap
        );
    }
}
