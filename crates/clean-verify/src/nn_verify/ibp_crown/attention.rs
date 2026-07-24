// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Attention Mechanism Bilinear Bound Propagation
//!
//! Transformer attention involves the bilinear product Q * K^T, which is
//! bounded via per-coordinate McCormick envelopes. This module computes
//! sound interval bounds on:
//!
//! 1. **Attention scores:** `q^T * k = sum_i q_i * k_i`, bounded by summing
//!    per-coordinate McCormick intervals.
//! 2. **Softmax outputs:** `softmax(z)_i = exp(z_i) / sum_j exp(z_j)`, bounded
//!    using monotonicity of `exp` and interval arithmetic on the denominator.
//! 3. **Full attention head:** `softmax(Q*K^T / sqrt(d_k)) * V`, composing
//!    bilinear QK bounds, softmax bounds, and a final bilinear softmax-V product.
//!
//! ## Theorems (all `DerivedPending`, Phase 3)
//!
//! - **T53 (Attention score bound soundness):** For q in [q_l, q_u] and
//!   k in [k_l, k_u], the computed score bounds contain the true dot product.
//! - **T54 (Softmax monotone bound):** Softmax bounds computed from score
//!   interval bounds are sound and each output coordinate is in [0, 1].

use crate::spec::ProofStatus;

use super::mccormick::mccormick_product_interval;

// ---------------------------------------------------------------------------
// AttentionScoreBounds: result of dot-product interval propagation
// ---------------------------------------------------------------------------

/// Bounds on a single attention score `q^T * k` where each coordinate
/// `q_i` in `[q_lower_i, q_upper_i]` and `k_i` in `[k_lower_i, k_upper_i]`.
///
/// The dot product `sum_i q_i * k_i` is bounded by summing per-coordinate
/// McCormick product intervals. This is sound because interval addition
/// preserves containment.
#[derive(Debug, Clone, PartialEq)]
#[non_exhaustive]
pub struct AttentionScoreBounds {
    /// Lower bound on the dot product score.
    pub lower: f64,
    /// Upper bound on the dot product score.
    pub upper: f64,
    /// Dimension of the dot product.
    pub dim: usize,
}

/// Bounds on a full attention head output.
#[derive(Debug, Clone, PartialEq)]
#[non_exhaustive]
pub struct AttentionBounds {
    /// Per-dimension lower bounds on the attention output.
    pub lower: Vec<f64>,
    /// Per-dimension upper bounds on the attention output.
    pub upper: Vec<f64>,
    /// Key dimension (used for scaling).
    pub d_k: usize,
}

// ---------------------------------------------------------------------------
// Core attention bound propagation functions
// ---------------------------------------------------------------------------

/// Compute bounds on the dot product `q^T * k = sum_i q_i * k_i`
/// using per-coordinate McCormick envelopes and interval addition.
///
/// Each coordinate product `q_i * k_i` is bounded via [`mccormick_product_interval`],
/// and the total dot product bounds are the sum of per-coordinate bounds.
/// This is sound because for intervals `[a_i, b_i]`:
///   `sum [a_i, b_i] = [sum a_i, sum b_i]`.
///
/// # Panics
///
/// Panics if the slices have different lengths or are empty.
#[must_use]
pub fn attention_score_bounds(
    q_lower: &[f64],
    q_upper: &[f64],
    k_lower: &[f64],
    k_upper: &[f64],
) -> (f64, f64) {
    assert_eq!(
        q_lower.len(),
        q_upper.len(),
        "q bounds must have equal length"
    );
    assert_eq!(
        k_lower.len(),
        k_upper.len(),
        "k bounds must have equal length"
    );
    assert_eq!(
        q_lower.len(),
        k_lower.len(),
        "q and k must have equal dimension"
    );
    assert!(!q_lower.is_empty(), "dimension must be positive");

    let mut total_lower = 0.0;
    let mut total_upper = 0.0;

    for i in 0..q_lower.len() {
        let (prod_lo, prod_hi) =
            mccormick_product_interval((q_lower[i], q_upper[i]), (k_lower[i], k_upper[i]));
        total_lower += prod_lo;
        total_upper += prod_hi;
    }

    (total_lower, total_upper)
}

/// Compute bounds on `softmax(scores)` using interval arithmetic.
///
/// For `softmax(z)_i = exp(z_i) / sum_j exp(z_j)`:
/// - Numerator `exp(z_i)` is bounded by `[exp(z_i_lower), exp(z_i_upper)]`
///   (monotonicity of exp).
/// - Denominator `sum_j exp(z_j)` is bounded by
///   `[sum_j exp(z_j_lower), sum_j exp(z_j_upper)]`.
/// - The fraction is bounded by `[exp(z_i_lower) / sum_upper, exp(z_i_upper) / sum_lower]`
///   where `sum_upper` excludes the i-th term's minimum and `sum_lower` excludes
///   its maximum to get the tightest bounds.
///
/// All outputs are guaranteed to be in `[0, 1]`.
///
/// # Panics
///
/// Panics if the slices have different lengths or are empty.
#[must_use]
pub fn softmax_bounds(score_lower: &[f64], score_upper: &[f64]) -> Vec<(f64, f64)> {
    assert_eq!(
        score_lower.len(),
        score_upper.len(),
        "score bounds must have equal length"
    );
    let n = score_lower.len();
    assert!(n > 0, "must have at least one score");

    // Precompute exp bounds for each coordinate.
    let exp_lower: Vec<f64> = score_lower.iter().map(|&s| s.exp()).collect();
    let exp_upper: Vec<f64> = score_upper.iter().map(|&s| s.exp()).collect();

    // Total sum bounds (used for denominator).
    let sum_exp_lower: f64 = exp_lower.iter().sum();
    let sum_exp_upper: f64 = exp_upper.iter().sum();

    let mut result = Vec::with_capacity(n);
    for i in 0..n {
        // For the lower bound of softmax_i:
        //   numerator is minimized: exp(z_i_lower)
        //   denominator is maximized: sum_j exp(z_j_upper) for j != i + exp(z_i_lower)
        //   = sum_exp_upper - exp_upper[i] + exp_lower[i]
        let denom_for_lower = sum_exp_upper - exp_upper[i] + exp_lower[i];

        // For the upper bound of softmax_i:
        //   numerator is maximized: exp(z_i_upper)
        //   denominator is minimized: sum_j exp(z_j_lower) for j != i + exp(z_i_upper)
        //   = sum_exp_lower - exp_lower[i] + exp_upper[i]
        let denom_for_upper = sum_exp_lower - exp_lower[i] + exp_upper[i];

        let lo = (exp_lower[i] / denom_for_lower).clamp(0.0, 1.0);
        let hi = (exp_upper[i] / denom_for_upper).clamp(0.0, 1.0);

        result.push((lo, hi));
    }

    result
}

/// Compute bounds on a full attention head output:
/// `output = softmax(q^T * k / sqrt(d_k)) * v`.
///
/// Composition pipeline:
/// 1. Compute dot product bounds `q^T * k` via per-coordinate McCormick envelopes.
/// 2. Scale by `1 / sqrt(d_k)`.
/// 3. Compute softmax bounds on the scaled scores.
/// 4. Compute output bounds as `softmax_bounds * v_bounds` via McCormick.
///
/// This models a single query attending to a single key-value pair.
/// For multi-head attention, call once per head.
///
/// # Panics
///
/// Panics if dimensions are inconsistent or `d_k` is zero.
#[must_use]
pub fn attention_head_bounds(
    q_lower: &[f64],
    q_upper: &[f64],
    k_lower: &[f64],
    k_upper: &[f64],
    v_lower: &[f64],
    v_upper: &[f64],
    d_k: usize,
) -> (Vec<f64>, Vec<f64>) {
    assert!(d_k > 0, "d_k must be positive");
    assert_eq!(q_lower.len(), q_upper.len());
    assert_eq!(k_lower.len(), k_upper.len());
    assert_eq!(v_lower.len(), v_upper.len());
    assert_eq!(
        q_lower.len(),
        k_lower.len(),
        "q and k must have same dimension"
    );

    let v_dim = v_lower.len();

    // Step 1: Dot product bounds q^T * k
    let (score_lo, score_hi) = attention_score_bounds(q_lower, q_upper, k_lower, k_upper);

    // Step 2: Scale by 1/sqrt(d_k)
    let scale = 1.0 / (d_k as f64).sqrt();
    let scaled_lo = score_lo * scale;
    let scaled_hi = score_hi * scale;

    // Step 3: Softmax bounds. For a single score, softmax is just sigmoid-like
    // (maps scalar to [0,1]). We model it as softmax over [score, 0] which gives
    // softmax = exp(score) / (exp(score) + 1) = sigmoid(score).
    // For soundness, we bound the attention weight in [0, 1].
    let attn_weight_lo = sigmoid_lower(scaled_lo);
    let attn_weight_hi = sigmoid_upper(scaled_hi);

    // Step 4: Output = attn_weight * v, bounded per-dimension via McCormick
    let mut out_lower = Vec::with_capacity(v_dim);
    let mut out_upper = Vec::with_capacity(v_dim);

    for i in 0..v_dim {
        let (prod_lo, prod_hi) =
            mccormick_product_interval((attn_weight_lo, attn_weight_hi), (v_lower[i], v_upper[i]));
        out_lower.push(prod_lo);
        out_upper.push(prod_hi);
    }

    (out_lower, out_upper)
}

/// Lower bound of sigmoid(x) for x in the lower end of the score interval.
/// sigmoid(x) = 1 / (1 + exp(-x)), which is monotonically increasing.
#[must_use]
fn sigmoid_lower(x: f64) -> f64 {
    sigmoid(x).clamp(0.0, 1.0)
}

/// Upper bound of sigmoid(x) for x in the upper end of the score interval.
#[must_use]
fn sigmoid_upper(x: f64) -> f64 {
    sigmoid(x).clamp(0.0, 1.0)
}

/// Standard sigmoid function.
#[must_use]
fn sigmoid(x: f64) -> f64 {
    if x >= 0.0 {
        let e = (-x).exp();
        1.0 / (1.0 + e)
    } else {
        let e = x.exp();
        e / (1.0 + e)
    }
}

/// Verify that an attention output falls within the computed bounds.
///
/// For concrete vectors `q`, `k`, `v`, computes the actual attention output
/// `sigmoid(q^T * k / sqrt(d_k)) * v` and checks containment in `bounds`.
#[must_use]
pub fn verify_attention_soundness(
    q: &[f64],
    k: &[f64],
    v: &[f64],
    bounds: &AttentionBounds,
) -> bool {
    assert_eq!(q.len(), k.len(), "q and k must have same dimension");
    assert_eq!(v.len(), bounds.lower.len(), "v dimension must match bounds");
    assert_eq!(v.len(), bounds.upper.len(), "v dimension must match bounds");

    let eps = f64::EPSILON * 64.0;

    // Compute actual attention output
    let dot: f64 = q.iter().zip(k.iter()).map(|(qi, ki)| qi * ki).sum();
    let scale = 1.0 / (bounds.d_k as f64).sqrt();
    let attn_weight = sigmoid(dot * scale);

    for (i, &vi) in v.iter().enumerate() {
        let output_i = attn_weight * vi;
        if output_i < bounds.lower[i] - eps || output_i > bounds.upper[i] + eps {
            return false;
        }
    }

    true
}

// ---------------------------------------------------------------------------
// Proof spec stubs (Phase 3 theorem tracking)
// ---------------------------------------------------------------------------

/// Proof specification for T53: Attention score bound soundness.
///
/// Tracks the formal proof that per-coordinate McCormick envelope summation
/// produces sound bounds on the dot product `q^T * k`.
#[derive(Debug)]
pub struct AttentionScoreBoundSpec {
    status: ProofStatus,
}

impl AttentionScoreBoundSpec {
    #[must_use]
    pub fn new() -> Self {
        Self {
            status: ProofStatus::DerivedPending,
        }
    }

    #[must_use]
    pub fn status(&self) -> ProofStatus {
        self.status
    }
}

impl Default for AttentionScoreBoundSpec {
    fn default() -> Self {
        Self::new()
    }
}

/// Proof specification for T54: Softmax monotone bound soundness.
///
/// Tracks the formal proof that softmax bounds computed from score interval
/// bounds are sound and each output coordinate is in [0, 1].
#[derive(Debug)]
pub struct SoftmaxMonotoneBoundSpec {
    status: ProofStatus,
}

impl SoftmaxMonotoneBoundSpec {
    #[must_use]
    pub fn new() -> Self {
        Self {
            status: ProofStatus::DerivedPending,
        }
    }

    #[must_use]
    pub fn status(&self) -> ProofStatus {
        self.status
    }
}

impl Default for SoftmaxMonotoneBoundSpec {
    fn default() -> Self {
        Self::new()
    }
}

// ---------------------------------------------------------------------------
// Attention theorems for the registry
// ---------------------------------------------------------------------------

/// Phase 3 Attention theorems (T53-T54).
#[must_use]
pub(crate) fn attention_theorems() -> Vec<super::TheoremEntry> {
    use super::{Phase, TheoremEntry};

    vec![
        TheoremEntry {
            id: "T53",
            description: "Attention score bound soundness (McCormick dot product)",
            status: ProofStatus::DerivedPending,
            phase: Phase::Phase3,
        },
        TheoremEntry {
            id: "T54",
            description: "Softmax monotone bound soundness",
            status: ProofStatus::DerivedPending,
            phase: Phase::Phase3,
        },
    ]
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_attention_specs_exist_as_derived_pending() {
        let score_spec = AttentionScoreBoundSpec::new();
        let softmax_spec = SoftmaxMonotoneBoundSpec::new();
        assert_eq!(score_spec.status(), ProofStatus::DerivedPending);
        assert_eq!(softmax_spec.status(), ProofStatus::DerivedPending);
    }

    #[test]
    fn test_attention_theorems_count() {
        let theorems = attention_theorems();
        assert_eq!(theorems.len(), 2);
        assert_eq!(theorems[0].id, "T53");
        assert_eq!(theorems[1].id, "T54");
    }

    #[test]
    fn test_sigmoid_basic() {
        assert!((sigmoid(0.0) - 0.5).abs() < 1e-10);
        assert!(sigmoid(100.0) > 0.999);
        assert!(sigmoid(-100.0) < 0.001);
    }
}
