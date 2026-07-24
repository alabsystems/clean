// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! CROWN Backward Bound Propagation -- Types, Concretization, and Proof Specs
//!
//! CROWN computes tighter bounds than IBP by propagating linear relaxations
//! backward through the network. For each output neuron, CROWN maintains
//! symbolic linear bounds of the form:
//!
//!   lower_bias + lower_coeffs * x  <=  f(x)  <=  upper_bias + upper_coeffs * x
//!
//! where x is the network input vector.
//!
//! ## Theorems (all `DerivedPending`, Phase 3)
//!
//! - **T40 (CROWN linear relaxation):** For a ReLU neuron with pre-activation
//!   bounds [l, u] where l < 0 < u, the tightest convex relaxation is the
//!   line from (l, 0) to (u, u) as the upper bound and zero as the lower.
//!
//! - **T41 (CROWN backward propagation):** The backward pass computes valid
//!   linear bounds by composing per-layer relaxations. Soundness requires
//!   that each layer's relaxation is a valid over/under-approximation.
//!
//! - **T42 (CROWN concave envelope):** The concave envelope of ReLU on [l, u]
//!   (l < 0 < u) has slope u/(u - l) and intercept -l*u/(u - l).
//!
//! ## Module Structure
//!
//! - This file: `CrownBound`, `CrownResult`, `crown_concretize`, proof specs.
//! - [`super::crown_backward`]: `crown_linear_backward`, `crown_relu_backward`,
//!   `verify_crown_bounds`.

use crate::spec::ProofStatus;

/// Backward linear bound: lower_bias + lower_coeffs * x <= f(x) <= upper_bias + upper_coeffs * x
///
/// Each row i of the coefficient matrices corresponds to one output neuron.
/// `lower_coeffs[i][j]` is the coefficient of input j in the lower bound for output i.
#[derive(Debug, Clone, PartialEq)]
pub struct CrownBound {
    /// Lower bound coefficients: matrix of shape (num_outputs x num_inputs).
    pub lower_coeffs: Vec<Vec<f64>>,
    /// Upper bound coefficients: matrix of shape (num_outputs x num_inputs).
    pub upper_coeffs: Vec<Vec<f64>>,
    /// Lower bound bias: vector of length num_outputs.
    pub lower_bias: Vec<f64>,
    /// Upper bound bias: vector of length num_outputs.
    pub upper_bias: Vec<f64>,
}

impl CrownBound {
    /// Create an identity bound for `dim` neurons: coefficients = I, bias = 0.
    ///
    /// This represents the trivial bound x <= f(x) <= x, used to initialize
    /// the backward pass at the output layer.
    #[must_use]
    pub fn identity(dim: usize) -> Self {
        let mut lower_coeffs = vec![vec![0.0; dim]; dim];
        let mut upper_coeffs = vec![vec![0.0; dim]; dim];
        for i in 0..dim {
            lower_coeffs[i][i] = 1.0;
            upper_coeffs[i][i] = 1.0;
        }
        Self {
            lower_coeffs,
            upper_coeffs,
            lower_bias: vec![0.0; dim],
            upper_bias: vec![0.0; dim],
        }
    }

    /// Number of output neurons tracked by this bound.
    #[must_use]
    pub fn num_outputs(&self) -> usize {
        self.lower_bias.len()
    }

    /// Number of input variables in the symbolic expression.
    #[must_use]
    pub fn num_inputs(&self) -> usize {
        if self.lower_coeffs.is_empty() {
            0
        } else {
            self.lower_coeffs[0].len()
        }
    }
}

/// Result of CROWN verification on a network.
#[derive(Debug, Clone, PartialEq)]
#[non_exhaustive]
pub struct CrownResult {
    /// Concrete lower bounds on each output neuron.
    pub lower: Vec<f64>,
    /// Concrete upper bounds on each output neuron.
    pub upper: Vec<f64>,
}

/// Concretize symbolic bounds using input intervals.
///
/// Given symbolic bound: lower_bias + lower_coeffs * x <= f(x) <= upper_bias + upper_coeffs * x,
/// and input x in [input_lower, input_upper], compute concrete scalar bounds.
///
/// For each output i:
///   concrete_lower[i] = lower_bias[i] + sum_j (pos(lower_coeffs[i][j]) * input_lower[j]
///                                              + neg(lower_coeffs[i][j]) * input_upper[j])
///   concrete_upper[i] = upper_bias[i] + sum_j (pos(upper_coeffs[i][j]) * input_upper[j]
///                                              + neg(upper_coeffs[i][j]) * input_lower[j])
///
/// This is the standard interval arithmetic concretization: positive coefficients
/// multiply the bound that extremizes the expression, negative coefficients multiply
/// the opposite bound.
#[must_use]
pub fn crown_concretize(
    bound: &CrownBound,
    input_lower: &[f64],
    input_upper: &[f64],
) -> (Vec<f64>, Vec<f64>) {
    let num_outputs = bound.num_outputs();
    let mut concrete_lower = Vec::with_capacity(num_outputs);
    let mut concrete_upper = Vec::with_capacity(num_outputs);

    for i in 0..num_outputs {
        let mut cl = bound.lower_bias[i];
        let mut cu = bound.upper_bias[i];

        for (j, (il, iu)) in input_lower.iter().zip(input_upper.iter()).enumerate() {
            let lc = bound.lower_coeffs[i][j];
            let uc = bound.upper_coeffs[i][j];

            // Lower bound: minimize lower_coeffs * x
            if lc >= 0.0 {
                cl += lc * il;
            } else {
                cl += lc * iu;
            }

            // Upper bound: maximize upper_coeffs * x
            if uc >= 0.0 {
                cu += uc * iu;
            } else {
                cu += uc * il;
            }
        }

        concrete_lower.push(cl);
        concrete_upper.push(cu);
    }

    (concrete_lower, concrete_upper)
}

// ---------------------------------------------------------------------------
// Proof spec types
// ---------------------------------------------------------------------------

/// T40: CROWN linear relaxation soundness.
///
/// **Statement:** For a ReLU neuron with pre-activation bounds [l, u]
/// where l < 0 < u, the triangle relaxation provides a sound convex
/// relaxation:
///   - Upper bound: lambda * x + mu, where lambda = u/(u-l), mu = -l*u/(u-l)
///   - Lower bound: 0 (conservative) or alpha * x for alpha in [0, 1]
///
/// **Proof:** Case analysis on x: when x <= 0, ReLU(x) = 0 <= lambda*x + mu;
/// when x >= 0, ReLU(x) = x <= lambda*x + mu by convexity.
///
/// **Status:** `DerivedPending` -- constructive proof in `crown_proofs.rs`.
#[derive(Debug)]
pub struct CrownLinearSpec {
    status: ProofStatus,
}

impl CrownLinearSpec {
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

    /// Compute the triangle relaxation parameters for a crossing ReLU neuron.
    ///
    /// Given pre-activation bounds [l, u] with l < 0 < u, returns (lambda, mu)
    /// where the upper relaxation is lambda * x + mu.
    ///
    /// Returns `None` if the neuron is not in the crossing case.
    #[must_use]
    pub fn triangle_params(l: f64, u: f64) -> Option<(f64, f64)> {
        if l >= 0.0 || u <= 0.0 {
            return None;
        }
        let lambda = u / (u - l);
        let mu = -l * u / (u - l);
        Some((lambda, mu))
    }

    /// Verify that the triangle relaxation is sound for a concrete value.
    ///
    /// For x in [l, u] with l < 0 < u:
    ///   - Upper: ReLU(x) <= lambda * x + mu
    ///   - Lower: 0 <= ReLU(x) (trivially true)
    pub fn verify_relaxation(&self, x: f64, l: f64, u: f64) -> Result<(), String> {
        if x < l - f64::EPSILON || x > u + f64::EPSILON {
            return Err(format!("x={x} not in [{l}, {u}]"));
        }
        let relu_x = x.max(0.0);

        // Lower bound: 0 <= ReLU(x)
        if relu_x < -f64::EPSILON {
            return Err(format!("ReLU({x})={relu_x} < 0 (lower bound violated)"));
        }

        // Upper bound for crossing case
        if l < 0.0 && u > 0.0 {
            let (lambda, mu) = Self::triangle_params(l, u)
                .expect("invariant: crossing case must produce triangle params");
            let upper_relax = lambda * x + mu;
            if relu_x > upper_relax + f64::EPSILON {
                return Err(format!(
                    "ReLU({x})={relu_x} > lambda*x+mu={upper_relax} (upper bound violated)"
                ));
            }
        }

        Ok(())
    }
}

impl Default for CrownLinearSpec {
    fn default() -> Self {
        Self::new()
    }
}

/// T41: CROWN backward bound propagation soundness.
///
/// **Statement:** The CROWN backward pass computes valid output bounds for a
/// multi-layer ReLU network. Starting from identity bounds at the output,
/// propagating backward through each layer's linear transform and ReLU
/// relaxation, then concretizing at the input, yields concrete bounds that
/// contain all achievable network outputs.
///
/// **Proof:** By induction on the number of layers. Base case: identity bound
/// trivially holds. Inductive step: if B_k is a sound bound on layers k+1..n
/// relative to the post-layer-k activation, then:
/// 1. `crown_relu_backward` applies a sound ReLU relaxation (by T40: triangle
///    for crossing, identity for active, zero for inactive).
/// 2. `crown_linear_backward` applies the exact linear transform (matrix
///    product and bias absorption, no approximation).
///    The composition of sound transformations is sound.
///
/// **Status:** `DerivedPending` -- verified via constructive proof in
/// `crown_proofs::verify_t41_backward_propagation` which checks corner points
/// and dense sampling. See `crown_proofs.rs`.
#[derive(Debug)]
pub struct CrownBackwardSpec {
    status: ProofStatus,
}

impl CrownBackwardSpec {
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

impl Default for CrownBackwardSpec {
    fn default() -> Self {
        Self::new()
    }
}

/// T42: CROWN concave envelope tightness.
///
/// **Statement:** The concave envelope of ReLU on [l, u] (l < 0 < u) is the
/// line from (l, 0) to (u, u) with slope u/(u-l) and intercept -l*u/(u-l).
/// This is the tightest concave upper bound on ReLU over the interval.
///
/// **Proof:** The line through (l, ReLU(l)) = (l, 0) and (u, ReLU(u)) = (u, u)
/// is linear (hence concave) and dominates ReLU on [l, u] (by convexity of
/// ReLU and the chord property). Any concave function g with g >= ReLU on [l, u]
/// satisfies g(l) >= 0 = line(l) and g(u) >= u = line(u). By concavity,
/// g(t*l + (1-t)*u) >= t*g(l) + (1-t)*g(u) >= t*line(l) + (1-t)*line(u) = line(...)
/// for all t in [0, 1]. Therefore the line is the tightest concave upper bound.
///
/// **Status:** `DerivedPending` -- verified via constructive proof in
/// `crown_proofs::verify_t42_concave_envelope` which checks endpoint conditions,
/// verifies the envelope dominates ReLU at dense samples, and computes the
/// maximum gap. See `crown_proofs.rs`.
#[derive(Debug)]
pub struct CrownConcaveSpec {
    status: ProofStatus,
}

impl CrownConcaveSpec {
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

impl Default for CrownConcaveSpec {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_crown_specs_are_derived_proved() {
        let linear = CrownLinearSpec::new();
        let backward = CrownBackwardSpec::new();
        let concave = CrownConcaveSpec::new();
        assert_eq!(linear.status(), ProofStatus::DerivedPending);
        assert_eq!(backward.status(), ProofStatus::DerivedPending);
        assert_eq!(concave.status(), ProofStatus::DerivedPending);
    }

    #[test]
    fn test_crown_linear_triangle_params_crossing() {
        // [l, u] = [-2, 4], crossing case
        let (lambda, mu) = CrownLinearSpec::triangle_params(-2.0, 4.0).unwrap();
        // lambda = 4/(4-(-2)) = 4/6 = 2/3
        assert!((lambda - 2.0 / 3.0).abs() < 1e-10);
        // mu = 2*4/6 = 8/6 = 4/3
        assert!((mu - 4.0 / 3.0).abs() < 1e-10);
    }

    #[test]
    fn test_crown_linear_triangle_params_not_crossing() {
        // Always active [1, 3]
        assert!(CrownLinearSpec::triangle_params(1.0, 3.0).is_none());
        // Always inactive [-3, -1]
        assert!(CrownLinearSpec::triangle_params(-3.0, -1.0).is_none());
    }

    #[test]
    fn test_crown_linear_relaxation_sound_at_endpoints() {
        let spec = CrownLinearSpec::new();
        // [-1, 1] crossing
        spec.verify_relaxation(-1.0, -1.0, 1.0)
            .expect("lower endpoint");
        spec.verify_relaxation(1.0, -1.0, 1.0)
            .expect("upper endpoint");
        spec.verify_relaxation(0.0, -1.0, 1.0).expect("zero");
    }

    #[test]
    fn test_crown_linear_relaxation_sound_random() {
        let spec = CrownLinearSpec::new();
        let l = -3.0;
        let u = 5.0;
        let mut rng: u64 = 42;
        let lcg = |state: &mut u64| -> f64 {
            *state = state
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1);
            (*state >> 33) as f64 / (1u64 << 31) as f64
        };
        for _ in 0..200 {
            let x = l + lcg(&mut rng) * (u - l);
            spec.verify_relaxation(x, l, u)
                .unwrap_or_else(|e| panic!("relaxation soundness failed at x={x}: {e}"));
        }
    }

    #[test]
    fn test_crown_linear_relaxation_always_active() {
        let spec = CrownLinearSpec::new();
        // [2, 5] always active -- no crossing, relaxation is just identity
        spec.verify_relaxation(3.0, 2.0, 5.0)
            .expect("always active");
    }

    #[test]
    fn test_crown_linear_relaxation_always_inactive() {
        let spec = CrownLinearSpec::new();
        // [-5, -2] always inactive -- ReLU is 0
        spec.verify_relaxation(-3.0, -5.0, -2.0)
            .expect("always inactive");
    }
}
