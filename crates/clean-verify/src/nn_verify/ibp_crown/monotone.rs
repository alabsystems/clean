// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Monotone Activation Function Bound Propagation
//!
//! IBP for monotone activations (sigmoid, tanh, GELU, softplus) shares a
//! common pattern: if f is monotone increasing, then f([l, u]) = [f(l), f(u)].
//!
//! This module provides a unified framework for classifying activation
//! functions by monotonicity and propagating interval bounds through them.
//! It also computes interval-restricted Lipschitz constants for tightness
//! analysis.
//!
//! ## Theorems (all `DerivedPending`)
//!
//! - **T83 (Sigmoid monotone bound):** sigmoid is monotone increasing,
//!   so sigmoid([l, u]) = [sigmoid(l), sigmoid(u)].
//! - **T85 (Tanh monotone bound):** tanh is monotone increasing,
//!   so tanh([l, u]) = [tanh(l), tanh(u)].
//! - **T86 (GELU approx bound):** The GELU approximation is monotone
//!   increasing for all x, so GELU([l, u]) = [GELU(l), GELU(u)].
//! - **T87 (Activation Lipschitz):** Lipschitz constants for monotone
//!   activations on restricted intervals.

use crate::spec::ProofStatus;

/// Classification of activation functions by monotonicity.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum MonotoneClass {
    /// Monotone increasing (sigmoid, tanh, softplus).
    Increasing,
    /// Monotone decreasing (e.g. 1 - sigmoid).
    Decreasing,
    /// Piecewise monotone (ReLU, leaky ReLU, ELU, GELU approx).
    /// GELU approximation has a local minimum near x ~ -0.75.
    PiecewiseMonotone,
}

/// Concrete monotone activation functions for bound propagation.
///
/// Float parameters are stored as `u64` via `f64::to_bits()` so that the
/// enum can derive `Eq` and `Hash`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum ActivationFn {
    /// Standard sigmoid: 1 / (1 + exp(-x)).
    Sigmoid,
    /// Hyperbolic tangent.
    Tanh,
    /// Softplus: ln(1 + exp(x)).
    Softplus,
    /// GELU approximation: 0.5 * x * (1 + tanh(sqrt(2/pi) * (x + 0.044715 * x^3))).
    GeluApprox,
    /// Leaky ReLU: max(alpha*x, x). Alpha stored as f64 bits.
    LeakyRelu(u64),
    /// ELU: x if x >= 0, alpha*(exp(x)-1) if x < 0. Alpha stored as f64 bits.
    Elu(u64),
}

/// Constant: sqrt(2/pi) used in GELU approximation.
const SQRT_2_OVER_PI: f64 = 0.7978845608028654;

/// Constant: coefficient in GELU approximation.
const GELU_COEFF: f64 = 0.044715;

impl ActivationFn {
    /// Create a `LeakyRelu` with the given alpha slope for negative inputs.
    #[must_use]
    pub fn leaky_relu(alpha: f64) -> Self {
        Self::LeakyRelu(alpha.to_bits())
    }

    /// Create an `Elu` with the given alpha.
    #[must_use]
    pub fn elu(alpha: f64) -> Self {
        Self::Elu(alpha.to_bits())
    }

    /// Evaluate the activation function at a single point.
    #[must_use]
    pub fn evaluate(&self, x: f64) -> f64 {
        match self {
            Self::Sigmoid => 1.0 / (1.0 + (-x).exp()),
            Self::Tanh => x.tanh(),
            Self::Softplus => {
                // Numerically stable: for large x, softplus(x) ~ x
                if x > 20.0 {
                    x
                } else if x < -20.0 {
                    x.exp()
                } else {
                    (1.0 + x.exp()).ln()
                }
            }
            Self::GeluApprox => {
                let inner = SQRT_2_OVER_PI * (x + GELU_COEFF * x * x * x);
                0.5 * x * (1.0 + inner.tanh())
            }
            Self::LeakyRelu(alpha_bits) => {
                let alpha = f64::from_bits(*alpha_bits);
                if x >= 0.0 {
                    x
                } else {
                    alpha * x
                }
            }
            Self::Elu(alpha_bits) => {
                let alpha = f64::from_bits(*alpha_bits);
                if x >= 0.0 {
                    x
                } else {
                    alpha * (x.exp() - 1.0)
                }
            }
        }
    }

    /// Return the monotonicity classification for this activation function.
    #[must_use]
    pub fn monotone_class(&self) -> MonotoneClass {
        match self {
            Self::Sigmoid | Self::Tanh | Self::Softplus => MonotoneClass::Increasing,
            // GELU approximation has a local minimum near x ~ -0.75 where the
            // derivative goes negative. It is NOT globally monotone.
            Self::GeluApprox | Self::LeakyRelu(_) | Self::Elu(_) => {
                MonotoneClass::PiecewiseMonotone
            }
        }
    }

    /// Compute bounds on f(x) for x in [lower, upper].
    ///
    /// - Monotone increasing: `[f(lower), f(upper)]`
    /// - Monotone decreasing: `[f(upper), f(lower)]`
    /// - Piecewise monotone: case-split at breakpoints or dense sampling
    #[must_use]
    pub fn propagate_bounds(&self, lower: f64, upper: f64) -> (f64, f64) {
        debug_assert!(
            lower <= upper,
            "lower must not exceed upper: {lower} > {upper}"
        );
        match self.monotone_class() {
            MonotoneClass::Increasing => (self.evaluate(lower), self.evaluate(upper)),
            MonotoneClass::Decreasing => (self.evaluate(upper), self.evaluate(lower)),
            MonotoneClass::PiecewiseMonotone => self.propagate_piecewise(lower, upper),
        }
    }

    /// Piecewise propagation for non-monotone activations.
    ///
    /// LeakyReLU/ELU have a breakpoint at x = 0.
    /// GELU approximation has a local minimum near x ~ -0.75.
    fn propagate_piecewise(&self, lower: f64, upper: f64) -> (f64, f64) {
        match self {
            Self::GeluApprox => {
                // GELU has a local minimum near x ~ -0.752. For sound bounds,
                // sample densely and take min/max over the interval.
                propagate_by_sampling(self, lower, upper)
            }
            Self::LeakyRelu(alpha_bits) => {
                let alpha = f64::from_bits(*alpha_bits);
                if alpha >= 0.0 {
                    // Both pieces are non-decreasing => overall monotone
                    (self.evaluate(lower), self.evaluate(upper))
                } else {
                    // Negative alpha: negative piece is decreasing.
                    if upper <= 0.0 {
                        (self.evaluate(upper), self.evaluate(lower))
                    } else if lower >= 0.0 {
                        (self.evaluate(lower), self.evaluate(upper))
                    } else {
                        let f_lower = self.evaluate(lower);
                        let f_upper = self.evaluate(upper);
                        let f_zero: f64 = 0.0;
                        (f_zero.min(f_lower).min(f_upper), f_lower.max(f_upper))
                    }
                }
            }
            Self::Elu(alpha_bits) => {
                let alpha = f64::from_bits(*alpha_bits);
                if alpha >= 0.0 {
                    // ELU with positive alpha: both pieces non-decreasing
                    (self.evaluate(lower), self.evaluate(upper))
                } else {
                    if upper <= 0.0 {
                        (self.evaluate(upper), self.evaluate(lower))
                    } else if lower >= 0.0 {
                        (self.evaluate(lower), self.evaluate(upper))
                    } else {
                        let f_lower = self.evaluate(lower);
                        let f_upper = self.evaluate(upper);
                        let f_zero: f64 = 0.0;
                        (f_zero.min(f_lower).min(f_upper), f_lower.max(f_upper))
                    }
                }
            }
            // Monotone cases handled by propagate_bounds directly
            _ => (self.evaluate(lower), self.evaluate(upper)),
        }
    }
}

/// Propagate bounds by dense sampling. Used for non-monotone activations
/// (GELU) where analytic breakpoint analysis is complex.
///
/// Samples 1000 points plus endpoints and returns conservative [min, max].
/// The small epsilon padding ensures soundness for values between sample points.
fn propagate_by_sampling(activation: &ActivationFn, lower: f64, upper: f64) -> (f64, f64) {
    let n = 1000;
    let f_lower = activation.evaluate(lower);
    let f_upper = activation.evaluate(upper);
    let mut min_val = f_lower.min(f_upper);
    let mut max_val = f_lower.max(f_upper);

    for i in 1..n {
        let t = i as f64 / n as f64;
        let x = lower + t * (upper - lower);
        let fx = activation.evaluate(x);
        if fx < min_val {
            min_val = fx;
        }
        if fx > max_val {
            max_val = fx;
        }
    }

    // Add small padding for values between sample points.
    // The Lipschitz constant bounds the max change between samples.
    let step = (upper - lower) / n as f64;
    // Conservative: GELU derivative magnitude is bounded by ~1.1 globally,
    // so the max change between adjacent samples is ~1.1 * step.
    let pad = 1.2 * step;
    (min_val - pad, max_val + pad)
}

/// Verify that activation bound propagation is sound:
/// for x in [lower, upper], f(x) is in propagate_bounds(lower, upper).
#[must_use]
pub fn verify_activation_soundness(
    activation: ActivationFn,
    x: f64,
    lower: f64,
    upper: f64,
) -> bool {
    if x < lower - f64::EPSILON || x > upper + f64::EPSILON {
        return false;
    }
    let (bound_lo, bound_hi) = activation.propagate_bounds(lower, upper);
    let fx = activation.evaluate(x);
    fx >= bound_lo - f64::EPSILON && fx <= bound_hi + f64::EPSILON
}

/// Compute Lipschitz constant of an activation on [lower, upper].
///
/// The Lipschitz constant L satisfies |f(x) - f(y)| <= L * |x - y| for
/// all x, y in the interval. For differentiable functions, L = max |f'(x)|
/// on the interval.
///
/// Specific bounds:
/// - Sigmoid: max derivative is sigmoid(x)*(1-sigmoid(x)), peaked at x=0
///   where sigmoid'(0) = 0.25. Globally L <= 0.25.
/// - Tanh: max derivative is 1 - tanh^2(x), peaked at x=0 where tanh'(0) = 1.
///   Globally L <= 1.0.
/// - Softplus: derivative is sigmoid(x), so L <= 1.0.
/// - GELU: derivative is bounded; empirically L <= ~1.13 but on most intervals < 1.5.
/// - LeakyReLU: L = max(1, |alpha|).
/// - ELU: L = max(1, |alpha|) (since ELU'(x) = alpha*exp(x) for x<0, bounded by alpha at x=0).
#[must_use]
pub fn activation_lipschitz(activation: ActivationFn, lower: f64, upper: f64) -> f64 {
    debug_assert!(lower <= upper, "lower must not exceed upper");

    match activation {
        ActivationFn::Sigmoid => {
            // sigmoid'(x) = sigmoid(x) * (1 - sigmoid(x))
            // Maximum at x = 0 where sigmoid'(0) = 0.25
            // On a restricted interval, sample to find max
            sigmoid_derivative_max(lower, upper)
        }
        ActivationFn::Tanh => {
            // tanh'(x) = 1 - tanh(x)^2 = sech^2(x)
            // Maximum at x = 0 where tanh'(0) = 1.0
            tanh_derivative_max(lower, upper)
        }
        ActivationFn::Softplus => {
            // softplus'(x) = sigmoid(x), which is monotone increasing.
            // Max on [lower, upper] is sigmoid(upper).
            let s = 1.0 / (1.0 + (-upper).exp());
            s.max(1.0 / (1.0 + (-lower).exp()))
        }
        ActivationFn::GeluApprox => {
            // GELU derivative is complex; sample the interval to estimate max.
            gelu_derivative_max(lower, upper)
        }
        ActivationFn::LeakyRelu(alpha_bits) => {
            let alpha = f64::from_bits(alpha_bits);
            // Slope is 1 for x >= 0, alpha for x < 0
            if lower >= 0.0 {
                1.0
            } else if upper <= 0.0 {
                alpha.abs()
            } else {
                1.0_f64.max(alpha.abs())
            }
        }
        ActivationFn::Elu(alpha_bits) => {
            let alpha = f64::from_bits(alpha_bits);
            // ELU'(x) = 1 for x >= 0, alpha*exp(x) for x < 0
            // |alpha*exp(x)| is maximized at x=0 where it equals |alpha|
            if lower >= 0.0 {
                1.0
            } else if upper <= 0.0 {
                // alpha*exp(x) on [lower, upper<=0], max at x=upper
                (alpha * upper.exp()).abs()
            } else {
                1.0_f64.max(alpha.abs())
            }
        }
    }
}

/// Find max of sigmoid'(x) = sigmoid(x)*(1-sigmoid(x)) on [lower, upper].
fn sigmoid_derivative_max(lower: f64, upper: f64) -> f64 {
    // sigmoid' is a bell curve peaked at x=0 with value 0.25.
    // If interval contains 0, max is 0.25. Otherwise, max is at the endpoint
    // closest to 0.
    if lower <= 0.0 && upper >= 0.0 {
        return 0.25;
    }
    let s_lo = 1.0 / (1.0 + (-lower).exp());
    let s_hi = 1.0 / (1.0 + (-upper).exp());
    let d_lo = s_lo * (1.0 - s_lo);
    let d_hi = s_hi * (1.0 - s_hi);
    d_lo.max(d_hi)
}

/// Find max of tanh'(x) = 1 - tanh(x)^2 on [lower, upper].
fn tanh_derivative_max(lower: f64, upper: f64) -> f64 {
    // tanh' is peaked at x=0 with value 1.0.
    if lower <= 0.0 && upper >= 0.0 {
        return 1.0;
    }
    let t_lo = lower.tanh();
    let t_hi = upper.tanh();
    let d_lo = 1.0 - t_lo * t_lo;
    let d_hi = 1.0 - t_hi * t_hi;
    d_lo.max(d_hi)
}

/// Estimate max of GELU'(x) on [lower, upper] by sampling.
fn gelu_derivative_max(lower: f64, upper: f64) -> f64 {
    // GELU'(x) = 0.5 * (1 + tanh(z)) + 0.5 * x * sech^2(z) * z'
    // where z = sqrt(2/pi) * (x + 0.044715 * x^3)
    // and z' = sqrt(2/pi) * (1 + 3*0.044715 * x^2)
    //
    // Sample at 200 points + endpoints for a reliable estimate.
    let n = 200;
    let mut max_deriv = f64::NEG_INFINITY;
    for i in 0..=n {
        let t = i as f64 / n as f64;
        let x = lower + t * (upper - lower);
        let d = gelu_derivative(x);
        if d > max_deriv {
            max_deriv = d;
        }
    }
    max_deriv
}

/// GELU approximation derivative at a point.
fn gelu_derivative(x: f64) -> f64 {
    let z = SQRT_2_OVER_PI * (x + GELU_COEFF * x * x * x);
    let tanh_z = z.tanh();
    let sech2_z = 1.0 - tanh_z * tanh_z;
    let z_prime = SQRT_2_OVER_PI * (1.0 + 3.0 * GELU_COEFF * x * x);
    0.5 * (1.0 + tanh_z) + 0.5 * x * sech2_z * z_prime
}

// ---------------------------------------------------------------------------
// Proof status tracking
// ---------------------------------------------------------------------------

/// T83: Sigmoid monotone bound soundness.
///
/// **Status:** `DerivedPending` -- kernel theorem `NNVerify.sigmoid_monotone_bound`
/// registered as `Declaration::Theorem`. The proof uses the strict positivity
/// of sigmoid'(x) = sigmoid(x)*(1-sigmoid(x)) > 0 for all x, establishing
/// global monotonicity. From `monotone_preserve_bounds`, l <= x <= u implies
/// sigma(l) <= sigma(x) <= sigma(u). Axiom-free constructive proof.
/// See `nn_verify_monotone_activation.rs` in clean-kernel.
pub const T83_SIGMOID_MONOTONE_BOUND: ProofStatus = ProofStatus::DerivedPending;

/// T85: Tanh monotone bound soundness.
///
/// **Status:** `DerivedPending` -- kernel theorem `NNVerify.tanh_monotone_bound`
/// registered as `Declaration::Theorem`. The proof uses tanh'(x) = 1 - tanh^2(x)
/// = sech^2(x) > 0 for all x, establishing global monotonicity. From
/// `monotone_preserve_bounds`, l <= x <= u implies tanh(l) <= tanh(x) <= tanh(u).
/// See `nn_verify_monotone_activation.rs` in clean-kernel.
pub const T85_TANH_MONOTONE_BOUND: ProofStatus = ProofStatus::DerivedPending;

/// T86: GELU approximation bound soundness.
pub const T86_GELU_APPROX_BOUND: ProofStatus = ProofStatus::DerivedPending;

/// T87: Activation Lipschitz constant bound.
pub const T87_ACTIVATION_LIPSCHITZ: ProofStatus = ProofStatus::DerivedPending;

// ---------------------------------------------------------------------------
// Concrete verification helpers for proved theorems
// ---------------------------------------------------------------------------

/// Verify T83 (sigmoid monotone bound) for a concrete value x in [lower, upper].
///
/// Checks that sigmoid(x) lies within [sigmoid(lower), sigmoid(upper)].
/// This is a direct consequence of sigmoid being monotone increasing.
pub fn verify_sigmoid_monotone_bound(x: f64, lower: f64, upper: f64) -> Result<(), String> {
    if x < lower - f64::EPSILON || x > upper + f64::EPSILON {
        return Err(format!("x={x} not in [{lower}, {upper}]"));
    }
    let sig = ActivationFn::Sigmoid;
    let fx = sig.evaluate(x);
    let f_lower = sig.evaluate(lower);
    let f_upper = sig.evaluate(upper);
    if fx < f_lower - f64::EPSILON || fx > f_upper + f64::EPSILON {
        return Err(format!(
            "sigmoid({x})={fx} not in [sigmoid({lower})={f_lower}, sigmoid({upper})={f_upper}]"
        ));
    }
    Ok(())
}

/// Verify T85 (tanh monotone bound) for a concrete value x in [lower, upper].
///
/// Checks that tanh(x) lies within [tanh(lower), tanh(upper)].
/// This is a direct consequence of tanh being monotone increasing.
pub fn verify_tanh_monotone_bound(x: f64, lower: f64, upper: f64) -> Result<(), String> {
    if x < lower - f64::EPSILON || x > upper + f64::EPSILON {
        return Err(format!("x={x} not in [{lower}, {upper}]"));
    }
    let tanh_fn = ActivationFn::Tanh;
    let fx = tanh_fn.evaluate(x);
    let f_lower = tanh_fn.evaluate(lower);
    let f_upper = tanh_fn.evaluate(upper);
    if fx < f_lower - f64::EPSILON || fx > f_upper + f64::EPSILON {
        return Err(format!(
            "tanh({x})={fx} not in [tanh({lower})={f_lower}, tanh({upper})={f_upper}]"
        ));
    }
    Ok(())
}
