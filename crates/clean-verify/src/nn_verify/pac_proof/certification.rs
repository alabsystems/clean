// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Core PAC-to-Proof certification logic.
//!
//! Provides Lipschitz bounds, Hessian bounds, and certified region computation
//! around PGD-found adversarial examples. The certifier produces a
//! [`CertifiedRegion`] proving that no better adversarial exists within a ball
//! of computed radius.

/// Error type for PAC-to-Proof certification operations.
#[derive(Debug, Clone, PartialEq, thiserror::Error)]
#[non_exhaustive]
pub enum CertificationError {
    /// Lipschitz constant must be strictly positive.
    #[error("Lipschitz constant must be positive, got {0}")]
    NonPositiveLipschitz(f64),

    /// Hessian bound must be non-negative.
    #[error("Hessian bound must be non-negative, got {0}")]
    NegativeHessian(f64),

    /// The adversarial output is already below the threshold, so no
    /// certification region can be established (PGD did not find a
    /// counterexample above threshold).
    #[error("adversarial output {output} is below threshold {threshold}")]
    OutputBelowThreshold { output: f64, threshold: f64 },

    /// Gradient norm must be non-negative.
    #[error("gradient norm must be non-negative, got {0}")]
    NegativeGradientNorm(f64),

    /// The quadratic discriminant is negative, meaning the Hessian-based
    /// certification cannot establish a positive radius. This occurs when the
    /// gradient is too steep relative to the margin and Hessian bound.
    #[error("negative discriminant in quadratic refinement: {0}")]
    NegativeDiscriminant(f64),

    /// A NaN or infinity was encountered in the computation.
    #[error("non-finite value encountered: {context}")]
    NonFinite { context: String },
}

/// Lipschitz bound on a network: ||f(x) - f(y)|| <= L * ||x - y||.
///
/// The Lipschitz constant L is an upper bound on the network's maximum rate
/// of change. Smaller L means the network is smoother and certification
/// radii are larger.
///
/// Typically computed via spectral norm product (see
/// [`crate::nn_verify::ibp_crown::lipschitz_concrete::compute_network_lipschitz`]).
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct LipschitzBound {
    /// The Lipschitz constant L > 0.
    constant: f64,
}

impl LipschitzBound {
    /// Create a new Lipschitz bound.
    ///
    /// # Errors
    ///
    /// Returns [`CertificationError::NonPositiveLipschitz`] if `constant <= 0`
    /// or is non-finite.
    pub fn new(constant: f64) -> Result<Self, CertificationError> {
        if !constant.is_finite() || constant <= 0.0 {
            return Err(CertificationError::NonPositiveLipschitz(constant));
        }
        Ok(Self { constant })
    }

    /// Returns the Lipschitz constant.
    #[must_use]
    pub fn constant(&self) -> f64 {
        self.constant
    }
}

/// Hessian bound on a network: ||nabla^2 f(x)|| <= H for all x.
///
/// The Hessian bound H controls the curvature of the network's output.
/// It enables second-order (quadratic) refinement of the certification
/// radius, which is tighter than the first-order Lipschitz-only bound
/// when the gradient at the adversarial example is small.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct HessianBound {
    /// The Hessian bound H >= 0.
    bound: f64,
}

impl HessianBound {
    /// Create a new Hessian bound.
    ///
    /// # Errors
    ///
    /// Returns [`CertificationError::NegativeHessian`] if `bound < 0`
    /// or is non-finite.
    pub fn new(bound: f64) -> Result<Self, CertificationError> {
        if !bound.is_finite() || bound < 0.0 {
            return Err(CertificationError::NegativeHessian(bound));
        }
        Ok(Self { bound })
    }

    /// Returns the Hessian bound.
    #[must_use]
    pub fn bound(&self) -> f64 {
        self.bound
    }
}

/// Certification mode: first-order (Lipschitz only) or second-order
/// (Lipschitz + Hessian).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum CertificationMode {
    /// First-order: r = (f(x_adv) - threshold) / L.
    FirstOrder,
    /// Second-order: quadratic refinement using Hessian bound.
    SecondOrder,
}

/// A certified region around an adversarial example.
///
/// Proves that within B(x_adv, radius), no point can reduce the network
/// output below the certification threshold. Equivalently, x_adv is a
/// local optimum (up to the certified radius) for the adversarial objective.
#[derive(Debug, Clone, PartialEq)]
pub struct CertifiedRegion {
    /// The certification radius. All points within this distance of x_adv
    /// have network output >= threshold.
    radius: f64,
    /// The Lipschitz constant used for certification.
    lipschitz: f64,
    /// The Hessian bound used (if second-order).
    hessian: Option<f64>,
    /// The network output at x_adv.
    adversarial_output: f64,
    /// The threshold that the adversarial output exceeds.
    threshold: f64,
    /// The gradient norm at x_adv (if second-order).
    gradient_norm: Option<f64>,
    /// Which certification mode produced this region.
    mode: CertificationMode,
}

impl CertifiedRegion {
    /// Returns the certification radius.
    #[must_use]
    pub fn radius(&self) -> f64 {
        self.radius
    }

    /// Returns the Lipschitz constant used.
    #[must_use]
    pub fn lipschitz(&self) -> f64 {
        self.lipschitz
    }

    /// Returns the Hessian bound (if second-order).
    #[must_use]
    pub fn hessian(&self) -> Option<f64> {
        self.hessian
    }

    /// Returns the network output at the adversarial example.
    #[must_use]
    pub fn adversarial_output(&self) -> f64 {
        self.adversarial_output
    }

    /// Returns the certification threshold.
    #[must_use]
    pub fn threshold(&self) -> f64 {
        self.threshold
    }

    /// Returns the gradient norm at x_adv (if second-order).
    #[must_use]
    pub fn gradient_norm(&self) -> Option<f64> {
        self.gradient_norm
    }

    /// Returns the certification mode that produced this region.
    #[must_use]
    pub fn mode(&self) -> CertificationMode {
        self.mode
    }

    /// The margin: f(x_adv) - threshold. Always positive for valid regions.
    #[must_use]
    pub fn margin(&self) -> f64 {
        self.adversarial_output - self.threshold
    }
}

/// Certifier that produces certified regions from PGD results.
///
/// Encapsulates Lipschitz and optional Hessian bounds for reuse across
/// multiple adversarial examples.
#[derive(Debug, Clone)]
pub struct PacProofCertifier {
    lipschitz: LipschitzBound,
    hessian: Option<HessianBound>,
}

impl PacProofCertifier {
    /// Create a first-order certifier (Lipschitz only).
    #[must_use]
    pub fn first_order(lipschitz: LipschitzBound) -> Self {
        Self {
            lipschitz,
            hessian: None,
        }
    }

    /// Create a second-order certifier (Lipschitz + Hessian).
    #[must_use]
    pub fn second_order(lipschitz: LipschitzBound, hessian: HessianBound) -> Self {
        Self {
            lipschitz,
            hessian: Some(hessian),
        }
    }

    /// Certify a PGD result.
    ///
    /// Given the network output at x_adv and a threshold, compute the
    /// certified radius using the best available method (second-order
    /// if Hessian bound is available, otherwise first-order).
    ///
    /// # Parameters
    ///
    /// - `adversarial_output`: f(x_adv), the network's output at the
    ///   PGD-found adversarial example.
    /// - `threshold`: The robustness threshold. The adversarial must satisfy
    ///   f(x_adv) > threshold.
    /// - `gradient_norm`: ||nabla f(x_adv)||. Required for second-order
    ///   certification; ignored for first-order.
    ///
    /// # Errors
    ///
    /// Returns an error if the adversarial output is below threshold, or if
    /// the computation produces non-finite values.
    pub fn certify(
        &self,
        adversarial_output: f64,
        threshold: f64,
        gradient_norm: Option<f64>,
    ) -> Result<CertifiedRegion, CertificationError> {
        // Validate output > threshold.
        if adversarial_output <= threshold {
            return Err(CertificationError::OutputBelowThreshold {
                output: adversarial_output,
                threshold,
            });
        }

        let margin = adversarial_output - threshold;

        match (self.hessian, gradient_norm) {
            (Some(hessian), Some(grad_norm)) if hessian.bound() > 0.0 => {
                // Second-order quadratic refinement.
                self.certify_second_order(adversarial_output, threshold, margin, grad_norm, hessian)
            }
            _ => {
                // First-order Lipschitz certification.
                self.certify_first_order(adversarial_output, threshold, margin)
            }
        }
    }

    /// First-order certification: r = margin / L.
    fn certify_first_order(
        &self,
        adversarial_output: f64,
        threshold: f64,
        margin: f64,
    ) -> Result<CertifiedRegion, CertificationError> {
        let radius = margin / self.lipschitz.constant();

        if !radius.is_finite() {
            return Err(CertificationError::NonFinite {
                context: format!(
                    "first-order radius: margin={margin}, L={}",
                    self.lipschitz.constant()
                ),
            });
        }

        Ok(CertifiedRegion {
            radius,
            lipschitz: self.lipschitz.constant(),
            hessian: None,
            adversarial_output,
            threshold,
            gradient_norm: None,
            mode: CertificationMode::FirstOrder,
        })
    }

    /// Second-order certification using Hessian bound.
    ///
    /// By Taylor's theorem with Hessian bound H:
    ///   f(x) >= f(x_adv) - ||grad f(x_adv)|| * r - (H/2) * r^2
    ///
    /// Setting f(x) >= threshold and solving for r:
    ///   (H/2) * r^2 + ||grad|| * r - margin <= 0
    ///
    /// Positive root: r = (-||grad|| + sqrt(||grad||^2 + 2*H*margin)) / H
    fn certify_second_order(
        &self,
        adversarial_output: f64,
        threshold: f64,
        margin: f64,
        grad_norm: f64,
        hessian: HessianBound,
    ) -> Result<CertifiedRegion, CertificationError> {
        if grad_norm < 0.0 {
            return Err(CertificationError::NegativeGradientNorm(grad_norm));
        }

        let h = hessian.bound();
        let discriminant = grad_norm * grad_norm + 2.0 * h * margin;

        if discriminant < 0.0 {
            return Err(CertificationError::NegativeDiscriminant(discriminant));
        }

        let radius = (-grad_norm + discriminant.sqrt()) / h;

        if !radius.is_finite() || radius < 0.0 {
            return Err(CertificationError::NonFinite {
                context: format!(
                    "second-order radius: grad_norm={grad_norm}, H={h}, margin={margin}"
                ),
            });
        }

        // Also compute first-order radius; take the maximum of the two
        // since second-order can be tighter or looser depending on gradient.
        let first_order_radius = margin / self.lipschitz.constant();

        // The second-order radius is valid independently of the Lipschitz
        // bound. We take the better (larger) of the two certified radii.
        let best_radius = if first_order_radius.is_finite() {
            radius.max(first_order_radius)
        } else {
            radius
        };

        let mode = if (best_radius - radius).abs() < f64::EPSILON {
            CertificationMode::SecondOrder
        } else {
            CertificationMode::FirstOrder
        };

        Ok(CertifiedRegion {
            radius: best_radius,
            lipschitz: self.lipschitz.constant(),
            hessian: Some(h),
            adversarial_output,
            threshold,
            gradient_norm: Some(grad_norm),
            mode,
        })
    }
}

// ---------------------------------------------------------------------------
// Convenience functions
// ---------------------------------------------------------------------------

/// Certify a PGD result using first-order Lipschitz bounds.
///
/// Convenience wrapper around [`PacProofCertifier::first_order`] +
/// [`PacProofCertifier::certify`].
///
/// # Parameters
///
/// - `lipschitz_constant`: The network's Lipschitz constant L > 0.
/// - `adversarial_output`: f(x_adv).
/// - `threshold`: The robustness threshold.
///
/// # Errors
///
/// Propagates errors from [`LipschitzBound::new`] and
/// [`PacProofCertifier::certify`].
pub fn certify_pgd_result(
    lipschitz_constant: f64,
    adversarial_output: f64,
    threshold: f64,
) -> Result<CertifiedRegion, CertificationError> {
    let lip = LipschitzBound::new(lipschitz_constant)?;
    let certifier = PacProofCertifier::first_order(lip);
    certifier.certify(adversarial_output, threshold, None)
}

/// Verify that a certified region is sound.
///
/// Checks the mathematical invariants of a [`CertifiedRegion`]:
///
/// 1. radius > 0
/// 2. margin > 0 (adversarial_output > threshold)
/// 3. For first-order: radius <= margin / L (within tolerance)
/// 4. For second-order: Taylor bound is non-negative at boundary
/// 5. Lipschitz constant is positive
///
/// Returns `true` if all invariants hold.
#[must_use]
pub fn verify_certified_region(region: &CertifiedRegion) -> bool {
    let tol = 1e-10;

    // Basic invariants.
    if region.radius() <= 0.0 {
        return false;
    }
    if region.margin() <= 0.0 {
        return false;
    }
    if region.lipschitz() <= 0.0 {
        return false;
    }
    if !region.radius().is_finite() {
        return false;
    }

    match region.mode() {
        CertificationMode::FirstOrder => {
            // r <= margin / L (the defining equation).
            let expected = region.margin() / region.lipschitz();
            region.radius() <= expected + tol
        }
        CertificationMode::SecondOrder => {
            // The region might have been produced by either first-order or
            // second-order formula (we take the max). Verify both bounds.
            let first_order_ok = {
                let expected = region.margin() / region.lipschitz();
                region.radius() <= expected + tol
            };

            let second_order_ok = match (region.hessian(), region.gradient_norm()) {
                (Some(h), Some(g)) if h > 0.0 => {
                    // At r = radius, verify: margin - g*r - (H/2)*r^2 >= -tol
                    let r = region.radius();
                    let taylor_lb = region.margin() - g * r - 0.5 * h * r * r;
                    taylor_lb >= -tol
                }
                _ => false,
            };

            first_order_ok || second_order_ok
        }
    }
}
