// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Lipschitz Constant Analysis for Neural Network Layers
//!
//! Formalizes Lipschitz constant computation and composition for networks
//! used in gamma-crown verification. The Lipschitz constant bounds how much
//! the output can change per unit change in input (or weights).
//!
//! ## Theorems
//!
//! - **T30 (Lipschitz compose):** For f with constant L_f and g with L_g,
//!   g(f(x)) has constant L_f * L_g (submultiplicativity).
//!
//! - **T31 (Eclipse block Lipschitz):** A compound "eclipse" block
//!   (attention + FFN + residual) has Lipschitz constant bounded by the
//!   product of individual layer constants, tightened by residual structure.
//!
//! - **T32 (Spectral norm bound):** For a linear layer y = Wx, the
//!   Lipschitz constant is sigma_max(W) (largest singular value).
//!
//! - **T33 (Residual Lipschitz):** For y = x + f(x) with f having constant
//!   L_f, the residual has constant 1 + L_f (triangle inequality).
//!
//! ## Connection to `neural_surgery::bound_propagation`
//!
//! The [`LipschitzBound`](crate::neural_surgery::LipschitzBound) type in
//! `neural_surgery` represents the same mathematical object. This module
//! provides the *proof strategies* for computing and composing those bounds,
//! while `neural_surgery` uses them for bound propagation under weight edits.

use crate::spec::ProofStatus;

/// Layer-level Lipschitz constant with provenance tracking.
///
/// Wraps a non-negative constant L such that ||f(x) - f(y)|| <= L * ||x - y||.
/// Tracks which theorem justifies the bound.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct LayerLipschitz {
    /// The Lipschitz constant L >= 0.
    constant: f64,
    /// Which theorem justifies this bound.
    source: LipschitzSource,
}

/// Source theorem for a Lipschitz constant.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum LipschitzSource {
    /// T32: Spectral norm of weight matrix.
    SpectralNorm,
    /// T30: Composition of two layers.
    Composition,
    /// T33: Residual connection (1 + L_f).
    Residual,
    /// T31: Eclipse block compound bound.
    EclipseBlock,
    /// ReLU: Lipschitz constant is 1 (non-expansive).
    Relu,
    /// Sigmoid: Lipschitz constant is 0.25 (max of sigma'(x) = sigma(x)(1-sigma(x))).
    Sigmoid,
}

impl LayerLipschitz {
    /// Create a new Lipschitz bound. Debug-asserts non-negative.
    #[must_use]
    pub fn new(constant: f64, source: LipschitzSource) -> Self {
        debug_assert!(
            constant >= 0.0,
            "Lipschitz constant must be non-negative: {constant}"
        );
        Self { constant, source }
    }

    /// The Lipschitz constant value.
    #[must_use]
    pub fn constant(&self) -> f64 {
        self.constant
    }

    /// The source theorem.
    #[must_use]
    pub fn source(&self) -> LipschitzSource {
        self.source
    }

    /// ReLU has Lipschitz constant 1.
    #[must_use]
    pub fn relu() -> Self {
        Self::new(1.0, LipschitzSource::Relu)
    }

    /// Sigmoid has Lipschitz constant 0.25.
    #[must_use]
    pub fn sigmoid() -> Self {
        Self::new(0.25, LipschitzSource::Sigmoid)
    }
}

// ---------------------------------------------------------------------------
// T30: Lipschitz Compose (Submultiplicativity)
// ---------------------------------------------------------------------------

/// Proof specification for T30: Lipschitz composition.
///
/// **Statement:** If f: X -> Y has Lipschitz constant L_f and
/// g: Y -> Z has Lipschitz constant L_g, then g . f: X -> Z has
/// Lipschitz constant L_f * L_g.
///
/// **Proof:**
///   ||g(f(x)) - g(f(y))|| <= L_g * ||f(x) - f(y)||   (g is L_g-Lipschitz)
///                           <= L_g * L_f * ||x - y||    (f is L_f-Lipschitz)
///
/// **Status:** `DerivedPending` -- kernel theorem
/// `NNVerify.Lipschitz.lipschitz_compose` registered as `Declaration::Theorem`
/// with proof term that type-checks via `tc.infer_type()` + `tc.is_def_eq()`.
/// See `nn_verify_lipschitz_eclipse.rs` in clean-kernel.
#[derive(Debug)]
pub struct LipschitzComposeSpec {
    status: ProofStatus,
}

impl LipschitzComposeSpec {
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

    /// Compose two Lipschitz bounds via submultiplicativity.
    #[must_use]
    pub fn compose(&self, first: &LayerLipschitz, second: &LayerLipschitz) -> LayerLipschitz {
        LayerLipschitz::new(
            first.constant() * second.constant(),
            LipschitzSource::Composition,
        )
    }

    /// Compose a chain of Lipschitz bounds (product of all constants).
    #[must_use]
    pub fn compose_chain(&self, layers: &[LayerLipschitz]) -> LayerLipschitz {
        let product = layers.iter().map(|l| l.constant()).product::<f64>();
        LayerLipschitz::new(product, LipschitzSource::Composition)
    }

    /// Verify the composition bound for concrete inputs.
    ///
    /// Given two function evaluations and their Lipschitz constants,
    /// checks that the composed mapping satisfies the bound.
    pub fn verify_concrete(
        &self,
        l_f: &LayerLipschitz,
        l_g: &LayerLipschitz,
        x_diff_norm: f64,
        fx_diff_norm: f64,
        gfx_diff_norm: f64,
    ) -> Result<(), String> {
        // Check f is L_f-Lipschitz
        if fx_diff_norm > l_f.constant() * x_diff_norm + f64::EPSILON {
            return Err(format!(
                "f violates L_f={}: ||f(x)-f(y)||={fx_diff_norm} > L_f*||x-y||={}",
                l_f.constant(),
                l_f.constant() * x_diff_norm,
            ));
        }
        // Check g . f is (L_f * L_g)-Lipschitz
        let composed = l_f.constant() * l_g.constant();
        if gfx_diff_norm > composed * x_diff_norm + f64::EPSILON {
            return Err(format!(
                "g.f violates L_f*L_g={composed}: ||g(f(x))-g(f(y))||={gfx_diff_norm} > {}",
                composed * x_diff_norm,
            ));
        }
        Ok(())
    }
}

impl Default for LipschitzComposeSpec {
    fn default() -> Self {
        Self::new()
    }
}

// ---------------------------------------------------------------------------
// T33: Residual Connection Lipschitz
// ---------------------------------------------------------------------------

/// Proof specification for T33: residual connection Lipschitz bound.
///
/// **Statement:** For a residual block y = x + f(x) where f has Lipschitz
/// constant L_f, the overall mapping has Lipschitz constant 1 + L_f.
///
/// **Proof:**
///   ||y(x) - y(z)|| = ||(x + f(x)) - (z + f(z))||
///                    = ||(x - z) + (f(x) - f(z))||
///                    <= ||x - z|| + ||f(x) - f(z)||   (triangle inequality)
///                    <= ||x - z|| + L_f * ||x - z||    (f is L_f-Lipschitz)
///                    = (1 + L_f) * ||x - z||
///
/// **Status:** `DerivedPending` -- kernel theorem
/// `NNVerify.Lipschitz.residual_lipschitz_sum` registered as
/// `Declaration::Theorem`. See `nn_verify_lipschitz_eclipse.rs` in clean-kernel.
#[derive(Debug)]
pub struct ResidualLipschitzSpec {
    status: ProofStatus,
}

impl ResidualLipschitzSpec {
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

    /// Compute the Lipschitz constant for a residual block y = x + f(x).
    #[must_use]
    pub fn residual_bound(&self, f_lipschitz: &LayerLipschitz) -> LayerLipschitz {
        LayerLipschitz::new(1.0 + f_lipschitz.constant(), LipschitzSource::Residual)
    }

    /// Verify the residual bound for concrete vectors.
    ///
    /// `x`, `z` are inputs; `fx`, `fz` are f(x), f(z).
    pub fn verify_concrete(
        &self,
        x: &[f64],
        z: &[f64],
        fx: &[f64],
        fz: &[f64],
        f_lipschitz: &LayerLipschitz,
    ) -> Result<(), String> {
        let n = x.len();
        if z.len() != n || fx.len() != n || fz.len() != n {
            return Err("dimension mismatch".to_string());
        }

        let x_diff_sq: f64 = x.iter().zip(z.iter()).map(|(a, b)| (a - b).powi(2)).sum();
        let x_diff_norm = x_diff_sq.sqrt();

        // Residual output: y = x + f(x), w = z + f(z)
        let mut y_diff_sq = 0.0;
        for i in 0..n {
            let yi = x[i] + fx[i];
            let wi = z[i] + fz[i];
            y_diff_sq += (yi - wi).powi(2);
        }
        let y_diff_norm = y_diff_sq.sqrt();

        let bound = (1.0 + f_lipschitz.constant()) * x_diff_norm;
        if y_diff_norm > bound + f64::EPSILON {
            return Err(format!(
                "residual Lipschitz violated: ||y-w||={y_diff_norm} > (1+L_f)*||x-z||={bound}"
            ));
        }
        Ok(())
    }
}

impl Default for ResidualLipschitzSpec {
    fn default() -> Self {
        Self::new()
    }
}

// ---------------------------------------------------------------------------
// T31: Eclipse Block Lipschitz
// ---------------------------------------------------------------------------

/// Proof specification for T31: eclipse block Lipschitz constant.
///
/// **Statement:** An "eclipse block" consists of:
///   1. Multi-head attention (Lipschitz L_attn)
///   2. Residual connection around attention
///   3. Feed-forward network (Lipschitz L_ffn)
///   4. Residual connection around FFN
///
/// The overall block Lipschitz constant is:
///   L_block = (1 + L_attn) * (1 + L_ffn)
///
/// This follows from composing T33 (residual) with T30 (composition).
///
/// **Status:** `DerivedPending` -- kernel theorem
/// `NNVerify.Lipschitz.eclipse_block_lipschitz` registered as
/// `Declaration::Theorem`. See `nn_verify_lipschitz_eclipse.rs` in clean-kernel.
#[derive(Debug)]
pub struct EclipseLipschitzSpec {
    status: ProofStatus,
}

impl EclipseLipschitzSpec {
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

    /// Compute the eclipse block Lipschitz constant.
    #[must_use]
    pub fn block_bound(
        &self,
        attn_lipschitz: &LayerLipschitz,
        ffn_lipschitz: &LayerLipschitz,
    ) -> LayerLipschitz {
        let residual_spec = ResidualLipschitzSpec::new();
        let compose_spec = LipschitzComposeSpec::new();

        let attn_residual = residual_spec.residual_bound(attn_lipschitz);
        let ffn_residual = residual_spec.residual_bound(ffn_lipschitz);
        compose_spec.compose(&attn_residual, &ffn_residual)
    }

    /// Compute the Lipschitz constant for N stacked eclipse blocks.
    #[must_use]
    pub fn stacked_blocks_bound(
        &self,
        blocks: &[(LayerLipschitz, LayerLipschitz)],
    ) -> LayerLipschitz {
        let compose_spec = LipschitzComposeSpec::new();
        let per_block: Vec<LayerLipschitz> = blocks
            .iter()
            .map(|(attn, ffn)| self.block_bound(attn, ffn))
            .collect();
        compose_spec.compose_chain(&per_block)
    }
}

impl Default for EclipseLipschitzSpec {
    fn default() -> Self {
        Self::new()
    }
}
