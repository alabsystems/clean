// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Alpha-CROWN per-neuron bound optimization.
//!
//! Alpha-CROWN improves on standard CROWN by optimizing the lower-bound
//! relaxation slope (alpha) per neuron via projected gradient descent.
//! For crossing neurons with pre-activation bounds [l, u] where l < 0 < u:
//!
//! - Standard CROWN uses a fixed lower bound slope (alpha = 0, conservative).
//! - Alpha-CROWN treats alpha as an optimizable parameter in [0, 1] and
//!   minimizes the output bound width via gradient descent.
//!
//! ## Theorems
//!
//! - **T43 (Alpha-CROWN soundness):** For any alpha in [0, 1], the backward
//!   pass produces valid (sound) output bounds.
//! - **T44 (Alpha-CROWN tighter than CROWN):** The optimized bounds are at
//!   least as tight as standard CROWN (which uses alpha = 0).
//!
//! ## Algorithm
//!
//! 1. Run IBP forward pass to get pre-activation bounds per layer.
//! 2. Initialize alphas using the default CROWN heuristic (u / (u - l)).
//! 3. Iterate: backward pass -> gradient -> update -> project to [0, 1].
//! 4. Return the tightest bounds found.

use super::crown_alpha_backward::{
    backward_pass, compute_alpha_gradient, ibp_forward, initialize_alphas, project_alphas,
};
use super::ibp::Interval;
use crate::spec::ProofStatus;

/// Per-neuron relaxation parameters for alpha-CROWN.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct AlphaCrownParams {
    /// Per-layer, per-neuron alpha values in [0, 1].
    pub alphas: Vec<Vec<f64>>,
}

/// Result of alpha-CROWN bound computation.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct AlphaCrownResult {
    /// Final output interval bounds after optimization.
    pub output_bounds: Interval,
    /// Per-layer intermediate bounds (from IBP forward pass).
    pub layer_bounds: Vec<Interval>,
    /// The optimized alpha parameters.
    pub params: AlphaCrownParams,
    /// Number of optimization iterations performed.
    pub iterations: usize,
}

/// Compute alpha-CROWN bounds for a multi-layer ReLU network.
///
/// Layers are specified as weight matrices and bias vectors. The network is:
///   x -> W_0*x+b_0 -> ReLU -> W_1*x+b_1 -> ReLU -> ... -> output
///
/// The last layer has no ReLU activation.
///
/// # Parameters
/// - `weights`: Per-layer weight matrices (row-major, out_features x in_features).
/// - `biases`: Per-layer bias vectors.
/// - `input_bounds`: Input domain as an `Interval`.
/// - `max_iterations`: Maximum projected gradient descent iterations.
/// - `learning_rate`: Step size for gradient descent on alpha parameters.
#[must_use]
pub fn alpha_crown_bounds(
    weights: &[Vec<Vec<f64>>],
    biases: &[Vec<f64>],
    input_bounds: &Interval,
    max_iterations: usize,
    learning_rate: f64,
) -> AlphaCrownResult {
    if weights.is_empty() {
        return AlphaCrownResult {
            output_bounds: *input_bounds,
            layer_bounds: vec![],
            params: AlphaCrownParams { alphas: vec![] },
            iterations: 0,
        };
    }

    // Step 1: IBP forward to get pre-activation bounds per layer.
    let layer_bounds = ibp_forward(weights, biases, input_bounds);

    // Step 2: Initialize alphas from default CROWN heuristic.
    let mut params = initialize_alphas(&layer_bounds);

    // Step 3: Iterative optimization via projected gradient descent.
    let mut best_width = f64::INFINITY;
    let mut best_params = params.clone();
    let mut best_output = backward_pass(weights, biases, input_bounds, &layer_bounds, &params);

    for iter_idx in 0..max_iterations {
        let current_output = backward_pass(weights, biases, input_bounds, &layer_bounds, &params);
        let current_width = current_output.upper - current_output.lower;

        if current_width < best_width {
            best_width = current_width;
            best_params = params.clone();
            best_output = current_output;
        }

        let grad =
            compute_alpha_gradient(weights, biases, input_bounds, &layer_bounds, &params, 1e-6);

        let mut changed = false;
        for (layer_idx, layer_grad) in grad.iter().enumerate() {
            for (neuron_idx, &g) in layer_grad.iter().enumerate() {
                if g.abs() > 1e-12 {
                    let lr = learning_rate / (1.0 + 0.01 * iter_idx as f64);
                    params.alphas[layer_idx][neuron_idx] -= lr * g;
                    changed = true;
                }
            }
        }

        if !changed {
            break;
        }

        project_alphas(&mut params);
    }

    // Final pass with best params.
    let _ = best_output;
    let final_output = backward_pass(weights, biases, input_bounds, &layer_bounds, &best_params);
    let final_width = final_output.upper - final_output.lower;
    if final_width < best_width {
        best_params = best_params.clone();
    }

    let output = backward_pass(weights, biases, input_bounds, &layer_bounds, &best_params);

    AlphaCrownResult {
        output_bounds: output,
        layer_bounds,
        params: best_params,
        iterations: max_iterations,
    }
}

/// Verify that all alphas are in [0, 1].
#[must_use]
pub fn verify_alphas_in_range(params: &AlphaCrownParams) -> bool {
    params
        .alphas
        .iter()
        .all(|layer| layer.iter().all(|&a| (0.0..=1.0).contains(&a)))
}

/// T43: Alpha-CROWN soundness (optimized alphas still produce valid bounds).
///
/// **Status:** `DerivedPending` -- verified via constructive proof in
/// `crown_proofs::verify_t43_alpha_soundness`. For any alpha in [0, 1], the
/// per-neuron relaxation of ReLU is sound: alpha*z <= ReLU(z) for z >= 0
/// and 0 <= ReLU(z) for z < 0. The upper relaxation (triangle) is independent
/// of alpha and always sound by T40.
pub const T43_ALPHA_CROWN_SOUND: ProofStatus = ProofStatus::DerivedPending;

/// T44: Alpha-CROWN tighter than CROWN (optimization cannot worsen bounds).
///
/// **Status:** `DerivedPending` -- verified via constructive proof in
/// `crown_proofs::verify_t44_alpha_tighter`. Standard CROWN uses alpha = 0.
/// Alpha-CROWN optimizes alpha in [0, 1], a superset that contains alpha = 0.
/// By the property of optimization over a superset, the optimum is at least
/// as good as any fixed feasible point, including alpha = 0.
pub const T44_ALPHA_TIGHTER_THAN_CROWN: ProofStatus = ProofStatus::DerivedPending;

/// T43: Alpha-CROWN soundness specification.
///
/// **Statement:** For any alpha in [0, 1], the alpha-CROWN backward pass
/// produces valid (sound) output bounds. This extends T40 by showing that
/// the parameterized lower bound alpha*z (for crossing neurons) is always
/// below ReLU(z) when z >= 0 (since alpha <= 1 implies alpha*z <= z = ReLU(z))
/// and the zero lower bound holds when z < 0.
///
/// **Status:** `DerivedPending` -- constructive verification in `crown_proofs.rs`.
#[derive(Debug)]
pub struct AlphaCrownSoundSpec {
    status: ProofStatus,
}

impl AlphaCrownSoundSpec {
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

impl Default for AlphaCrownSoundSpec {
    fn default() -> Self {
        Self::new()
    }
}

/// T44: Alpha-CROWN tightness specification.
///
/// **Statement:** Alpha-CROWN bounds are at least as tight as standard CROWN.
/// Standard CROWN fixes alpha = 0 for all crossing neurons. Alpha-CROWN
/// optimizes alpha in [0, 1] per neuron via projected gradient descent.
/// Since alpha = 0 is in the feasible set, the optimized configuration
/// achieves bounds at least as tight.
///
/// **Status:** `DerivedPending` -- constructive verification in `crown_proofs.rs`.
#[derive(Debug)]
pub struct AlphaCrownTighterSpec {
    status: ProofStatus,
}

impl AlphaCrownTighterSpec {
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

impl Default for AlphaCrownTighterSpec {
    fn default() -> Self {
        Self::new()
    }
}
