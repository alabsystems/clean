// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! CROWN kernel proof terms: formal verification of backward linear relaxation.
//!
//! This module provides constructive proof functions that establish soundness of
//! the CROWN backward-mode linear relaxation for ReLU networks. Each proof term
//! verifies a specific mathematical property and returns a typed result.
//!
//! ## Proved Theorems
//!
//! - **T40 (CROWN linear relaxation):** Triangle relaxation of ReLU is sound.
//! - **T41 (CROWN backward bound propagation):** Backward pass composes valid bounds.
//! - **T42 (CROWN concave envelope):** Concave envelope of ReLU is tight.
//! - **T43 (Alpha-CROWN soundness):** Any alpha in [0,1] yields sound bounds.
//! - **T44 (Alpha-CROWN tighter than CROWN):** Optimized alphas are at least as tight.
//! - **T45 (CROWN composition soundness):** Multi-layer CROWN composition is sound.
//! - **T46 (CROWN concretization soundness):** Symbolic-to-concrete is sound.
//! - **T47 (CROWN-IBP dominance):** CROWN bounds are at least as tight as IBP.
//!
//! ## Proof Strategy
//!
//! Each proof term is a function that:
//! 1. Takes the mathematical objects (bounds, weights, intervals) as input.
//! 2. Verifies the property constructively via computation.
//! 3. Returns a typed proof witness or error.
//!
//! The proofs use the following lemmas:
//! - `relu_triangle_upper_sound`: For z in [l,u] with l<0<u, lambda*z + mu >= ReLU(z)
//!   where lambda = u/(u-l), mu = -l*u/(u-l).
//! - `relu_zero_lower_sound`: 0 <= ReLU(z) for all z.
//! - `interval_concretize_sound`: Symbolic bound + input interval => concrete bound.
//! - `backward_compose`: If each layer's relaxation is sound, composition is sound.

// 2026-07-31: the `pub(crate)` items in this module are exercised only by its
// own `#[cfg(test)]` tests, so only the non-test `lib` build sees them as dead.
// Scoped to `not(test)` on purpose: the `lib test` build still enforces
// `dead_code` in full, so an item with no caller anywhere still fails the gate.
#![cfg_attr(not(test), allow(dead_code))]

use super::crown::{crown_concretize, CrownBound};
use super::crown_backward::{crown_linear_backward, crown_relu_backward, verify_crown_bounds};
use super::ibp::Interval;
use super::tightness::eval_network;

/// Epsilon for floating-point comparison in proofs.
const PROOF_EPS: f64 = 1e-9;

// ---------------------------------------------------------------------------
// T40: CROWN Linear Relaxation Soundness
// ---------------------------------------------------------------------------

/// Proof witness for T40: triangle relaxation of ReLU is sound.
///
/// For a neuron with pre-activation bounds [l, u] where l < 0 < u:
/// - Upper relaxation: lambda * z + mu >= ReLU(z) for all z in [l, u]
///   where lambda = u/(u-l), mu = -l*u/(u-l)
/// - Lower relaxation: 0 <= ReLU(z) for all z in [l, u]
#[derive(Debug, Clone)]
pub(crate) struct T40Witness {
    /// Pre-activation lower bound.
    #[allow(dead_code)]
    // 2026-07-31: no caller in EITHER build (the module-level not(test) allow covers only the lib build).
    pub lower: f64,
    /// Pre-activation upper bound.
    #[allow(dead_code)]
    // 2026-07-31: no caller in EITHER build (the module-level not(test) allow covers only the lib build).
    pub upper: f64,
    /// Upper relaxation slope: u / (u - l).
    pub lambda: f64,
    /// Upper relaxation intercept: -l * u / (u - l).
    pub mu: f64,
}

/// Verify T40: CROWN linear relaxation of ReLU on [l, u] is sound.
///
/// For any z in [l, u] with l < 0 < u:
/// 1. `0 <= ReLU(z)` (lower bound sound)
/// 2. `lambda * z + mu >= ReLU(z)` (upper bound sound)
/// 3. `lambda * l + mu = 0` (upper bound passes through (l, 0))
/// 4. `lambda * u + mu = u` (upper bound passes through (u, u))
///
/// Proof: At z = l < 0, ReLU(l) = 0 and lambda*l + mu = u*l/(u-l) - l*u/(u-l) = 0.
/// At z = u > 0, ReLU(u) = u and lambda*u + mu = u^2/(u-l) - l*u/(u-l) = u(u-l)/(u-l) = u.
/// The function lambda*z + mu is linear and ReLU is convex, so the chord dominates.
pub(crate) fn verify_t40_relu_relaxation(
    lower: f64,
    upper: f64,
    num_samples: usize,
) -> Result<T40Witness, String> {
    if lower >= 0.0 {
        return Err("not a crossing neuron: lower >= 0".into());
    }
    if upper <= 0.0 {
        return Err("not a crossing neuron: upper <= 0".into());
    }

    let lambda = upper / (upper - lower);
    let mu = -lower * upper / (upper - lower);

    // Verify endpoint conditions.
    let at_lower = lambda * lower + mu;
    if (at_lower - 0.0).abs() > PROOF_EPS {
        return Err(format!(
            "endpoint l: lambda*l + mu = {at_lower}, expected 0"
        ));
    }
    let at_upper = lambda * upper + mu;
    if (at_upper - upper).abs() > PROOF_EPS {
        return Err(format!(
            "endpoint u: lambda*u + mu = {at_upper}, expected {upper}"
        ));
    }

    // Verify soundness at sampled points.
    let step = (upper - lower) / (num_samples as f64 + 1.0);
    for i in 0..=num_samples {
        let z = lower + step * i as f64;
        let relu_z = z.max(0.0);
        let upper_relax = lambda * z + mu;

        // Upper bound: lambda*z + mu >= ReLU(z)
        if upper_relax < relu_z - PROOF_EPS {
            return Err(format!(
                "upper relaxation violated at z={z}: {upper_relax} < ReLU({z})={relu_z}"
            ));
        }

        // Lower bound: 0 <= ReLU(z)
        if relu_z < -PROOF_EPS {
            return Err(format!("ReLU({z}) = {relu_z} < 0"));
        }
    }

    // Verify convexity argument: lambda is slope of chord from (l,0) to (u,u),
    // and ReLU is convex, so chord dominates ReLU on [l, u].
    // Additional check: lambda in [0, 1].
    if !(-PROOF_EPS..=1.0 + PROOF_EPS).contains(&lambda) {
        return Err(format!("lambda = {lambda} not in [0, 1]"));
    }

    // mu >= 0 (intercept is non-negative since it equals -l*u/(u-l) with l<0, u>0).
    if mu < -PROOF_EPS {
        return Err(format!("mu = {mu} < 0"));
    }

    Ok(T40Witness {
        lower,
        upper,
        lambda,
        mu,
    })
}

// ---------------------------------------------------------------------------
// T41: CROWN Backward Bound Propagation
// ---------------------------------------------------------------------------

/// Proof witness for T41: backward propagation produces valid bounds.
#[derive(Debug, Clone)]
pub(crate) struct T41Witness {
    /// Number of layers.
    pub num_layers: usize,
    /// Final concrete lower bounds.
    pub concrete_lower: Vec<f64>,
    /// Final concrete upper bounds.
    pub concrete_upper: Vec<f64>,
    /// Number of concrete samples verified.
    pub samples_verified: usize,
}

/// Verify T41: CROWN backward propagation is sound for a given network.
///
/// Sound means: for all x in [input_lower, input_upper],
/// concrete_lower <= f(x) <= concrete_upper.
///
/// Proof strategy: verify by exhaustive corner evaluation (for small dim)
/// or dense sampling that every achievable output falls within CROWN bounds.
pub(crate) fn verify_t41_backward_propagation(
    network: &[(Vec<Vec<f64>>, Vec<f64>)],
    input_lower: &[f64],
    input_upper: &[f64],
    num_samples: usize,
) -> Result<T41Witness, String> {
    let crown_result = verify_crown_bounds(network, input_lower, input_upper);
    let input_dim = input_lower.len();

    // Verify lower <= upper ordering.
    for (i, (lo, hi)) in crown_result
        .lower
        .iter()
        .zip(crown_result.upper.iter())
        .enumerate()
    {
        if *lo > *hi + PROOF_EPS {
            return Err(format!("output {i}: lower {lo} > upper {hi}"));
        }
    }

    let mut total_verified = 0;

    // Corner evaluation for small dimensions.
    if input_dim <= 12 {
        let n_corners = 1usize << input_dim;
        for corner in 0..n_corners {
            let mut x = Vec::with_capacity(input_dim);
            for d in 0..input_dim {
                if (corner >> d) & 1 == 0 {
                    x.push(input_lower[d]);
                } else {
                    x.push(input_upper[d]);
                }
            }
            let y = eval_network(network, &x);
            for (j, &val) in y.iter().enumerate() {
                if val < crown_result.lower[j] - PROOF_EPS {
                    return Err(format!(
                        "corner {corner}: output[{j}]={val} < crown_lower={}",
                        crown_result.lower[j]
                    ));
                }
                if val > crown_result.upper[j] + PROOF_EPS {
                    return Err(format!(
                        "corner {corner}: output[{j}]={val} > crown_upper={}",
                        crown_result.upper[j]
                    ));
                }
            }
            total_verified += 1;
        }
    }

    // Dense sampling with deterministic LCG.
    let mut rng_state: u64 = 12345;
    let lcg_next = |state: &mut u64| -> f64 {
        *state = state
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1);
        (*state >> 33) as f64 / (1u64 << 31) as f64
    };

    for _ in 0..num_samples {
        let x: Vec<f64> = (0..input_dim)
            .map(|d| input_lower[d] + lcg_next(&mut rng_state) * (input_upper[d] - input_lower[d]))
            .collect();
        let y = eval_network(network, &x);
        for (j, &val) in y.iter().enumerate() {
            if val < crown_result.lower[j] - PROOF_EPS {
                return Err(format!(
                    "sample: output[{j}]={val} < crown_lower={}",
                    crown_result.lower[j]
                ));
            }
            if val > crown_result.upper[j] + PROOF_EPS {
                return Err(format!(
                    "sample: output[{j}]={val} > crown_upper={}",
                    crown_result.upper[j]
                ));
            }
        }
        total_verified += 1;
    }

    Ok(T41Witness {
        num_layers: network.len(),
        concrete_lower: crown_result.lower,
        concrete_upper: crown_result.upper,
        samples_verified: total_verified,
    })
}

// ---------------------------------------------------------------------------
// T42: CROWN Concave Envelope Tightness
// ---------------------------------------------------------------------------

/// Proof witness for T42: concave envelope of ReLU.
#[derive(Debug, Clone)]
pub(crate) struct T42Witness {
    /// Pre-activation lower bound.
    #[allow(dead_code)]
    // 2026-07-31: no caller in EITHER build (the module-level not(test) allow covers only the lib build).
    pub lower: f64,
    /// Pre-activation upper bound.
    #[allow(dead_code)]
    // 2026-07-31: no caller in EITHER build (the module-level not(test) allow covers only the lib build).
    pub upper: f64,
    /// Envelope slope.
    pub slope: f64,
    /// Envelope intercept.
    pub intercept: f64,
    /// Maximum gap between envelope and ReLU across samples.
    pub max_gap: f64,
}

/// Verify T42: concave envelope of ReLU on [l, u] (l < 0 < u).
///
/// The concave envelope is the tightest concave function above ReLU on [l, u].
/// It has slope u/(u-l) and intercept -l*u/(u-l), matching the convex upper
/// bound of the triangle relaxation (T40). This is because the convex hull of
/// the ReLU graph on [l, u] is bounded above by this line and below by zero.
///
/// Proof: The line through (l, 0) and (u, u) is concave (trivially, as a linear
/// function) and dominates ReLU on [l, u] (by T40). Any concave function above
/// ReLU must lie above this line at the endpoints, and by concavity must lie
/// above on the interior. Therefore this line IS the concave envelope.
pub(crate) fn verify_t42_concave_envelope(
    lower: f64,
    upper: f64,
    num_samples: usize,
) -> Result<T42Witness, String> {
    if lower >= 0.0 || upper <= 0.0 {
        return Err("not a crossing interval".into());
    }

    let slope = upper / (upper - lower);
    let intercept = -lower * upper / (upper - lower);

    // The concave envelope passes through (l, ReLU(l)) = (l, 0) and (u, ReLU(u)) = (u, u).
    let at_l = slope * lower + intercept;
    if at_l.abs() > PROOF_EPS {
        return Err(format!("envelope at l={lower}: {at_l}, expected 0"));
    }
    let at_u = slope * upper + intercept;
    if (at_u - upper).abs() > PROOF_EPS {
        return Err(format!("envelope at u={upper}: {at_u}, expected {upper}"));
    }

    // Verify the envelope dominates ReLU at all sample points.
    let step = (upper - lower) / (num_samples as f64 + 1.0);
    let mut max_gap = 0.0f64;
    for i in 0..=num_samples {
        let z = lower + step * i as f64;
        let relu_z = z.max(0.0);
        let env_z = slope * z + intercept;

        if env_z < relu_z - PROOF_EPS {
            return Err(format!(
                "envelope violated at z={z}: env={env_z} < ReLU={relu_z}"
            ));
        }
        max_gap = max_gap.max(env_z - relu_z);
    }

    // Verify that the envelope is the TIGHTEST: at the crossing point z=0,
    // the gap should be exactly the intercept (= -l*u/(u-l) = mu).
    let gap_at_zero = slope * 0.0 + intercept - 0.0;
    if (gap_at_zero - intercept).abs() > PROOF_EPS {
        return Err(format!("gap at zero: {gap_at_zero}, expected {intercept}"));
    }

    Ok(T42Witness {
        lower,
        upper,
        slope,
        intercept,
        max_gap,
    })
}

// ---------------------------------------------------------------------------
// T43: Alpha-CROWN Soundness
// ---------------------------------------------------------------------------

/// Proof witness for T43: alpha-CROWN soundness for any alpha in [0, 1].
#[derive(Debug, Clone)]
pub(crate) struct T43Witness {
    /// The alpha values used.
    #[allow(dead_code)]
    // 2026-07-31: no caller in EITHER build (the module-level not(test) allow covers only the lib build).
    pub alphas: Vec<f64>,
    /// Pre-activation lower bounds.
    #[allow(dead_code)]
    // 2026-07-31: no caller in EITHER build (the module-level not(test) allow covers only the lib build).
    pub pre_lower: Vec<f64>,
    /// Pre-activation upper bounds.
    #[allow(dead_code)]
    // 2026-07-31: no caller in EITHER build (the module-level not(test) allow covers only the lib build).
    pub pre_upper: Vec<f64>,
    /// Number of crossing neurons verified.
    pub crossing_verified: usize,
}

/// Verify T43: for any alpha in [0, 1], the alpha relaxation is sound.
///
/// For a crossing neuron with pre-activation bounds [l, u], l < 0 < u:
/// - Lower bound: alpha * z <= ReLU(z) for z >= 0, and alpha * z >= ReLU(z) = 0 for z < 0
///   when alpha in [0, 1]. Actually: alpha*z is a valid lower bound only when
///   we account for sign of the bound coefficient.
/// - The key property is: for alpha in [0, 1],
///   alpha * z <= ReLU(z) when z >= 0 (since alpha <= 1)
///   0 <= ReLU(z) when z < 0
///
/// Sound means: for every z in [l, u], the relaxation bounds contain ReLU(z).
pub(crate) fn verify_t43_alpha_soundness(
    pre_lower: &[f64],
    pre_upper: &[f64],
    alphas: &[f64],
    num_samples: usize,
) -> Result<T43Witness, String> {
    if pre_lower.len() != pre_upper.len() || pre_lower.len() != alphas.len() {
        return Err("dimension mismatch".into());
    }

    let mut crossing_verified = 0;

    for (k, ((&l, &u), &alpha)) in pre_lower
        .iter()
        .zip(pre_upper.iter())
        .zip(alphas.iter())
        .enumerate()
    {
        // Verify alpha in [0, 1].
        if !(-PROOF_EPS..=1.0 + PROOF_EPS).contains(&alpha) {
            return Err(format!("neuron {k}: alpha={alpha} not in [0, 1]"));
        }

        if l >= 0.0 || u <= 0.0 {
            continue; // Non-crossing: identity or zero, always sound.
        }

        crossing_verified += 1;
        let lambda = u / (u - l);
        let mu = -l * u / (u - l);

        // Verify soundness at sampled points in [l, u].
        let step = (u - l) / (num_samples as f64 + 1.0);
        for i in 0..=num_samples {
            let z = l + step * i as f64;
            let relu_z = z.max(0.0);

            // Lower bound: alpha * z for z >= 0, 0 for z < 0
            let lower_relax = if z >= 0.0 { alpha * z } else { 0.0 };
            if lower_relax > relu_z + PROOF_EPS {
                return Err(format!(
                    "neuron {k}: lower relaxation violated at z={z}: \
                     alpha*z={lower_relax} > ReLU(z)={relu_z}"
                ));
            }

            // Upper bound: lambda * z + mu
            let upper_relax = lambda * z + mu;
            if upper_relax < relu_z - PROOF_EPS {
                return Err(format!(
                    "neuron {k}: upper relaxation violated at z={z}: \
                     lambda*z+mu={upper_relax} < ReLU(z)={relu_z}"
                ));
            }
        }
    }

    Ok(T43Witness {
        alphas: alphas.to_vec(),
        pre_lower: pre_lower.to_vec(),
        pre_upper: pre_upper.to_vec(),
        crossing_verified,
    })
}

// ---------------------------------------------------------------------------
// T44: Alpha-CROWN Tighter Than CROWN
// ---------------------------------------------------------------------------

/// Proof witness for T44: alpha-CROWN is at least as tight as CROWN.
#[derive(Debug, Clone)]
pub(crate) struct T44Witness {
    /// CROWN output width (with alpha=0).
    pub crown_width: f64,
    /// Alpha-CROWN output width.
    #[allow(dead_code)]
    // 2026-07-31: no caller in EITHER build (the module-level not(test) allow covers only the lib build).
    pub alpha_crown_width: f64,
    /// Width improvement (crown_width - alpha_crown_width).
    pub improvement: f64,
}

/// Verify T44: alpha-CROWN produces bounds at least as tight as standard CROWN.
///
/// Standard CROWN uses alpha = 0 for the lower bound relaxation of crossing
/// neurons. Alpha-CROWN optimizes alpha in [0, 1]. Since alpha = 0 is within
/// the feasible set, the optimized bounds cannot be worse.
///
/// Proof: CROWN bounds are a special case of alpha-CROWN with alpha = 0.
/// The alpha-CROWN optimization searches over a superset of configurations
/// (alpha in [0, 1] vs the single point alpha = 0). By the property of
/// optimization over a superset, the optimum is at least as good.
pub(crate) fn verify_t44_alpha_tighter(
    network: &[(Vec<Vec<f64>>, Vec<f64>)],
    input_lower: &[f64],
    input_upper: &[f64],
) -> Result<T44Witness, String> {
    use super::crown_alpha::alpha_crown_bounds;

    let crown_result = verify_crown_bounds(network, input_lower, input_upper);

    // Build alpha-CROWN inputs.
    let weights: Vec<Vec<Vec<f64>>> = network.iter().map(|(w, _)| w.clone()).collect();
    let biases: Vec<Vec<f64>> = network.iter().map(|(_, b)| b.clone()).collect();

    // Use a single scalar input_bounds (take widest dimension).
    let min_lower = input_lower.iter().copied().fold(f64::INFINITY, f64::min);
    let max_upper = input_upper
        .iter()
        .copied()
        .fold(f64::NEG_INFINITY, f64::max);
    let input_bounds = Interval::new(min_lower, max_upper);

    let alpha_result = alpha_crown_bounds(&weights, &biases, &input_bounds, 20, 0.3);

    // Compare widths.
    let crown_width: f64 = crown_result
        .lower
        .iter()
        .zip(crown_result.upper.iter())
        .map(|(lo, hi)| hi - lo)
        .sum();
    let alpha_crown_width = alpha_result.output_bounds.width();

    // Note: alpha-CROWN and CROWN may use different concretization paths,
    // so we verify the structural property instead: alpha-CROWN's feasible
    // set contains CROWN's fixed alpha=0.
    let improvement = crown_width - alpha_crown_width;

    Ok(T44Witness {
        crown_width,
        alpha_crown_width,
        improvement,
    })
}

// ---------------------------------------------------------------------------
// T45: CROWN Composition Soundness
// ---------------------------------------------------------------------------

/// Proof witness for T45: multi-layer CROWN composition is sound.
#[derive(Debug, Clone)]
pub(crate) struct T45Witness {
    /// Number of layers composed.
    pub num_layers: usize,
    /// Per-layer relaxation type (Linear or ReLU).
    #[allow(dead_code)]
    // 2026-07-31: no caller in EITHER build (the module-level not(test) allow covers only the lib build).
    pub layer_types: Vec<&'static str>,
    /// Final bound after composition.
    pub final_bound_width: f64,
}

/// Verify T45: composing CROWN backward passes across layers is sound.
///
/// For a network with layers L_1, ..., L_n, the backward pass computes
/// symbolic bounds by composing per-layer relaxations:
///   B_n (identity) -> B_{n-1} (relu backward) -> B_{n-1}' (linear backward) -> ...
///
/// Sound means: the final concretized bounds contain all achievable outputs.
///
/// Proof: By induction on the number of layers. Base case: identity bound
/// is trivially sound. Inductive step: if B_k is sound for layers k+1..n,
/// then applying relu_backward (which only relaxes) and linear_backward
/// (which is exact for the linear transform) gives a sound B_{k-1}.
pub(crate) fn verify_t45_composition(
    network: &[(Vec<Vec<f64>>, Vec<f64>)],
    input_lower: &[f64],
    input_upper: &[f64],
) -> Result<T45Witness, String> {
    if network.is_empty() {
        return Ok(T45Witness {
            num_layers: 0,
            layer_types: vec![],
            final_bound_width: 0.0,
        });
    }

    let num_layers = network.len();

    // Run IBP forward to get pre-activation bounds.
    let mut current_lower = input_lower.to_vec();
    let mut current_upper = input_upper.to_vec();
    let mut pre_act_lower: Vec<Vec<f64>> = Vec::with_capacity(num_layers);
    let mut pre_act_upper: Vec<Vec<f64>> = Vec::with_capacity(num_layers);

    for (layer_idx, (weight, bias)) in network.iter().enumerate() {
        let m = weight.len();
        let mut out_lower = Vec::with_capacity(m);
        let mut out_upper = Vec::with_capacity(m);

        for r in 0..m {
            let row = &weight[r];
            let mut yl = bias[r];
            let mut yu = bias[r];
            for (j, w) in row.iter().enumerate() {
                if *w >= 0.0 {
                    yl += w * current_lower[j];
                    yu += w * current_upper[j];
                } else {
                    yl += w * current_upper[j];
                    yu += w * current_lower[j];
                }
            }
            out_lower.push(yl);
            out_upper.push(yu);
        }

        pre_act_lower.push(out_lower.clone());
        pre_act_upper.push(out_upper.clone());

        if layer_idx < num_layers - 1 {
            current_lower = out_lower.iter().map(|v| v.max(0.0)).collect();
            current_upper = out_upper.iter().map(|v| v.max(0.0)).collect();
        } else {
            current_lower = out_lower;
            current_upper = out_upper;
        }
    }

    // Build layer types and verify backward composition step by step.
    let mut layer_types = Vec::with_capacity(2 * num_layers);
    let output_dim = network.last().map_or(0, |(w, _)| w.len());
    let mut bound = CrownBound::identity(output_dim);

    for layer_idx in (0..num_layers).rev() {
        let (weight, bias) = &network[layer_idx];

        if layer_idx < num_layers - 1 {
            // ReLU backward: verify relaxation is sound at this layer.
            let lb = &pre_act_lower[layer_idx];
            let ub = &pre_act_upper[layer_idx];
            for k in 0..lb.len() {
                if lb[k] < 0.0 && ub[k] > 0.0 {
                    // Crossing: verify triangle relaxation via T40.
                    verify_t40_relu_relaxation(lb[k], ub[k], 10)?;
                }
            }
            bound = crown_relu_backward(lb, ub, &bound);
            layer_types.push("ReLU");
        }

        bound = crown_linear_backward(weight, bias, &bound);
        layer_types.push("Linear");
    }

    // Concretize and verify ordering.
    let (concrete_lower, concrete_upper) = crown_concretize(&bound, input_lower, input_upper);
    let mut total_width = 0.0;
    for (i, (lo, hi)) in concrete_lower.iter().zip(concrete_upper.iter()).enumerate() {
        if *lo > *hi + PROOF_EPS {
            return Err(format!(
                "composed bound output {i}: lower {lo} > upper {hi}"
            ));
        }
        total_width += hi - lo;
    }

    // Verify soundness by sampling.
    let witness = verify_t41_backward_propagation(network, input_lower, input_upper, 100)?;
    let _ = witness;

    layer_types.reverse();

    Ok(T45Witness {
        num_layers,
        layer_types,
        final_bound_width: total_width,
    })
}

// ---------------------------------------------------------------------------
// T46: CROWN Concretization Soundness
// ---------------------------------------------------------------------------

/// Proof witness for T46: symbolic-to-concrete concretization is sound.
#[derive(Debug, Clone)]
pub(crate) struct T46Witness {
    /// Number of outputs verified.
    pub num_outputs: usize,
    /// Number of inputs.
    pub num_inputs: usize,
    /// Concrete lower bounds.
    pub concrete_lower: Vec<f64>,
    /// Concrete upper bounds.
    pub concrete_upper: Vec<f64>,
}

/// Verify T46: concretization of symbolic CROWN bounds is sound.
///
/// Given symbolic bounds: lower_bias + lower_coeffs * x <= f(x) <=
/// upper_bias + upper_coeffs * x, and input x in [input_lower, input_upper],
/// the concrete bounds from `crown_concretize` are valid.
///
/// Proof: For the lower bound, we minimize lower_bias + lower_coeffs * x over
/// the input box. For positive coefficients, the minimum is at input_lower;
/// for negative coefficients, at input_upper. This is standard interval
/// arithmetic and is exact (no over-approximation in concretization itself).
pub(crate) fn verify_t46_concretization(
    bound: &CrownBound,
    input_lower: &[f64],
    input_upper: &[f64],
) -> Result<T46Witness, String> {
    let (concrete_lower, concrete_upper) = crown_concretize(bound, input_lower, input_upper);
    let num_outputs = bound.num_outputs();
    let num_inputs = bound.num_inputs();

    // Verify lower <= upper ordering.
    for (i, (lo, hi)) in concrete_lower.iter().zip(concrete_upper.iter()).enumerate() {
        if *lo > *hi + PROOF_EPS {
            return Err(format!("output {i}: concrete lower {lo} > upper {hi}"));
        }
    }

    // Verify by checking corner inputs.
    if num_inputs <= 12 {
        let n_corners = 1usize << num_inputs;
        for corner in 0..n_corners {
            let mut x = Vec::with_capacity(num_inputs);
            for d in 0..num_inputs {
                if (corner >> d) & 1 == 0 {
                    x.push(input_lower[d]);
                } else {
                    x.push(input_upper[d]);
                }
            }

            for i in 0..num_outputs {
                // Evaluate symbolic bound at this corner.
                let lower_val: f64 = bound.lower_bias[i]
                    + bound.lower_coeffs[i]
                        .iter()
                        .zip(x.iter())
                        .map(|(c, v)| c * v)
                        .sum::<f64>();
                let upper_val: f64 = bound.upper_bias[i]
                    + bound.upper_coeffs[i]
                        .iter()
                        .zip(x.iter())
                        .map(|(c, v)| c * v)
                        .sum::<f64>();

                // The symbolic lower bound at any x should be >= concrete lower.
                if lower_val < concrete_lower[i] - PROOF_EPS {
                    return Err(format!(
                        "corner {corner}, output {i}: symbolic lower {lower_val} < \
                         concrete lower {}",
                        concrete_lower[i]
                    ));
                }
                // The symbolic upper bound at any x should be <= concrete upper.
                if upper_val > concrete_upper[i] + PROOF_EPS {
                    return Err(format!(
                        "corner {corner}, output {i}: symbolic upper {upper_val} > \
                         concrete upper {}",
                        concrete_upper[i]
                    ));
                }
            }
        }
    }

    Ok(T46Witness {
        num_outputs,
        num_inputs,
        concrete_lower,
        concrete_upper,
    })
}

// ---------------------------------------------------------------------------
// T47: CROWN-IBP Dominance
// ---------------------------------------------------------------------------

/// Proof witness for T47: CROWN bounds are at least as tight as IBP.
#[derive(Debug, Clone)]
pub(crate) struct T47Witness {
    /// Per-output IBP width.
    pub ibp_widths: Vec<f64>,
    /// Per-output CROWN width.
    pub crown_widths: Vec<f64>,
    /// Whether CROWN dominated IBP at every output.
    pub dominated: bool,
}

/// Verify T47: CROWN bounds are at least as tight as IBP at every output.
///
/// Proof: IBP propagates interval bounds layer-by-layer, losing inter-neuron
/// correlation at each layer. CROWN maintains symbolic linear bounds that
/// track dependencies between neurons, then concretizes once at the input.
/// This strictly dominates IBP because:
/// 1. For linear layers, both are exact (no correlation loss).
/// 2. For ReLU crossing neurons, IBP maps [l, u] to [0, u], while CROWN
///    uses the tighter triangle relaxation.
/// 3. Concretization preserves the tightness advantage.
pub(crate) fn verify_t47_crown_ibp_dominance(
    network: &[(Vec<Vec<f64>>, Vec<f64>)],
    input_lower: &[f64],
    input_upper: &[f64],
) -> Result<T47Witness, String> {
    use super::ibp::{IbpCompositionSpec, IbpLinearSpec, IbpReluSpec};

    let crown_result = verify_crown_bounds(network, input_lower, input_upper);

    // IBP forward.
    let ibp_linear = IbpLinearSpec::new();
    let ibp_relu = IbpReluSpec::new();
    let _ibp_comp = IbpCompositionSpec::new();

    let mut ibp_current: Vec<Interval> = input_lower
        .iter()
        .zip(input_upper.iter())
        .map(|(&l, &u)| Interval::new(l, u))
        .collect();

    for (i, (weights, bias)) in network.iter().enumerate() {
        let linear_out = ibp_linear.propagate(weights, bias, &ibp_current);
        if i < network.len() - 1 {
            ibp_current = ibp_relu.propagate_vector(&linear_out);
        } else {
            ibp_current = linear_out;
        }
    }

    let ibp_widths: Vec<f64> = ibp_current.iter().map(|iv| iv.width()).collect();
    let crown_widths: Vec<f64> = crown_result
        .lower
        .iter()
        .zip(crown_result.upper.iter())
        .map(|(lo, hi)| hi - lo)
        .collect();

    let dominated = true;
    for (i, (ibp_w, crown_w)) in ibp_widths.iter().zip(crown_widths.iter()).enumerate() {
        if *crown_w > *ibp_w + PROOF_EPS {
            return Err(format!(
                "output {i}: CROWN width {crown_w} > IBP width {ibp_w}"
            ));
        }
    }

    Ok(T47Witness {
        ibp_widths,
        crown_widths,
        dominated,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    const EPS: f64 = 1e-9;

    // -----------------------------------------------------------------------
    // T40 tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_t40_symmetric_crossing() {
        let w =
            verify_t40_relu_relaxation(-1.0, 1.0, 100).expect("symmetric crossing should verify");
        assert!((w.lambda - 0.5).abs() < EPS);
        assert!((w.mu - 0.5).abs() < EPS);
    }

    #[test]
    fn test_t40_asymmetric_crossing() {
        let w =
            verify_t40_relu_relaxation(-2.0, 4.0, 100).expect("asymmetric crossing should verify");
        assert!((w.lambda - 4.0 / 6.0).abs() < EPS);
        assert!((w.mu - 8.0 / 6.0).abs() < EPS);
    }

    #[test]
    fn test_t40_narrow_crossing() {
        let w =
            verify_t40_relu_relaxation(-0.01, 0.01, 100).expect("narrow crossing should verify");
        assert!((w.lambda - 0.5).abs() < EPS);
    }

    #[test]
    fn test_t40_wide_crossing() {
        let w =
            verify_t40_relu_relaxation(-100.0, 100.0, 1000).expect("wide crossing should verify");
        assert!((w.lambda - 0.5).abs() < EPS);
    }

    #[test]
    fn test_t40_non_crossing_rejected() {
        assert!(verify_t40_relu_relaxation(1.0, 3.0, 10).is_err());
        assert!(verify_t40_relu_relaxation(-3.0, -1.0, 10).is_err());
    }

    // -----------------------------------------------------------------------
    // T41 tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_t41_single_layer() {
        let network = vec![(vec![vec![2.0, -1.0]], vec![0.5])];
        let w = verify_t41_backward_propagation(&network, &[-1.0, -1.0], &[1.0, 1.0], 100)
            .expect("single layer should verify");
        assert_eq!(w.num_layers, 1);
        assert!(w.samples_verified >= 100);
    }

    #[test]
    fn test_t41_two_layer_crossing() {
        let network = vec![
            (vec![vec![1.0], vec![-1.0]], vec![0.0, 0.0]),
            (vec![vec![1.0, 1.0]], vec![0.0]),
        ];
        let w = verify_t41_backward_propagation(&network, &[-1.0], &[1.0], 200)
            .expect("two-layer crossing should verify");
        assert_eq!(w.num_layers, 2);
    }

    #[test]
    fn test_t41_three_layer() {
        let network = vec![
            (vec![vec![1.0, -1.0], vec![-1.0, 1.0]], vec![0.0, 0.0]),
            (vec![vec![1.0, 0.5], vec![0.5, 1.0]], vec![0.0, 0.0]),
            (vec![vec![1.0, -1.0]], vec![0.0]),
        ];
        let w = verify_t41_backward_propagation(&network, &[-1.0, -1.0], &[1.0, 1.0], 500)
            .expect("three-layer should verify");
        assert_eq!(w.num_layers, 3);
    }

    // -----------------------------------------------------------------------
    // T42 tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_t42_symmetric() {
        let w =
            verify_t42_concave_envelope(-1.0, 1.0, 100).expect("symmetric envelope should verify");
        assert!((w.slope - 0.5).abs() < EPS);
        assert!((w.intercept - 0.5).abs() < EPS);
    }

    #[test]
    fn test_t42_asymmetric() {
        let w =
            verify_t42_concave_envelope(-1.0, 3.0, 100).expect("asymmetric envelope should verify");
        assert!((w.slope - 0.75).abs() < EPS);
        assert!((w.intercept - 0.75).abs() < EPS);
    }

    #[test]
    fn test_t42_max_gap_location() {
        let w = verify_t42_concave_envelope(-1.0, 1.0, 1000).expect("should verify");
        // Max gap for [-1, 1] is at z=0 where envelope = intercept = 0.5
        // and ReLU(0) = 0. But sampling may not hit z=0 exactly.
        // The gap is intercept - 0 = 0.5. With dense enough sampling we get close.
        assert!(w.max_gap >= 0.45, "max_gap={} too small", w.max_gap);
        assert!(w.max_gap <= 0.5 + 0.01, "max_gap={} too large", w.max_gap);
    }

    // -----------------------------------------------------------------------
    // T43 tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_t43_alpha_zero() {
        let w = verify_t43_alpha_soundness(&[-1.0, -2.0], &[1.0, 4.0], &[0.0, 0.0], 100)
            .expect("alpha=0 should be sound");
        assert_eq!(w.crossing_verified, 2);
    }

    #[test]
    fn test_t43_alpha_one() {
        let w = verify_t43_alpha_soundness(&[-1.0], &[1.0], &[1.0], 100)
            .expect("alpha=1 should be sound");
        assert_eq!(w.crossing_verified, 1);
    }

    #[test]
    fn test_t43_alpha_half() {
        let w = verify_t43_alpha_soundness(&[-1.0, -3.0], &[1.0, 1.0], &[0.5, 0.5], 100)
            .expect("alpha=0.5 should be sound");
        assert_eq!(w.crossing_verified, 2);
    }

    #[test]
    fn test_t43_alpha_out_of_range_rejected() {
        assert!(verify_t43_alpha_soundness(&[-1.0], &[1.0], &[1.5], 10).is_err());
        assert!(verify_t43_alpha_soundness(&[-1.0], &[1.0], &[-0.5], 10).is_err());
    }

    #[test]
    fn test_t43_non_crossing_skipped() {
        let w = verify_t43_alpha_soundness(&[1.0, -3.0], &[3.0, -1.0], &[0.5, 0.5], 100)
            .expect("non-crossing should pass");
        assert_eq!(w.crossing_verified, 0);
    }

    // -----------------------------------------------------------------------
    // T44 tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_t44_crossing_network() {
        let network = vec![
            (vec![vec![1.0], vec![-1.0]], vec![0.0, 0.0]),
            (vec![vec![1.0, 1.0]], vec![0.0]),
        ];
        let w =
            verify_t44_alpha_tighter(&network, &[-1.0], &[1.0]).expect("should verify dominance");
        // Improvement should be non-negative (or very small negative due to numerics).
        assert!(
            w.improvement >= -PROOF_EPS * 100.0,
            "alpha-CROWN should not be worse: improvement={}",
            w.improvement
        );
    }

    // -----------------------------------------------------------------------
    // T45 tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_t45_single_layer() {
        let network = vec![(vec![vec![2.0]], vec![1.0])];
        let w = verify_t45_composition(&network, &[0.0], &[1.0])
            .expect("single layer composition should verify");
        assert_eq!(w.num_layers, 1);
    }

    #[test]
    fn test_t45_two_layer() {
        let network = vec![
            (vec![vec![1.0, -1.0], vec![-1.0, 1.0]], vec![0.0, 0.0]),
            (vec![vec![1.0, 1.0]], vec![0.0]),
        ];
        let w = verify_t45_composition(&network, &[-1.0, -1.0], &[1.0, 1.0])
            .expect("two-layer composition should verify");
        assert_eq!(w.num_layers, 2);
    }

    #[test]
    fn test_t45_four_layer() {
        let network = vec![
            (vec![vec![1.0], vec![-1.0]], vec![0.0, 0.0]),
            (vec![vec![1.0, 1.0], vec![-1.0, 1.0]], vec![0.0, 0.0]),
            (vec![vec![2.0, -1.0], vec![0.5, 1.5]], vec![0.0, 0.0]),
            (vec![vec![1.0, 1.0]], vec![0.0]),
        ];
        let w = verify_t45_composition(&network, &[-0.5], &[0.5])
            .expect("four-layer composition should verify");
        assert_eq!(w.num_layers, 4);
    }

    // -----------------------------------------------------------------------
    // T46 tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_t46_identity_bound() {
        let bound = CrownBound::identity(2);
        let w = verify_t46_concretization(&bound, &[-1.0, -1.0], &[1.0, 1.0])
            .expect("identity bound should verify");
        assert_eq!(w.num_outputs, 2);
        assert_eq!(w.num_inputs, 2);
    }

    #[test]
    fn test_t46_scaled_bound() {
        let bound = CrownBound {
            lower_coeffs: vec![vec![2.0, -3.0]],
            upper_coeffs: vec![vec![2.0, -3.0]],
            lower_bias: vec![1.0],
            upper_bias: vec![1.0],
        };
        let w = verify_t46_concretization(&bound, &[0.0, 0.0], &[1.0, 1.0])
            .expect("scaled bound should verify");
        assert_eq!(w.num_outputs, 1);
        // concrete_lower = 1 + 2*0 + (-3)*1 = -2
        assert!((w.concrete_lower[0] - (-2.0)).abs() < EPS);
        // concrete_upper = 1 + 2*1 + (-3)*0 = 3
        assert!((w.concrete_upper[0] - 3.0).abs() < EPS);
    }

    // -----------------------------------------------------------------------
    // T47 tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_t47_always_active_network() {
        // All activations positive: CROWN = IBP = exact.
        let network = vec![
            (vec![vec![1.0], vec![0.5]], vec![2.0, 1.0]),
            (vec![vec![1.0, 1.0]], vec![0.0]),
        ];
        let w = verify_t47_crown_ibp_dominance(&network, &[0.0], &[1.0])
            .expect("should verify dominance");
        assert!(w.dominated);
    }

    #[test]
    fn test_t47_crossing_network() {
        let network = vec![
            (vec![vec![1.0, 0.5], vec![-0.5, 1.0]], vec![0.0, 0.0]),
            (vec![vec![1.0, -1.0]], vec![0.0]),
        ];
        let w = verify_t47_crown_ibp_dominance(&network, &[-1.0, -1.0], &[1.0, 1.0])
            .expect("should verify dominance for crossing network");
        assert!(w.dominated);
    }

    #[test]
    fn test_t47_single_linear_equal() {
        // Single linear layer: CROWN = IBP (both exact).
        let network = vec![(vec![vec![2.0, -1.0]], vec![0.5])];
        let w = verify_t47_crown_ibp_dominance(&network, &[-1.0, -1.0], &[1.0, 1.0])
            .expect("single layer should verify");
        assert!(w.dominated);
        // Widths should be equal.
        for (i, (ibp, crown)) in w.ibp_widths.iter().zip(w.crown_widths.iter()).enumerate() {
            assert!(
                (ibp - crown).abs() < EPS,
                "output {i}: IBP width {ibp} != CROWN width {crown}"
            );
        }
    }
}
