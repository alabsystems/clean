// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! CROWN vs IBP Tightness Analysis
//!
//! Compares bound tightness of IBP (Interval Bound Propagation) against CROWN
//! (backward linear relaxation). IBP loses inter-neuron correlation at each
//! layer; CROWN preserves it via backward linear bounds, yielding tighter
//! output intervals. The gap appears only at crossing ReLU neurons (l < 0 < u).

use super::crown_backward::verify_crown_bounds;
use super::ibp::{IbpLinearSpec, IbpReluSpec, Interval};

/// Activation type for a neuron, determined by pre-activation interval.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ActivationStatus {
    /// Pre-activation interval is entirely non-negative: ReLU is identity.
    AlwaysActive,
    /// Pre-activation interval is entirely non-positive: ReLU is zero.
    AlwaysInactive,
    /// Pre-activation interval crosses zero: ReLU is nonlinear.
    Crossing,
}

/// Per-layer tightness comparison between IBP and CROWN bounds.
#[derive(Debug, Clone)]
pub struct LayerTightness {
    /// Layer index (0-based, after each linear+ReLU block).
    pub layer_index: usize,
    /// IBP interval width per output dimension.
    pub ibp_widths: Vec<f64>,
    /// CROWN interval width per output dimension (populated only at output layer).
    pub crown_widths: Vec<f64>,
    /// Per-dimension tightness ratio: CROWN_width / IBP_width.
    /// NaN if IBP_width is zero (point interval). 1.0 for hidden layers.
    pub ratios: Vec<f64>,
    /// Activation status per neuron at this layer (pre-ReLU classification).
    pub activations: Vec<ActivationStatus>,
}

impl LayerTightness {
    /// Number of crossing neurons at this layer.
    #[must_use]
    pub fn crossing_count(&self) -> usize {
        self.activations
            .iter()
            .filter(|a| **a == ActivationStatus::Crossing)
            .count()
    }

    /// Mean tightness ratio across dimensions (excluding NaN entries).
    #[must_use]
    pub fn mean_ratio(&self) -> f64 {
        let valid: Vec<f64> = self
            .ratios
            .iter()
            .copied()
            .filter(|r| r.is_finite())
            .collect();
        if valid.is_empty() {
            return 1.0;
        }
        valid.iter().sum::<f64>() / valid.len() as f64
    }

    /// Minimum tightness ratio (best CROWN advantage).
    #[must_use]
    pub fn min_ratio(&self) -> f64 {
        self.ratios
            .iter()
            .copied()
            .filter(|r| r.is_finite())
            .fold(f64::INFINITY, f64::min)
    }
}

/// Full tightness report comparing IBP and CROWN across all layers.
#[derive(Debug, Clone)]
pub struct TightnessReport {
    /// Per-layer tightness data.
    pub layers: Vec<LayerTightness>,
    /// Final output IBP bounds.
    pub output_ibp: Vec<Interval>,
    /// Final output CROWN bounds.
    pub output_crown: Vec<Interval>,
    /// Overall mean tightness ratio at the output layer.
    pub overall_ratio: f64,
    /// Total crossing neurons across all layers.
    pub total_crossing: usize,
}

/// Classify a neuron's activation status from its pre-activation interval.
fn classify_activation(pre_act: &Interval) -> ActivationStatus {
    if pre_act.lower >= 0.0 {
        ActivationStatus::AlwaysActive
    } else if pre_act.upper <= 0.0 {
        ActivationStatus::AlwaysInactive
    } else {
        ActivationStatus::Crossing
    }
}

/// Compare IBP and CROWN bound tightness on a ReLU network.
/// `layers` is (weight_matrix, bias) per layer; hidden layers get ReLU, final is linear-only.
#[must_use]
pub fn compare_ibp_crown(
    layers: &[(Vec<Vec<f64>>, Vec<f64>)],
    input_lower: &[f64],
    input_upper: &[f64],
) -> TightnessReport {
    let linear = IbpLinearSpec::new();
    let relu = IbpReluSpec::new();

    // IBP forward pass, collecting per-layer data.
    let mut ibp_current: Vec<Interval> = input_lower
        .iter()
        .zip(input_upper.iter())
        .map(|(&l, &u)| Interval::new(l, u))
        .collect();

    let mut layer_data: Vec<(Vec<ActivationStatus>, Vec<Interval>)> =
        Vec::with_capacity(layers.len());

    for (i, (weights, bias)) in layers.iter().enumerate() {
        let pre_relu = linear.propagate(weights, bias, &ibp_current);

        if i < layers.len() - 1 {
            // Hidden layer: classify activations based on pre-ReLU bounds.
            let activations: Vec<ActivationStatus> =
                pre_relu.iter().map(classify_activation).collect();
            let post_relu = relu.propagate_vector(&pre_relu);
            layer_data.push((activations, post_relu.clone()));
            ibp_current = post_relu;
        } else {
            // Output layer: no ReLU applied, so no activation to classify.
            let activations = vec![ActivationStatus::AlwaysActive; pre_relu.len()];
            layer_data.push((activations, pre_relu.clone()));
            ibp_current = pre_relu;
        }
    }

    let ibp_output = ibp_current;

    // CROWN backward pass via the existing verify_crown_bounds.
    let crown_result = verify_crown_bounds(layers, input_lower, input_upper);
    let crown_output: Vec<Interval> = crown_result
        .lower
        .iter()
        .zip(crown_result.upper.iter())
        .map(|(&l, &u)| {
            // Numerical guard: ensure lower <= upper
            if l <= u {
                Interval::new(l, u)
            } else {
                Interval::new(u, u)
            }
        })
        .collect();

    // Build per-layer tightness report.
    let mut layers_report = Vec::with_capacity(layer_data.len());
    for (i, (activations, ibp_bounds)) in layer_data.iter().enumerate() {
        if i == layer_data.len() - 1 {
            // Output layer: compare IBP vs CROWN.
            let ibp_widths: Vec<f64> = ibp_bounds.iter().map(Interval::width).collect();
            let crown_widths: Vec<f64> = crown_output.iter().map(Interval::width).collect();
            let ratios: Vec<f64> = ibp_widths
                .iter()
                .zip(crown_widths.iter())
                .map(|(&iw, &cw)| {
                    if iw.abs() < 1e-15 {
                        if cw.abs() < 1e-15 {
                            1.0
                        } else {
                            f64::NAN
                        }
                    } else {
                        cw / iw
                    }
                })
                .collect();

            layers_report.push(LayerTightness {
                layer_index: i,
                ibp_widths,
                crown_widths,
                ratios,
                activations: activations.clone(),
            });
        } else {
            // Hidden layer: IBP only (CROWN gives end-to-end bounds, not per-layer).
            let ibp_widths: Vec<f64> = ibp_bounds.iter().map(Interval::width).collect();
            layers_report.push(LayerTightness {
                layer_index: i,
                ibp_widths: ibp_widths.clone(),
                crown_widths: ibp_widths.clone(),
                ratios: vec![1.0; ibp_bounds.len()],
                activations: activations.clone(),
            });
        }
    }

    let total_crossing: usize = layers_report
        .iter()
        .map(LayerTightness::crossing_count)
        .sum();
    let overall_ratio = layers_report
        .last()
        .map(LayerTightness::mean_ratio)
        .unwrap_or(1.0);

    TightnessReport {
        layers: layers_report,
        output_ibp: ibp_output,
        output_crown: crown_output,
        overall_ratio,
        total_crossing,
    }
}

/// Estimate true output bounds via Monte Carlo sampling and corner evaluation.
/// Returns (estimated_lower, estimated_upper) approaching true bounds from inside.
#[must_use]
pub fn best_possible_bounds(
    layers: &[(Vec<Vec<f64>>, Vec<f64>)],
    input_lower: &[f64],
    input_upper: &[f64],
    samples: usize,
) -> (Vec<f64>, Vec<f64>) {
    let input_dim = input_lower.len();
    let output_dim = layers.last().map(|(w, _)| w.len()).unwrap_or(0);

    let mut best_lower = vec![f64::INFINITY; output_dim];
    let mut best_upper = vec![f64::NEG_INFINITY; output_dim];

    // Deterministic LCG for reproducibility.
    let mut rng_state: u64 = 42;
    let lcg_next = |state: &mut u64| -> f64 {
        *state = state
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1);
        (*state >> 33) as f64 / (1u64 << 31) as f64
    };

    for _ in 0..samples {
        let mut x: Vec<f64> = Vec::with_capacity(input_dim);
        for d in 0..input_dim {
            let t = lcg_next(&mut rng_state);
            x.push(input_lower[d] + t * (input_upper[d] - input_lower[d]));
        }

        let output = eval_network(layers, &x);
        for (j, &val) in output.iter().enumerate() {
            if val < best_lower[j] {
                best_lower[j] = val;
            }
            if val > best_upper[j] {
                best_upper[j] = val;
            }
        }
    }

    // Evaluate corner points for small dimensions.
    if input_dim <= 10 {
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
            let output = eval_network(layers, &x);
            for (j, &val) in output.iter().enumerate() {
                if val < best_lower[j] {
                    best_lower[j] = val;
                }
                if val > best_upper[j] {
                    best_upper[j] = val;
                }
            }
        }
    }

    (best_lower, best_upper)
}

/// Evaluate a ReLU network on a concrete input vector.
///
/// Each layer applies y = Wx + b. Hidden layers (all except the last) apply
/// element-wise ReLU after the affine transform.
#[must_use]
pub fn eval_network(layers: &[(Vec<Vec<f64>>, Vec<f64>)], input: &[f64]) -> Vec<f64> {
    let mut current = input.to_vec();
    for (i, (weights, bias)) in layers.iter().enumerate() {
        let mut next = Vec::with_capacity(weights.len());
        for (row, b) in weights.iter().zip(bias.iter()) {
            let val: f64 = row
                .iter()
                .zip(current.iter())
                .map(|(w, x)| w * x)
                .sum::<f64>()
                + b;
            next.push(val);
        }
        if i < layers.len() - 1 {
            for v in &mut next {
                *v = v.max(0.0);
            }
        }
        current = next;
    }
    current
}

/// Verify that CROWN bounds are at least as tight as IBP bounds at every
/// output dimension.
///
/// Returns `true` if CROWN_width <= IBP_width + epsilon for all dimensions.
#[must_use]
pub fn verify_crown_tighter_than_ibp(report: &TightnessReport) -> bool {
    let eps = 1e-10;
    report
        .output_crown
        .iter()
        .zip(report.output_ibp.iter())
        .all(|(crown, ibp)| crown.width() <= ibp.width() + eps)
}

// ---------------------------------------------------------------------------
// Per-interval tightness analysis
// ---------------------------------------------------------------------------

/// Measures how much tighter CROWN bounds are compared to IBP bounds.
#[derive(Debug, Clone, PartialEq)]
#[non_exhaustive]
pub struct TightnessGap {
    /// Absolute gap: IBP_width - CROWN_width.
    pub absolute: f64,
    /// Relative gap: 1.0 - (CROWN_width / IBP_width). NaN if IBP_width is zero.
    pub relative: f64,
    /// Width of the IBP interval.
    pub ibp_width: f64,
    /// Width of the CROWN interval.
    pub crown_width: f64,
}

/// Per-layer tightness metrics aggregated across all neurons.
#[derive(Debug, Clone, PartialEq)]
#[non_exhaustive]
pub struct LayerProfile {
    /// Per-neuron tightness gaps.
    pub gaps: Vec<TightnessGap>,
    /// Fraction of neurons whose bounds cross zero (l < 0 < u).
    pub crossing_ratio: f64,
    /// Mean interval width across all neurons in the layer.
    pub mean_width: f64,
}

/// Descriptive statistics for interval widths across a set of neurons.
#[derive(Debug, Clone, PartialEq)]
#[non_exhaustive]
pub struct WidthStats {
    /// Minimum width.
    pub min: f64,
    /// Maximum width.
    pub max: f64,
    /// Arithmetic mean width.
    pub mean: f64,
    /// Median width.
    pub median: f64,
    /// Number of neurons.
    pub count: usize,
}

/// Compute the tightness gap between IBP and CROWN bounds for a single dimension.
///
/// A positive `absolute` gap means CROWN is tighter (smaller width).
/// A `relative` value near 1.0 means CROWN is much tighter; 0.0 means identical.
#[must_use]
pub fn compute_tightness_gap(ibp_bounds: &Interval, crown_bounds: &Interval) -> TightnessGap {
    let ibp_w = ibp_bounds.width();
    let crown_w = crown_bounds.width();
    let absolute = ibp_w - crown_w;
    let relative = if ibp_w.abs() < 1e-15 {
        if crown_w.abs() < 1e-15 {
            0.0
        } else {
            f64::NAN
        }
    } else {
        1.0 - crown_w / ibp_w
    };
    TightnessGap {
        absolute,
        relative,
        ibp_width: ibp_w,
        crown_width: crown_w,
    }
}

/// Build a per-layer tightness profile comparing IBP and CROWN bounds neuron-by-neuron.
///
/// Both slices must have equal length (one entry per neuron).
/// Uses IBP bounds for the crossing ratio and mean width computation.
#[must_use]
pub fn layer_tightness_profile(layer_ibp: &[Interval], layer_crown: &[Interval]) -> LayerProfile {
    let n = layer_ibp.len();
    let gaps: Vec<TightnessGap> = layer_ibp
        .iter()
        .zip(layer_crown.iter())
        .map(|(ibp, crown)| compute_tightness_gap(ibp, crown))
        .collect();

    let crossing = crossing_neuron_ratio(layer_ibp);

    let mean_width = if n == 0 {
        0.0
    } else {
        layer_ibp.iter().map(Interval::width).sum::<f64>() / n as f64
    };

    LayerProfile {
        gaps,
        crossing_ratio: crossing,
        mean_width,
    }
}

/// Fraction of neurons whose pre-activation bounds cross zero (lower < 0 < upper).
///
/// Returns 0.0 for an empty slice.
#[must_use]
pub fn crossing_neuron_ratio(bounds: &[Interval]) -> f64 {
    if bounds.is_empty() {
        return 0.0;
    }
    let crossing_count = bounds
        .iter()
        .filter(|b| b.lower < 0.0 && b.upper > 0.0)
        .count();
    crossing_count as f64 / bounds.len() as f64
}

/// Compute descriptive statistics (min, max, mean, median) of interval widths.
///
/// Returns a `WidthStats` with all fields set to 0.0 and count=0 for empty input.
#[must_use]
pub fn bound_width_statistics(bounds: &[Interval]) -> WidthStats {
    if bounds.is_empty() {
        return WidthStats {
            min: 0.0,
            max: 0.0,
            mean: 0.0,
            median: 0.0,
            count: 0,
        };
    }
    let mut widths: Vec<f64> = bounds.iter().map(Interval::width).collect();
    let n = widths.len();
    let sum: f64 = widths.iter().sum();
    let mean = sum / n as f64;

    // Sort for min/max/median.
    widths.sort_by(|a, b| a.partial_cmp(b).unwrap_or(std::cmp::Ordering::Equal));
    let min = widths[0];
    let max = widths[n - 1];
    let median = if n % 2 == 1 {
        widths[n / 2]
    } else {
        (widths[n / 2 - 1] + widths[n / 2]) / 2.0
    };

    WidthStats {
        min,
        max,
        mean,
        median,
        count: n,
    }
}

/// Verify that CROWN bounds are contained within IBP bounds (CROWN is tighter).
///
/// Returns `true` when `crown.lower >= ibp.lower - eps` and `crown.upper <= ibp.upper + eps`
/// and `crown.width() <= ibp.width() + eps`.
#[must_use]
pub fn verify_crown_tighter(ibp: &Interval, crown: &Interval) -> bool {
    let eps = 1e-10;
    crown.lower >= ibp.lower - eps
        && crown.upper <= ibp.upper + eps
        && crown.width() <= ibp.width() + eps
}

/// Track tightness improvement ratio across layers.
///
/// For each consecutive pair of `LayerProfile`s, computes the ratio of
/// the current layer's mean tightness gap to the previous layer's.
/// Specifically: `mean_relative_gap[i] / mean_relative_gap[i-1]`.
///
/// A value > 1.0 indicates tightness improvement is accelerating through
/// deeper layers (common in networks with many crossing neurons).
/// Returns a vector of length `max(0, layer_profiles.len() - 1)`.
#[must_use]
pub fn tightness_improvement_chain(layer_profiles: &[LayerProfile]) -> Vec<f64> {
    if layer_profiles.len() < 2 {
        return Vec::new();
    }
    let mean_gaps: Vec<f64> = layer_profiles
        .iter()
        .map(|lp| {
            if lp.gaps.is_empty() {
                return 0.0;
            }
            let finite: Vec<f64> = lp
                .gaps
                .iter()
                .map(|g| g.relative)
                .filter(|r| r.is_finite())
                .collect();
            if finite.is_empty() {
                0.0
            } else {
                finite.iter().sum::<f64>() / finite.len() as f64
            }
        })
        .collect();

    mean_gaps
        .windows(2)
        .map(|w| {
            if w[0].abs() < 1e-15 {
                if w[1].abs() < 1e-15 {
                    1.0
                } else {
                    f64::INFINITY
                }
            } else {
                w[1] / w[0]
            }
        })
        .collect()
}
