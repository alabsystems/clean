// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! ReLU stability analysis: classify neurons, count stable patterns,
//! and compute relaxation gap ratios.
//!
//! A ReLU neuron with pre-activation bounds `[l, u]` is:
//! - **StablyActive**: `l > 0` -- ReLU is identity, exact output `[l, u]`
//! - **StablyInactive**: `u < 0` -- ReLU is zero, exact output `[0, 0]`
//! - **Unstable**: `l <= 0 <= u` -- crossing region, requires relaxation
//!
//! For stable neurons, verification is exact (no relaxation gap). The
//! fraction of stable neurons in a network directly determines
//! verification precision.

use super::super::ibp_crown::Interval;

/// Classification of a single neuron's stability under perturbation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum NeuronStability {
    /// Pre-activation lower bound > 0: ReLU always outputs the input.
    StablyActive,
    /// Pre-activation upper bound < 0: ReLU always outputs zero.
    StablyInactive,
    /// Pre-activation bounds cross zero: relaxation required.
    Unstable,
}

impl NeuronStability {
    /// Returns `true` if the neuron is stable (either active or inactive).
    #[must_use]
    pub fn is_stable(self) -> bool {
        matches!(self, Self::StablyActive | Self::StablyInactive)
    }
}

/// Classify a neuron given its pre-activation interval bounds.
///
/// Uses strict inequality for stability: `l > 0` (not `l >= 0`) for
/// StablyActive, and `u < 0` (not `u <= 0`) for StablyInactive. This
/// matches the C012 criterion where stability requires the bounds to
/// strictly not cross zero, ensuring robustness to small perturbations.
#[must_use]
pub fn classify_neuron(bounds: Interval) -> NeuronStability {
    if bounds.lower > 0.0 {
        NeuronStability::StablyActive
    } else if bounds.upper < 0.0 {
        NeuronStability::StablyInactive
    } else {
        NeuronStability::Unstable
    }
}

/// Analyze stability of all neurons in a single layer.
///
/// Takes pre-activation bounds for each neuron in the layer and returns
/// their stability classifications.
#[must_use]
pub fn analyze_layer_stability(pre_activation_bounds: &[Interval]) -> Vec<NeuronStability> {
    pre_activation_bounds
        .iter()
        .map(|&b| classify_neuron(b))
        .collect()
}

/// Compute the exact ReLU output interval for a stable neuron.
///
/// For stable neurons, the output is exact (no relaxation needed):
/// - StablyActive: output = input bounds `[l, u]`
/// - StablyInactive: output = `[0, 0]`
/// - Unstable: returns `None` (caller must use relaxation)
#[must_use]
pub fn exact_relu_output(bounds: Interval) -> Option<Interval> {
    match classify_neuron(bounds) {
        NeuronStability::StablyActive => Some(bounds),
        NeuronStability::StablyInactive => Some(Interval::new(0.0, 0.0)),
        NeuronStability::Unstable => None,
    }
}

/// Compute the relaxation gap for a single unstable neuron.
///
/// For a crossing interval `[l, u]` with `l < 0 < u`, the lambda-relaxation
/// overapproximation has a triangle gap with area `|l| * u / (2 * (u - l))`.
/// This represents the overestimation introduced by linear relaxation.
///
/// Returns 0.0 for stable neurons (no gap).
#[must_use]
pub fn neuron_relaxation_gap(bounds: Interval) -> f64 {
    match classify_neuron(bounds) {
        NeuronStability::StablyActive | NeuronStability::StablyInactive => 0.0,
        NeuronStability::Unstable => {
            let l = bounds.lower;
            let u = bounds.upper;
            // Triangle gap area from lambda-relaxation
            // The gap is the area between the upper relaxation line and the
            // true ReLU function over [l, 0], which forms a triangle.
            (-l) * u / (2.0 * (u - l))
        }
    }
}

/// Compute the relaxation gap ratio for a network layer.
///
/// Returns the ratio of total relaxation gap to total output width.
/// A ratio of 0.0 means all neurons are stable (exact verification).
/// Higher ratios indicate more overestimation from unstable neurons.
///
/// Returns 0.0 if all neurons are stable or if total width is zero.
#[must_use]
pub fn relaxation_gap_ratio(pre_activation_bounds: &[Interval]) -> f64 {
    let total_gap: f64 = pre_activation_bounds
        .iter()
        .map(|&b| neuron_relaxation_gap(b))
        .sum();

    let total_width: f64 = pre_activation_bounds
        .iter()
        .map(|&b| {
            match classify_neuron(b) {
                NeuronStability::StablyActive => b.upper - b.lower,
                NeuronStability::StablyInactive => 0.0,
                NeuronStability::Unstable => b.upper, // ReLU output range is [0, u]
            }
        })
        .sum();

    if total_width < f64::EPSILON {
        return 0.0;
    }

    total_gap / total_width
}

/// Summary report for network-wide stability analysis.
#[derive(Debug, Clone, PartialEq)]
pub struct NetworkStabilityReport {
    /// Total number of ReLU neurons across all layers.
    pub total_neurons: usize,
    /// Number of stably active neurons (l > 0).
    pub stably_active: usize,
    /// Number of stably inactive neurons (u < 0).
    pub stably_inactive: usize,
    /// Number of unstable (crossing) neurons.
    pub unstable: usize,
    /// Per-layer stability counts: `(stably_active, stably_inactive, unstable)`.
    pub per_layer: Vec<(usize, usize, usize)>,
    /// Fraction of stable neurons (0.0 to 1.0).
    pub stability_ratio: f64,
    /// Total relaxation gap across all unstable neurons.
    pub total_relaxation_gap: f64,
    /// Whether all neurons are stable (enabling exact verification).
    pub is_exact: bool,
}

/// Analyzer for computing stability across a multi-layer network.
///
/// Accumulates pre-activation bounds for each layer and produces a
/// [`NetworkStabilityReport`].
#[derive(Debug, Clone, Default)]
pub struct StabilityAnalyzer {
    /// Pre-activation bounds per layer. Each inner `Vec` has one
    /// `Interval` per neuron in that layer.
    layers: Vec<Vec<Interval>>,
}

impl StabilityAnalyzer {
    /// Create a new empty analyzer.
    #[must_use]
    pub fn new() -> Self {
        Self { layers: Vec::new() }
    }

    /// Add a layer's pre-activation bounds.
    pub fn add_layer(&mut self, bounds: Vec<Interval>) {
        self.layers.push(bounds);
    }

    /// Compute the full network stability report.
    #[must_use]
    pub fn analyze(&self) -> NetworkStabilityReport {
        let mut total_neurons = 0;
        let mut stably_active = 0;
        let mut stably_inactive = 0;
        let mut unstable = 0;
        let mut total_gap = 0.0;
        let mut per_layer = Vec::with_capacity(self.layers.len());

        for layer_bounds in &self.layers {
            let classifications = analyze_layer_stability(layer_bounds);
            let mut la = 0usize;
            let mut li = 0usize;
            let mut lu = 0usize;

            for &c in &classifications {
                match c {
                    NeuronStability::StablyActive => la += 1,
                    NeuronStability::StablyInactive => li += 1,
                    NeuronStability::Unstable => lu += 1,
                }
            }

            for &b in layer_bounds {
                total_gap += neuron_relaxation_gap(b);
            }

            total_neurons += classifications.len();
            stably_active += la;
            stably_inactive += li;
            unstable += lu;
            per_layer.push((la, li, lu));
        }

        let stability_ratio = if total_neurons > 0 {
            (stably_active + stably_inactive) as f64 / total_neurons as f64
        } else {
            1.0
        };

        NetworkStabilityReport {
            total_neurons,
            stably_active,
            stably_inactive,
            unstable,
            per_layer,
            stability_ratio,
            total_relaxation_gap: total_gap,
            is_exact: unstable == 0,
        }
    }
}

/// Analyze stability for a full network given per-layer pre-activation bounds.
///
/// Convenience function that wraps [`StabilityAnalyzer`].
#[must_use]
pub fn analyze_network_stability(layers: &[Vec<Interval>]) -> NetworkStabilityReport {
    let mut analyzer = StabilityAnalyzer::new();
    for layer in layers {
        analyzer.add_layer(layer.clone());
    }
    analyzer.analyze()
}
