// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Layer-by-layer diagnostics for the NN verification pipeline.
//!
//! Tracks bound amplification, identifies bottleneck layers, and suggests
//! which verification method (IBP, CROWN, alpha-CROWN, McCormick) to apply
//! at each layer for optimal tightness. Used by gamma-crown integration
//! to guide adaptive verification strategies.

use std::fmt;

// ---------------------------------------------------------------------------
// Enums
// ---------------------------------------------------------------------------

/// Classification of a neural network layer for diagnostic purposes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum LayerType {
    /// Fully-connected affine transform.
    Linear,
    /// Rectified linear unit activation.
    ReLU,
    /// Convolutional layer.
    Conv,
    /// Layer normalization.
    LayerNorm,
    /// Self-attention or multi-head attention.
    Attention,
    /// Residual (skip) connection.
    Residual,
}

impl fmt::Display for LayerType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Linear => write!(f, "Linear"),
            Self::ReLU => write!(f, "ReLU"),
            Self::Conv => write!(f, "Conv"),
            Self::LayerNorm => write!(f, "LayerNorm"),
            Self::Attention => write!(f, "Attention"),
            Self::Residual => write!(f, "Residual"),
        }
    }
}

/// Verification method applicable to a layer.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum VerificationMethod {
    /// Interval Bound Propagation (fast, loose).
    IBP,
    /// CROWN backward-mode linear relaxation.
    CROWN,
    /// alpha-CROWN with optimized relaxation slopes.
    AlphaCROWN,
    /// McCormick envelope relaxation for bilinear terms.
    McCormick,
}

impl fmt::Display for VerificationMethod {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::IBP => write!(f, "IBP"),
            Self::CROWN => write!(f, "CROWN"),
            Self::AlphaCROWN => write!(f, "alpha-CROWN"),
            Self::McCormick => write!(f, "McCormick"),
        }
    }
}

// ---------------------------------------------------------------------------
// Diagnostic structs
// ---------------------------------------------------------------------------

/// Per-layer diagnostic metrics from bound propagation.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct LayerDiagnostic {
    /// Index of this layer in the network.
    pub layer_idx: usize,
    /// Classification of the layer type.
    pub layer_type: LayerType,
    /// Sum of input interval widths.
    pub input_width: f64,
    /// Sum of output interval widths.
    pub output_width: f64,
    /// Ratio of output width to input width (>1 means bounds expand).
    pub amplification: f64,
    /// Number of neurons whose pre-activation bounds cross zero (ReLU
    /// instability source).
    pub crossing_neurons: usize,
    /// Total neurons in this layer.
    pub total_neurons: usize,
}

/// Aggregated diagnostics across an entire verification pipeline.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct PipelineDiagnostic {
    /// Per-layer diagnostics in order.
    pub layers: Vec<LayerDiagnostic>,
    /// Product of per-layer amplifications.
    pub total_amplification: f64,
    /// Index of the layer with the highest amplification.
    pub bottleneck_layer: usize,
    /// Index of the layer with the lowest amplification (tightest bounds).
    pub tightest_layer: usize,
}

/// Report identifying the worst amplification bottleneck.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct BottleneckReport {
    /// Index of the bottleneck layer.
    pub layer_idx: usize,
    /// Amplification factor at the bottleneck.
    pub amplification: f64,
    /// Type of the bottleneck layer.
    pub layer_type: LayerType,
}

/// Suggestion to switch verification method for a specific layer.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct TighteningTarget {
    /// Layer to re-verify with a different method.
    pub layer_idx: usize,
    /// Current (presumably looser) method.
    pub current_method: VerificationMethod,
    /// Suggested (presumably tighter) method.
    pub suggested_method: VerificationMethod,
    /// Estimated improvement factor (0.0..1.0 where lower means tighter).
    pub expected_improvement: f64,
}

// ---------------------------------------------------------------------------
// Amplification thresholds
// ---------------------------------------------------------------------------

/// Layers with amplification above this are candidates for CROWN.
const CROWN_THRESHOLD: f64 = 2.0;
/// Layers with amplification above this are candidates for alpha-CROWN.
const ALPHA_CROWN_THRESHOLD: f64 = 5.0;
/// McCormick is suggested for attention/layernorm with high amplification.
const MCCORMICK_THRESHOLD: f64 = 3.0;

// ---------------------------------------------------------------------------
// Core functions
// ---------------------------------------------------------------------------

/// Compute diagnostic metrics for a single layer.
///
/// `input_bounds` and `output_bounds` are slices of `(lower, upper)` pairs
/// for each neuron dimension.
#[must_use]
pub fn compute_layer_diagnostic(
    input_bounds: &[(f64, f64)],
    output_bounds: &[(f64, f64)],
    layer_idx: usize,
    layer_type: LayerType,
) -> LayerDiagnostic {
    let input_width: f64 = input_bounds.iter().map(|(lo, hi)| hi - lo).sum();
    let output_width: f64 = output_bounds.iter().map(|(lo, hi)| hi - lo).sum();
    let amplification = if input_width > 0.0 {
        output_width / input_width
    } else {
        // Degenerate: point inputs produce zero-width; avoid NaN.
        if output_width > 0.0 {
            f64::INFINITY
        } else {
            1.0
        }
    };

    let crossing_neurons = output_bounds
        .iter()
        .filter(|(lo, hi)| *lo < 0.0 && *hi > 0.0)
        .count();

    let total_neurons = output_bounds.len();

    LayerDiagnostic {
        layer_idx,
        layer_type,
        input_width,
        output_width,
        amplification,
        crossing_neurons,
        total_neurons,
    }
}

/// Aggregate per-layer diagnostics into a pipeline-level summary.
///
/// # Panics
///
/// Panics if `layer_diagnostics` is empty.
#[must_use]
pub fn compute_pipeline_diagnostic(layer_diagnostics: &[LayerDiagnostic]) -> PipelineDiagnostic {
    assert!(
        !layer_diagnostics.is_empty(),
        "cannot compute pipeline diagnostic from empty layer list"
    );

    let total_amplification = layer_diagnostics.iter().map(|d| d.amplification).product();

    let bottleneck_layer = layer_diagnostics
        .iter()
        .enumerate()
        .max_by(|(_, a), (_, b)| {
            a.amplification
                .partial_cmp(&b.amplification)
                .unwrap_or(std::cmp::Ordering::Equal)
        })
        .map(|(i, _)| i)
        .unwrap_or(0);

    let tightest_layer = layer_diagnostics
        .iter()
        .enumerate()
        .min_by(|(_, a), (_, b)| {
            a.amplification
                .partial_cmp(&b.amplification)
                .unwrap_or(std::cmp::Ordering::Equal)
        })
        .map(|(i, _)| i)
        .unwrap_or(0);

    PipelineDiagnostic {
        layers: layer_diagnostics.to_vec(),
        total_amplification,
        bottleneck_layer,
        tightest_layer,
    }
}

/// Identify the layer with the worst bound amplification.
#[must_use]
pub fn identify_bottleneck(diagnostics: &PipelineDiagnostic) -> BottleneckReport {
    let layer = &diagnostics.layers[diagnostics.bottleneck_layer];
    BottleneckReport {
        layer_idx: layer.layer_idx,
        amplification: layer.amplification,
        layer_type: layer.layer_type,
    }
}

/// Suggest which layers to re-verify with tighter methods.
///
/// Heuristic rules:
/// - High-amplification linear/ReLU layers: suggest CROWN or alpha-CROWN.
/// - High-amplification attention/layernorm: suggest McCormick.
/// - Low-amplification layers are left on IBP (cheapest).
#[must_use]
pub fn suggest_tightening_targets(diagnostics: &PipelineDiagnostic) -> Vec<TighteningTarget> {
    let mut targets = Vec::new();

    for layer in &diagnostics.layers {
        if layer.amplification <= CROWN_THRESHOLD {
            continue;
        }

        let (suggested, improvement) = match layer.layer_type {
            LayerType::Attention | LayerType::LayerNorm => {
                if layer.amplification > MCCORMICK_THRESHOLD {
                    (
                        VerificationMethod::McCormick,
                        estimate_mccormick_improvement(layer),
                    )
                } else {
                    (VerificationMethod::CROWN, estimate_crown_improvement(layer))
                }
            }
            _ => {
                if layer.amplification > ALPHA_CROWN_THRESHOLD {
                    (
                        VerificationMethod::AlphaCROWN,
                        estimate_alpha_crown_improvement(layer),
                    )
                } else {
                    (VerificationMethod::CROWN, estimate_crown_improvement(layer))
                }
            }
        };

        targets.push(TighteningTarget {
            layer_idx: layer.layer_idx,
            current_method: VerificationMethod::IBP,
            suggested_method: suggested,
            expected_improvement: improvement,
        });
    }

    // Sort by expected improvement (best improvement first).
    targets.sort_by(|a, b| {
        a.expected_improvement
            .partial_cmp(&b.expected_improvement)
            .unwrap_or(std::cmp::Ordering::Equal)
    });

    targets
}

/// Format a human-readable diagnostic report.
#[must_use]
pub fn format_diagnostic_report(diagnostics: &PipelineDiagnostic) -> String {
    let mut report = String::with_capacity(512);

    report.push_str("=== Pipeline Diagnostic Report ===\n\n");
    report.push_str(&format!("Layers: {}\n", diagnostics.layers.len()));
    report.push_str(&format!(
        "Total amplification: {:.4}\n",
        diagnostics.total_amplification
    ));
    report.push_str(&format!(
        "Bottleneck: layer {} ({})\n",
        diagnostics.bottleneck_layer, diagnostics.layers[diagnostics.bottleneck_layer].layer_type
    ));
    report.push_str(&format!(
        "Tightest:   layer {} ({})\n\n",
        diagnostics.tightest_layer, diagnostics.layers[diagnostics.tightest_layer].layer_type
    ));

    report.push_str("--- Per-Layer ---\n");
    for layer in &diagnostics.layers {
        report.push_str(&format!(
            "  [{}] {} | in_w={:.4} out_w={:.4} amp={:.4} | crossing={}/{}\n",
            layer.layer_idx,
            layer.layer_type,
            layer.input_width,
            layer.output_width,
            layer.amplification,
            layer.crossing_neurons,
            layer.total_neurons,
        ));
    }

    let targets = suggest_tightening_targets(diagnostics);
    if !targets.is_empty() {
        report.push_str("\n--- Tightening Suggestions ---\n");
        for t in &targets {
            report.push_str(&format!(
                "  layer {}: {} -> {} (expected improvement: {:.2}x)\n",
                t.layer_idx, t.current_method, t.suggested_method, t.expected_improvement,
            ));
        }
    }

    report
}

// ---------------------------------------------------------------------------
// Improvement estimators
// ---------------------------------------------------------------------------

/// Estimate improvement factor from switching to CROWN.
///
/// CROWN typically tightens bounds by a factor inversely related to
/// amplification; higher amplification layers benefit more.
#[must_use]
fn estimate_crown_improvement(layer: &LayerDiagnostic) -> f64 {
    // Heuristic: CROWN reduces width by ~30-50% for moderate amplification.
    let crossing_ratio = if layer.total_neurons > 0 {
        layer.crossing_neurons as f64 / layer.total_neurons as f64
    } else {
        0.0
    };
    // More crossing neurons => more room for CROWN to tighten.
    0.5 + 0.3 * crossing_ratio
}

/// Estimate improvement factor from switching to alpha-CROWN.
#[must_use]
fn estimate_alpha_crown_improvement(layer: &LayerDiagnostic) -> f64 {
    let crossing_ratio = if layer.total_neurons > 0 {
        layer.crossing_neurons as f64 / layer.total_neurons as f64
    } else {
        0.0
    };
    // alpha-CROWN is tighter than CROWN, especially with many crossing neurons.
    0.3 + 0.4 * crossing_ratio
}

/// Estimate improvement factor from switching to McCormick envelopes.
#[must_use]
fn estimate_mccormick_improvement(layer: &LayerDiagnostic) -> f64 {
    // McCormick is most effective for bilinear terms in attention.
    let base = match layer.layer_type {
        LayerType::Attention => 0.35,
        LayerType::LayerNorm => 0.45,
        _ => 0.6,
    };
    let crossing_ratio = if layer.total_neurons > 0 {
        layer.crossing_neurons as f64 / layer.total_neurons as f64
    } else {
        0.0
    };
    base + 0.2 * crossing_ratio
}
