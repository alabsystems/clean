// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the pipeline diagnostics module.

use super::diagnostics::*;

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Build a simple layer diagnostic from widths.
fn make_layer(
    idx: usize,
    layer_type: LayerType,
    input: &[(f64, f64)],
    output: &[(f64, f64)],
) -> LayerDiagnostic {
    compute_layer_diagnostic(input, output, idx, layer_type)
}

/// Build a pipeline diagnostic from a slice of layer diagnostics.
fn make_pipeline(layers: &[LayerDiagnostic]) -> PipelineDiagnostic {
    compute_pipeline_diagnostic(layers)
}

// ---------------------------------------------------------------------------
// 1. Layer diagnostic computation
// ---------------------------------------------------------------------------

#[test]
fn test_layer_diagnostic_basic_amplification() {
    let input = [(0.0, 1.0), (0.0, 1.0)];
    let output = [(0.0, 2.0), (0.0, 2.0)];
    let diag = compute_layer_diagnostic(&input, &output, 0, LayerType::Linear);
    assert_eq!(diag.layer_idx, 0);
    assert_eq!(diag.layer_type, LayerType::Linear);
    assert!((diag.input_width - 2.0).abs() < 1e-10);
    assert!((diag.output_width - 4.0).abs() < 1e-10);
    assert!((diag.amplification - 2.0).abs() < 1e-10);
}

#[test]
fn test_layer_diagnostic_no_amplification() {
    let bounds = [(0.0, 1.0), (0.0, 1.0)];
    let diag = compute_layer_diagnostic(&bounds, &bounds, 0, LayerType::ReLU);
    assert!((diag.amplification - 1.0).abs() < 1e-10);
}

#[test]
fn test_layer_diagnostic_contraction() {
    let input = [(0.0, 4.0)];
    let output = [(1.0, 2.0)];
    let diag = compute_layer_diagnostic(&input, &output, 1, LayerType::Linear);
    assert!((diag.amplification - 0.25).abs() < 1e-10);
}

#[test]
fn test_layer_diagnostic_zero_input_width_nonzero_output() {
    let input = [(1.0, 1.0)];
    let output = [(0.0, 2.0)];
    let diag = compute_layer_diagnostic(&input, &output, 0, LayerType::Linear);
    assert!(diag.amplification.is_infinite());
}

#[test]
fn test_layer_diagnostic_zero_input_zero_output() {
    let input = [(1.0, 1.0)];
    let output = [(5.0, 5.0)];
    let diag = compute_layer_diagnostic(&input, &output, 0, LayerType::Linear);
    assert!((diag.amplification - 1.0).abs() < 1e-10);
}

#[test]
fn test_layer_diagnostic_crossing_neurons_detected() {
    let input = [(0.0, 1.0)];
    let output = [(-1.0, 1.0), (0.0, 2.0), (-0.5, 0.5)];
    let diag = compute_layer_diagnostic(&input, &output, 0, LayerType::ReLU);
    assert_eq!(diag.crossing_neurons, 2);
    assert_eq!(diag.total_neurons, 3);
}

#[test]
fn test_layer_diagnostic_no_crossing_neurons() {
    let input = [(0.0, 1.0)];
    let output = [(1.0, 2.0), (0.5, 3.0)];
    let diag = compute_layer_diagnostic(&input, &output, 0, LayerType::ReLU);
    assert_eq!(diag.crossing_neurons, 0);
}

#[test]
fn test_layer_diagnostic_all_crossing() {
    let input = [(0.0, 1.0)];
    let output = [(-1.0, 1.0), (-2.0, 0.5)];
    let diag = compute_layer_diagnostic(&input, &output, 0, LayerType::ReLU);
    assert_eq!(diag.crossing_neurons, 2);
}

#[test]
fn test_layer_diagnostic_preserves_layer_type() {
    for lt in [
        LayerType::Linear,
        LayerType::ReLU,
        LayerType::Conv,
        LayerType::LayerNorm,
        LayerType::Attention,
        LayerType::Residual,
    ] {
        let diag = compute_layer_diagnostic(&[(0.0, 1.0)], &[(0.0, 1.0)], 0, lt);
        assert_eq!(diag.layer_type, lt);
    }
}

#[test]
fn test_layer_diagnostic_empty_bounds() {
    let diag = compute_layer_diagnostic(&[], &[], 0, LayerType::Linear);
    assert!((diag.input_width).abs() < 1e-10);
    assert!((diag.output_width).abs() < 1e-10);
    assert!((diag.amplification - 1.0).abs() < 1e-10);
    assert_eq!(diag.crossing_neurons, 0);
    assert_eq!(diag.total_neurons, 0);
}

// ---------------------------------------------------------------------------
// 2. Pipeline diagnostic aggregation
// ---------------------------------------------------------------------------

#[test]
fn test_pipeline_diagnostic_single_layer() {
    let layer = make_layer(0, LayerType::Linear, &[(0.0, 1.0)], &[(0.0, 2.0)]);
    let pipeline = make_pipeline(&[layer]);
    assert_eq!(pipeline.layers.len(), 1);
    assert!((pipeline.total_amplification - 2.0).abs() < 1e-10);
    assert_eq!(pipeline.bottleneck_layer, 0);
    assert_eq!(pipeline.tightest_layer, 0);
}

#[test]
fn test_pipeline_diagnostic_two_layers_bottleneck_is_higher() {
    let l0 = make_layer(0, LayerType::Linear, &[(0.0, 1.0)], &[(0.0, 3.0)]);
    let l1 = make_layer(1, LayerType::ReLU, &[(0.0, 3.0)], &[(0.0, 1.5)]);
    let pipeline = make_pipeline(&[l0, l1]);
    // l0 amp=3.0, l1 amp=0.5, total=1.5
    assert!((pipeline.total_amplification - 1.5).abs() < 1e-10);
    assert_eq!(pipeline.bottleneck_layer, 0);
    assert_eq!(pipeline.tightest_layer, 1);
}

#[test]
fn test_pipeline_diagnostic_three_layers_product() {
    let l0 = make_layer(0, LayerType::Linear, &[(0.0, 2.0)], &[(0.0, 4.0)]);
    let l1 = make_layer(1, LayerType::ReLU, &[(0.0, 4.0)], &[(0.0, 4.0)]);
    let l2 = make_layer(2, LayerType::Linear, &[(0.0, 4.0)], &[(0.0, 12.0)]);
    let pipeline = make_pipeline(&[l0, l1, l2]);
    // amps: 2.0, 1.0, 3.0 => total = 6.0
    assert!((pipeline.total_amplification - 6.0).abs() < 1e-10);
    assert_eq!(pipeline.bottleneck_layer, 2);
    assert_eq!(pipeline.tightest_layer, 1);
}

#[test]
fn test_pipeline_diagnostic_equal_amplification() {
    let l0 = make_layer(0, LayerType::Linear, &[(0.0, 1.0)], &[(0.0, 2.0)]);
    let l1 = make_layer(1, LayerType::Linear, &[(0.0, 2.0)], &[(0.0, 4.0)]);
    let pipeline = make_pipeline(&[l0, l1]);
    // Both amp=2.0; when amplifications are equal the selected index is
    // implementation-defined. Just verify both are valid indices and the
    // total amplification is correct.
    assert!(pipeline.bottleneck_layer < 2);
    assert!(pipeline.tightest_layer < 2);
    assert!((pipeline.total_amplification - 4.0).abs() < 1e-10);
}

#[test]
#[should_panic(expected = "cannot compute pipeline diagnostic from empty layer list")]
fn test_pipeline_diagnostic_empty_panics() {
    let _ = compute_pipeline_diagnostic(&[]);
}

// ---------------------------------------------------------------------------
// 3. Bottleneck identification
// ---------------------------------------------------------------------------

#[test]
fn test_identify_bottleneck_single_layer() {
    let layer = make_layer(0, LayerType::Conv, &[(0.0, 1.0)], &[(0.0, 5.0)]);
    let pipeline = make_pipeline(&[layer]);
    let report = identify_bottleneck(&pipeline);
    assert_eq!(report.layer_idx, 0);
    assert!((report.amplification - 5.0).abs() < 1e-10);
    assert_eq!(report.layer_type, LayerType::Conv);
}

#[test]
fn test_identify_bottleneck_selects_worst_layer() {
    let l0 = make_layer(0, LayerType::Linear, &[(0.0, 1.0)], &[(0.0, 2.0)]);
    let l1 = make_layer(1, LayerType::ReLU, &[(0.0, 2.0)], &[(0.0, 20.0)]);
    let l2 = make_layer(2, LayerType::Linear, &[(0.0, 20.0)], &[(0.0, 10.0)]);
    let pipeline = make_pipeline(&[l0, l1, l2]);
    let report = identify_bottleneck(&pipeline);
    assert_eq!(report.layer_idx, 1);
    assert!((report.amplification - 10.0).abs() < 1e-10);
    assert_eq!(report.layer_type, LayerType::ReLU);
}

#[test]
fn test_identify_bottleneck_returns_correct_layer_type() {
    let l0 = make_layer(0, LayerType::Attention, &[(0.0, 1.0)], &[(0.0, 8.0)]);
    let pipeline = make_pipeline(&[l0]);
    let report = identify_bottleneck(&pipeline);
    assert_eq!(report.layer_type, LayerType::Attention);
}

// ---------------------------------------------------------------------------
// 4. Tightening suggestions
// ---------------------------------------------------------------------------

#[test]
fn test_suggest_tightening_no_suggestions_for_low_amplification() {
    let l0 = make_layer(0, LayerType::Linear, &[(0.0, 1.0)], &[(0.0, 1.5)]);
    let pipeline = make_pipeline(&[l0]);
    let targets = suggest_tightening_targets(&pipeline);
    assert!(targets.is_empty());
}

#[test]
fn test_suggest_tightening_crown_for_moderate_linear() {
    let l0 = make_layer(0, LayerType::Linear, &[(0.0, 1.0)], &[(0.0, 3.0)]);
    let pipeline = make_pipeline(&[l0]);
    let targets = suggest_tightening_targets(&pipeline);
    assert_eq!(targets.len(), 1);
    assert_eq!(targets[0].layer_idx, 0);
    assert_eq!(targets[0].current_method, VerificationMethod::IBP);
    assert_eq!(targets[0].suggested_method, VerificationMethod::CROWN);
}

#[test]
fn test_suggest_tightening_alpha_crown_for_high_linear() {
    let l0 = make_layer(0, LayerType::Linear, &[(0.0, 1.0)], &[(0.0, 6.0)]);
    let pipeline = make_pipeline(&[l0]);
    let targets = suggest_tightening_targets(&pipeline);
    assert_eq!(targets.len(), 1);
    assert_eq!(targets[0].suggested_method, VerificationMethod::AlphaCROWN);
}

#[test]
fn test_suggest_tightening_mccormick_for_attention() {
    let l0 = make_layer(0, LayerType::Attention, &[(0.0, 1.0)], &[(0.0, 4.0)]);
    let pipeline = make_pipeline(&[l0]);
    let targets = suggest_tightening_targets(&pipeline);
    assert_eq!(targets.len(), 1);
    assert_eq!(targets[0].suggested_method, VerificationMethod::McCormick);
}

#[test]
fn test_suggest_tightening_mccormick_for_layernorm() {
    let l0 = make_layer(0, LayerType::LayerNorm, &[(0.0, 1.0)], &[(0.0, 4.0)]);
    let pipeline = make_pipeline(&[l0]);
    let targets = suggest_tightening_targets(&pipeline);
    assert_eq!(targets.len(), 1);
    assert_eq!(targets[0].suggested_method, VerificationMethod::McCormick);
}

#[test]
fn test_suggest_tightening_sorted_by_improvement() {
    // Two layers, both above threshold; ensure sorted by expected_improvement.
    let l0 = make_layer(0, LayerType::Linear, &[(0.0, 1.0)], &[(0.0, 3.0)]);
    let l1 = make_layer(
        1,
        LayerType::ReLU,
        &[(0.0, 3.0)],
        &[(-5.0, 5.0), (-3.0, 3.0), (-1.0, 1.0)],
    );
    let pipeline = make_pipeline(&[l0, l1]);
    let targets = suggest_tightening_targets(&pipeline);
    assert!(targets.len() >= 2);
    // Sorted ascending by expected_improvement.
    for w in targets.windows(2) {
        assert!(w[0].expected_improvement <= w[1].expected_improvement);
    }
}

#[test]
fn test_suggest_tightening_crown_for_relu_moderate() {
    let l0 = make_layer(0, LayerType::ReLU, &[(0.0, 1.0)], &[(0.0, 3.0)]);
    let pipeline = make_pipeline(&[l0]);
    let targets = suggest_tightening_targets(&pipeline);
    assert_eq!(targets.len(), 1);
    assert_eq!(targets[0].suggested_method, VerificationMethod::CROWN);
}

#[test]
fn test_suggest_tightening_residual_uses_linear_heuristic() {
    let l0 = make_layer(0, LayerType::Residual, &[(0.0, 1.0)], &[(0.0, 6.0)]);
    let pipeline = make_pipeline(&[l0]);
    let targets = suggest_tightening_targets(&pipeline);
    assert_eq!(targets.len(), 1);
    assert_eq!(targets[0].suggested_method, VerificationMethod::AlphaCROWN);
}

#[test]
fn test_suggest_tightening_improvement_positive() {
    let l0 = make_layer(0, LayerType::Linear, &[(0.0, 1.0)], &[(-5.0, 5.0)]);
    let pipeline = make_pipeline(&[l0]);
    let targets = suggest_tightening_targets(&pipeline);
    assert_eq!(targets.len(), 1);
    assert!(targets[0].expected_improvement > 0.0);
    assert!(targets[0].expected_improvement < 1.0);
}

// ---------------------------------------------------------------------------
// 5. Report formatting
// ---------------------------------------------------------------------------

#[test]
fn test_format_report_contains_header() {
    let l0 = make_layer(0, LayerType::Linear, &[(0.0, 1.0)], &[(0.0, 2.0)]);
    let pipeline = make_pipeline(&[l0]);
    let report = format_diagnostic_report(&pipeline);
    assert!(report.contains("Pipeline Diagnostic Report"));
}

#[test]
fn test_format_report_contains_layer_count() {
    let l0 = make_layer(0, LayerType::Linear, &[(0.0, 1.0)], &[(0.0, 2.0)]);
    let l1 = make_layer(1, LayerType::ReLU, &[(0.0, 2.0)], &[(0.0, 2.0)]);
    let pipeline = make_pipeline(&[l0, l1]);
    let report = format_diagnostic_report(&pipeline);
    assert!(report.contains("Layers: 2"));
}

#[test]
fn test_format_report_contains_total_amplification() {
    let l0 = make_layer(0, LayerType::Linear, &[(0.0, 1.0)], &[(0.0, 3.0)]);
    let pipeline = make_pipeline(&[l0]);
    let report = format_diagnostic_report(&pipeline);
    assert!(report.contains("Total amplification: 3.0000"));
}

#[test]
fn test_format_report_contains_bottleneck_info() {
    let l0 = make_layer(0, LayerType::Conv, &[(0.0, 1.0)], &[(0.0, 5.0)]);
    let pipeline = make_pipeline(&[l0]);
    let report = format_diagnostic_report(&pipeline);
    assert!(report.contains("Bottleneck: layer 0 (Conv)"));
}

#[test]
fn test_format_report_contains_per_layer_details() {
    let l0 = make_layer(0, LayerType::Linear, &[(0.0, 1.0)], &[(0.0, 2.0)]);
    let pipeline = make_pipeline(&[l0]);
    let report = format_diagnostic_report(&pipeline);
    assert!(report.contains("[0] Linear"));
    assert!(report.contains("amp=2.0000"));
}

#[test]
fn test_format_report_includes_tightening_suggestions() {
    let l0 = make_layer(0, LayerType::Linear, &[(0.0, 1.0)], &[(0.0, 4.0)]);
    let pipeline = make_pipeline(&[l0]);
    let report = format_diagnostic_report(&pipeline);
    assert!(report.contains("Tightening Suggestions"));
    assert!(report.contains("IBP -> CROWN"));
}

#[test]
fn test_format_report_no_suggestions_section_when_tight() {
    let l0 = make_layer(0, LayerType::Linear, &[(0.0, 1.0)], &[(0.0, 1.0)]);
    let pipeline = make_pipeline(&[l0]);
    let report = format_diagnostic_report(&pipeline);
    assert!(!report.contains("Tightening Suggestions"));
}

// ---------------------------------------------------------------------------
// 6. Display impls
// ---------------------------------------------------------------------------

#[test]
fn test_layer_type_display() {
    assert_eq!(format!("{}", LayerType::Linear), "Linear");
    assert_eq!(format!("{}", LayerType::ReLU), "ReLU");
    assert_eq!(format!("{}", LayerType::Conv), "Conv");
    assert_eq!(format!("{}", LayerType::LayerNorm), "LayerNorm");
    assert_eq!(format!("{}", LayerType::Attention), "Attention");
    assert_eq!(format!("{}", LayerType::Residual), "Residual");
}

#[test]
fn test_verification_method_display() {
    assert_eq!(format!("{}", VerificationMethod::IBP), "IBP");
    assert_eq!(format!("{}", VerificationMethod::CROWN), "CROWN");
    assert_eq!(format!("{}", VerificationMethod::AlphaCROWN), "alpha-CROWN");
    assert_eq!(format!("{}", VerificationMethod::McCormick), "McCormick");
}

// ---------------------------------------------------------------------------
// 7. Edge cases and integration
// ---------------------------------------------------------------------------

#[test]
fn test_pipeline_five_layers_selects_correct_bottleneck() {
    let layers: Vec<LayerDiagnostic> = (0..5)
        .map(|i| {
            let amp = if i == 3 { 10.0 } else { 1.5 };
            let out_hi = amp; // input width=1 so output_width = amp
            make_layer(i, LayerType::Linear, &[(0.0, 1.0)], &[(0.0, out_hi)])
        })
        .collect();
    let pipeline = make_pipeline(&layers);
    assert_eq!(pipeline.bottleneck_layer, 3);
    assert_eq!(pipeline.tightest_layer, 0); // all non-bottleneck are 1.5
}

#[test]
fn test_crossing_neurons_negative_only_not_crossing() {
    let input = [(0.0, 1.0)];
    let output = [(-3.0, -1.0)];
    let diag = compute_layer_diagnostic(&input, &output, 0, LayerType::ReLU);
    assert_eq!(diag.crossing_neurons, 0);
}

#[test]
fn test_crossing_neurons_positive_only_not_crossing() {
    let input = [(0.0, 1.0)];
    let output = [(0.5, 2.0)];
    let diag = compute_layer_diagnostic(&input, &output, 0, LayerType::ReLU);
    assert_eq!(diag.crossing_neurons, 0);
}

#[test]
fn test_crossing_neurons_exactly_at_zero_not_crossing() {
    // Boundary: lower=0 means not strictly < 0, so not crossing.
    let input = [(0.0, 1.0)];
    let output = [(0.0, 2.0)];
    let diag = compute_layer_diagnostic(&input, &output, 0, LayerType::ReLU);
    assert_eq!(diag.crossing_neurons, 0);
}

#[test]
fn test_bottleneck_report_fields_match_pipeline() {
    let l0 = make_layer(0, LayerType::Linear, &[(0.0, 1.0)], &[(0.0, 1.0)]);
    let l1 = make_layer(1, LayerType::Attention, &[(0.0, 1.0)], &[(0.0, 7.0)]);
    let pipeline = make_pipeline(&[l0, l1]);
    let report = identify_bottleneck(&pipeline);
    assert_eq!(
        report.layer_idx,
        pipeline.layers[pipeline.bottleneck_layer].layer_idx
    );
    assert!(
        (report.amplification - pipeline.layers[pipeline.bottleneck_layer].amplification).abs()
            < 1e-10
    );
}
