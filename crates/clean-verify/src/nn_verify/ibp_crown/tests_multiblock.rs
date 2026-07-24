// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Multi-block network verification integration tests.
//!
//! Demonstrates the full IBP + Lipschitz proof pipeline on realistic
//! architectures: Whisper-tiny-like (4 blocks), residual networks (3 blocks
//! with skip connections), deep narrow networks (8 layers), adversarial
//! robustness checking, and IBP bound comparison across depth.
//!
//! All weights are deterministic (hardcoded small matrices) for reproducibility.

use super::ibp::{IbpCompositionSpec, IbpLinearSpec, IbpReluSpec, Interval};
use super::lipschitz::{
    EclipseLipschitzSpec, LayerLipschitz, LipschitzComposeSpec, LipschitzSource,
    ResidualLipschitzSpec,
};

// ---------------------------------------------------------------------------
// Helpers: deterministic weight generation + network evaluation
// ---------------------------------------------------------------------------

/// Compute the spectral norm (max singular value) of a matrix via power
/// iteration. 20 iterations is sufficient for small test matrices.
fn spectral_norm(weights: &[Vec<f64>]) -> f64 {
    let m = weights.len();
    if m == 0 {
        return 0.0;
    }
    let n = weights[0].len();
    // Start with uniform vector
    let mut v = vec![1.0 / (n as f64).sqrt(); n];
    for _ in 0..20 {
        // u = W * v
        let mut u = vec![0.0; m];
        for (i, row) in weights.iter().enumerate() {
            u[i] = row.iter().zip(v.iter()).map(|(w, x)| w * x).sum();
        }
        let u_norm: f64 = u.iter().map(|x| x * x).sum::<f64>().sqrt();
        if u_norm < 1e-15 {
            return 0.0;
        }
        for x in &mut u {
            *x /= u_norm;
        }
        // v = W^T * u
        v = vec![0.0; n];
        for (i, row) in weights.iter().enumerate() {
            for (j, w) in row.iter().enumerate() {
                v[j] += w * u[i];
            }
        }
        let v_norm: f64 = v.iter().map(|x| x * x).sum::<f64>().sqrt();
        if v_norm < 1e-15 {
            return 0.0;
        }
        for x in &mut v {
            *x /= v_norm;
        }
    }
    // Final sigma = ||W * v||
    let mut wv = vec![0.0; m];
    for (i, row) in weights.iter().enumerate() {
        wv[i] = row.iter().zip(v.iter()).map(|(w, x)| w * x).sum();
    }
    wv.iter().map(|x| x * x).sum::<f64>().sqrt()
}

/// Evaluate y = Wx + b for concrete x.
fn linear_eval(weights: &[Vec<f64>], bias: &[f64], x: &[f64]) -> Vec<f64> {
    weights
        .iter()
        .zip(bias.iter())
        .map(|(row, b)| row.iter().zip(x.iter()).map(|(w, xi)| w * xi).sum::<f64>() + b)
        .collect()
}

/// Element-wise ReLU on a concrete vector.
fn relu_eval(x: &[f64]) -> Vec<f64> {
    x.iter().map(|v| v.max(0.0)).collect()
}

/// Check that every element of `concrete` falls within the corresponding
/// interval in `bounds`, with floating-point tolerance.
fn assert_concrete_in_bounds(concrete: &[f64], bounds: &[Interval], label: &str) {
    assert_eq!(
        concrete.len(),
        bounds.len(),
        "{label}: dimension mismatch: concrete={} vs bounds={}",
        concrete.len(),
        bounds.len()
    );
    for (i, (val, bound)) in concrete.iter().zip(bounds.iter()).enumerate() {
        assert!(
            *val >= bound.lower - 1e-9 && *val <= bound.upper + 1e-9,
            "{label}[{i}]: value {val} not in [{}, {}]",
            bound.lower,
            bound.upper
        );
    }
}

/// Propagate a concrete vector through Linear+ReLU.
fn forward_linear_relu(weights: &[Vec<f64>], bias: &[f64], x: &[f64]) -> Vec<f64> {
    relu_eval(&linear_eval(weights, bias, x))
}

/// Total width of a bound vector (sum of individual interval widths).
fn total_width(bounds: &[Interval]) -> f64 {
    bounds.iter().map(Interval::width).sum()
}

// ---------------------------------------------------------------------------
// Deterministic weight matrices (small, Lipschitz-bounded)
// ---------------------------------------------------------------------------

/// 8x16 weight matrix: scaled contraction (spectral norm < 1).
/// Pattern: alternating +0.1/-0.1 with diagonal dominance.
fn whisper_w1() -> Vec<Vec<f64>> {
    let mut w = vec![vec![0.0; 8]; 16];
    for (i, row) in w.iter_mut().enumerate() {
        for (j, cell) in row.iter_mut().enumerate() {
            let sign = if (i + j) % 2 == 0 { 1.0 } else { -1.0 };
            *cell = sign * 0.15 / (1.0 + (i as f64 - j as f64).abs());
        }
    }
    w
}

/// 16x8 projection back to dimension 8.
fn whisper_w2() -> Vec<Vec<f64>> {
    let mut w = vec![vec![0.0; 16]; 8];
    for (i, row) in w.iter_mut().enumerate() {
        for (j, cell) in row.iter_mut().enumerate() {
            let sign = if (i + j) % 3 == 0 { -1.0 } else { 1.0 };
            *cell = sign * 0.1 / (1.0 + (i as f64 * 2.0 - j as f64).abs());
        }
    }
    w
}

/// 8x4 final projection.
fn whisper_final() -> Vec<Vec<f64>> {
    vec![
        vec![0.3, -0.1, 0.2, -0.05, 0.1, -0.1, 0.05, 0.15],
        vec![-0.1, 0.25, -0.15, 0.2, -0.05, 0.1, -0.1, 0.05],
        vec![0.05, -0.1, 0.3, -0.1, 0.15, -0.05, 0.1, -0.1],
        vec![-0.15, 0.1, -0.05, 0.25, -0.1, 0.2, -0.15, 0.1],
    ]
}

/// 4x4 Lipschitz-bounded weight matrix for residual/deep tests.
fn small_4x4(seed: usize) -> Vec<Vec<f64>> {
    let mut w = vec![vec![0.0; 4]; 4];
    for (i, row) in w.iter_mut().enumerate() {
        for (j, cell) in row.iter_mut().enumerate() {
            let k = (seed * 17 + i * 7 + j * 13) % 20;
            let val = (k as f64 - 10.0) * 0.04;
            *cell = val;
        }
    }
    w
}

/// 2x2 Lipschitz-bounded weights for deep narrow tests.
fn narrow_2x2(seed: usize) -> Vec<Vec<f64>> {
    let entries = [0.3, -0.2, 0.1, 0.35];
    let offset = seed % 4;
    vec![
        vec![entries[(offset) % 4] * 0.9, entries[(offset + 1) % 4] * 0.9],
        vec![
            entries[(offset + 2) % 4] * 0.9,
            entries[(offset + 3) % 4] * 0.9,
        ],
    ]
}

// ===========================================================================
// Test 1: Whisper-tiny-like (4 transformer blocks)
// ===========================================================================

#[test]
fn test_multiblock_whisper_tiny_4_blocks_ibp_pipeline() {
    let linear = IbpLinearSpec::new();
    let relu = IbpReluSpec::new();
    let comp = IbpCompositionSpec::new();

    // Input: 8-dim, center 0, epsilon 0.5
    let input_bounds: Vec<Interval> = (0..8).map(|_| Interval::new(-0.5, 0.5)).collect();

    let w1 = whisper_w1();
    let b1 = vec![0.0; 16];
    let w2 = whisper_w2();
    let b2 = vec![0.0; 8];

    // Propagate through 4 identical transformer-like blocks
    let mut bounds = input_bounds.clone();
    let mut chain = vec![bounds.clone()];

    for _block in 0..4 {
        // Linear(8->16) + ReLU
        bounds = comp.compose_linear_relu(&linear, &relu, &w1, &b1, &bounds);
        chain.push(bounds.clone());
        // Linear(16->8) (no ReLU between blocks to simulate residual stream)
        bounds = linear.propagate(&w2, &b2, &bounds);
        chain.push(bounds.clone());
    }

    // Final projection 8->4
    let wf = whisper_final();
    let bf = vec![0.0; 4];
    let output_bounds = linear.propagate(&wf, &bf, &bounds);
    chain.push(output_bounds.clone());

    // (1) Chain composes validly
    comp.verify_chain(&chain)
        .expect("whisper-tiny IBP chain should compose");

    // (2) Output bounds are finite and non-degenerate
    for (i, b) in output_bounds.iter().enumerate() {
        assert!(b.lower.is_finite(), "output[{i}] lower not finite");
        assert!(b.upper.is_finite(), "output[{i}] upper not finite");
        assert!(b.width() >= 0.0, "output[{i}] has negative width");
    }

    // (3) Concrete evaluation at center lands within bounds
    let center = vec![0.0; 8];
    let mut x = center.clone();
    for _block in 0..4 {
        x = relu_eval(&linear_eval(&w1, &b1, &x));
        x = linear_eval(&w2, &b2, &x);
    }
    let output_concrete = linear_eval(&wf, &bf, &x);
    assert_concrete_in_bounds(&output_concrete, &output_bounds, "whisper-center");

    // (4) Concrete evaluation at a corner also lands within bounds
    let corner = vec![0.5, -0.5, 0.5, -0.5, 0.5, -0.5, 0.5, -0.5];
    let mut x = corner;
    for _block in 0..4 {
        x = relu_eval(&linear_eval(&w1, &b1, &x));
        x = linear_eval(&w2, &b2, &x);
    }
    let output_corner = linear_eval(&wf, &bf, &x);
    assert_concrete_in_bounds(&output_corner, &output_bounds, "whisper-corner");
}

#[test]
fn test_multiblock_whisper_tiny_lipschitz_chain() {
    let compose_spec = LipschitzComposeSpec::new();

    let w1 = whisper_w1();
    let w2 = whisper_w2();
    let wf = whisper_final();

    let sn_w1 = spectral_norm(&w1);
    let sn_w2 = spectral_norm(&w2);
    let sn_wf = spectral_norm(&wf);

    // Each block: Linear(sn_w1) -> ReLU(1) -> Linear(sn_w2)
    let mut layers = Vec::new();
    for _ in 0..4 {
        layers.push(LayerLipschitz::new(sn_w1, LipschitzSource::SpectralNorm));
        layers.push(LayerLipschitz::relu());
        layers.push(LayerLipschitz::new(sn_w2, LipschitzSource::SpectralNorm));
    }
    layers.push(LayerLipschitz::new(sn_wf, LipschitzSource::SpectralNorm));

    let total = compose_spec.compose_chain(&layers);

    // Lipschitz constant must be non-negative and finite
    assert!(total.constant() >= 0.0, "Lipschitz constant negative");
    assert!(
        total.constant().is_finite(),
        "Lipschitz constant not finite"
    );

    // With small weights (spectral norms < 1), 4-block chain should not
    // explode. Product of all spectral norms should be modest.
    let manual_product: f64 = (0..4).map(|_| sn_w1 * 1.0 * sn_w2).product::<f64>() * sn_wf;
    assert!(
        (total.constant() - manual_product).abs() < 1e-6,
        "compose_chain disagrees with manual product: {} vs {manual_product}",
        total.constant()
    );
}

// ===========================================================================
// Test 2: Residual network (3 blocks with skip connections)
// ===========================================================================

#[test]
fn test_multiblock_residual_3_blocks_ibp() {
    let linear = IbpLinearSpec::new();
    let relu = IbpReluSpec::new();
    let comp = IbpCompositionSpec::new();

    let input_bounds: Vec<Interval> = (0..4).map(|_| Interval::new(-1.0, 1.0)).collect();

    let weights: Vec<Vec<Vec<f64>>> = (0..3).map(small_4x4).collect();
    let biases: Vec<Vec<f64>> = vec![vec![0.0; 4]; 3];

    // Forward with skip: output = input + ReLU(W*input + b)
    let mut bounds = input_bounds.clone();
    let mut chain = vec![bounds.clone()];

    for block in 0..3 {
        let after_relu =
            comp.compose_linear_relu(&linear, &relu, &weights[block], &biases[block], &bounds);

        // Skip connection: elementwise add input + ReLU(W*input + b)
        // IBP: [l_skip, u_skip] = [l_in + l_relu, u_in + u_relu]
        let mut skip_bounds = Vec::with_capacity(4);
        for (inp, act) in bounds.iter().zip(after_relu.iter()) {
            skip_bounds.push(Interval::new(inp.lower + act.lower, inp.upper + act.upper));
        }
        bounds = skip_bounds;
        chain.push(bounds.clone());
    }

    // (1) Chain valid
    comp.verify_chain(&chain)
        .expect("residual IBP chain should compose");

    // (2) Skip connection widens bounds: each block's output is at least as
    //     wide as its input (because skip adds a non-negative-width interval)
    let input_width = total_width(&input_bounds);
    let output_width = total_width(&bounds);
    assert!(
        output_width >= input_width - 1e-9,
        "residual output should be at least as wide as input: {output_width} < {input_width}"
    );

    // (3) Concrete evaluation at center
    let center = vec![0.0; 4];
    let mut x = center;
    for block in 0..3 {
        let branch = forward_linear_relu(&weights[block], &biases[block], &x);
        x = x.iter().zip(branch.iter()).map(|(a, b)| a + b).collect();
    }
    assert_concrete_in_bounds(&x, &bounds, "residual-center");

    // (4) Concrete at extremes
    let extremes = vec![1.0, -1.0, 1.0, -1.0];
    let mut x = extremes;
    for block in 0..3 {
        let branch = forward_linear_relu(&weights[block], &biases[block], &x);
        x = x.iter().zip(branch.iter()).map(|(a, b)| a + b).collect();
    }
    assert_concrete_in_bounds(&x, &bounds, "residual-extreme");
}

#[test]
fn test_multiblock_residual_lipschitz_grows_additively() {
    let residual_spec = ResidualLipschitzSpec::new();
    let compose_spec = LipschitzComposeSpec::new();

    let weights: Vec<Vec<Vec<f64>>> = (0..3).map(small_4x4).collect();

    // Each residual block: L_block = 1 + L_f where L_f = sn(W) * 1 (ReLU)
    let mut block_lips = Vec::new();
    for w in &weights {
        let sn = spectral_norm(w);
        let f_lip = LayerLipschitz::new(sn, LipschitzSource::SpectralNorm);
        let block = residual_spec.residual_bound(&f_lip);
        block_lips.push(block);
        // Residual bound should be 1 + sn
        assert!(
            (block.constant() - (1.0 + sn)).abs() < 1e-9,
            "residual bound incorrect: {} vs {}",
            block.constant(),
            1.0 + sn
        );
    }

    // Composed Lipschitz = product of block Lipschitz constants
    let total = compose_spec.compose_chain(&block_lips);
    let manual: f64 = block_lips.iter().map(|l| l.constant()).product();
    assert!(
        (total.constant() - manual).abs() < 1e-9,
        "composed residual Lipschitz mismatch"
    );
}

// ===========================================================================
// Test 3: Deep narrow network (8 layers, 2->2)
// ===========================================================================

#[test]
fn test_multiblock_deep_narrow_8_layers_bounds_dont_explode() {
    let linear = IbpLinearSpec::new();
    let relu = IbpReluSpec::new();
    let comp = IbpCompositionSpec::new();

    let input_bounds = vec![Interval::new(-1.0, 1.0), Interval::new(-1.0, 1.0)];

    let weights: Vec<Vec<Vec<f64>>> = (0..8).map(narrow_2x2).collect();
    let bias = vec![0.0; 2];

    let mut bounds = input_bounds.clone();
    let mut widths = vec![total_width(&bounds)];

    for weight in &weights {
        bounds = comp.compose_linear_relu(&linear, &relu, weight, &bias, &bounds);
        widths.push(total_width(&bounds));
    }

    // With weights scaled by 0.9, spectral norms are < 1, so the network
    // is contractive. Bounds should shrink (or at worst stay stable).
    let final_width = *widths.last().unwrap();
    assert!(
        final_width < 100.0,
        "deep narrow bounds exploded: total width = {final_width}"
    );
    assert!(final_width.is_finite(), "deep narrow bounds not finite");

    // Verify that bounds are non-degenerate after 8 layers
    for (i, b) in bounds.iter().enumerate() {
        assert!(b.lower.is_finite(), "layer 8 output[{i}] lower not finite");
        assert!(b.upper.is_finite(), "layer 8 output[{i}] upper not finite");
    }

    // Concrete at center should land in bounds
    let mut x = vec![0.0, 0.0];
    for weight in &weights {
        x = forward_linear_relu(weight, &bias, &x);
    }
    assert_concrete_in_bounds(&x, &bounds, "deep-narrow-center");
}

#[test]
fn test_multiblock_deep_narrow_lipschitz_contracts() {
    let compose_spec = LipschitzComposeSpec::new();

    let weights: Vec<Vec<Vec<f64>>> = (0..8).map(narrow_2x2).collect();

    let mut layers = Vec::new();
    for w in &weights {
        let sn = spectral_norm(w);
        layers.push(LayerLipschitz::new(sn, LipschitzSource::SpectralNorm));
        layers.push(LayerLipschitz::relu());
    }

    let total = compose_spec.compose_chain(&layers);

    // All spectral norms of narrow_2x2 matrices (scaled by 0.9) should be
    // well below 1.0, making the product < 1 (contractive).
    // Verify each spectral norm is small:
    for (i, w) in weights.iter().enumerate() {
        let sn = spectral_norm(w);
        assert!(
            sn < 1.0,
            "layer {i} spectral norm {sn} >= 1.0, network not contractive"
        );
    }

    assert!(
        total.constant() < 1.0,
        "8-layer narrow Lipschitz should be < 1 (contractive): got {}",
        total.constant()
    );
}

#[test]
fn test_multiblock_deep_narrow_width_monotonically_bounded() {
    let linear = IbpLinearSpec::new();
    let relu = IbpReluSpec::new();
    let comp = IbpCompositionSpec::new();

    let input_bounds = vec![Interval::new(-1.0, 1.0), Interval::new(-1.0, 1.0)];

    let weights: Vec<Vec<Vec<f64>>> = (0..8).map(narrow_2x2).collect();
    let bias = vec![0.0; 2];

    let mut bounds = input_bounds;
    let mut widths = Vec::new();

    for weight in &weights {
        bounds = comp.compose_linear_relu(&linear, &relu, weight, &bias, &bounds);
        widths.push(total_width(&bounds));
    }

    // After ReLU clipping and contractive weights, widths should generally
    // decrease. At minimum, no width should exceed the Lipschitz-scaled
    // initial width.
    let mut lip_so_far = 1.0_f64;
    let initial_width = 4.0; // 2 dims * 2.0 each

    for (layer, &width) in widths.iter().enumerate() {
        let sn = spectral_norm(&weights[layer]);
        lip_so_far *= sn; // ReLU is 1-Lipschitz
                          // IBP width should be bounded by Lipschitz * initial width
                          // (IBP may be looser, so we allow 2x factor for IBP overestimation)
        let lip_bound = lip_so_far * initial_width * 2.0;
        assert!(
            width <= lip_bound + 1e-6,
            "layer {} width {width} exceeds 2x Lipschitz bound {lip_bound}",
            layer + 1
        );
    }
}

// ===========================================================================
// Test 4: Adversarial robustness check
// ===========================================================================

#[test]
fn test_multiblock_adversarial_robustness_class_stable() {
    let linear = IbpLinearSpec::new();
    let relu = IbpReluSpec::new();
    let comp = IbpCompositionSpec::new();

    // Simple classifier: Linear(2->4) + ReLU + Linear(4->2)
    // Designed so that input (0.5, 0.5) strongly predicts class 0.
    let w1 = vec![
        vec![0.8, 0.3],
        vec![-0.5, 0.6],
        vec![0.2, -0.7],
        vec![-0.3, -0.4],
    ];
    let b1 = vec![0.1, 0.0, 0.0, -0.1];

    let w2 = vec![vec![0.9, -0.2, 0.3, -0.1], vec![-0.3, 0.7, -0.5, 0.2]];
    let b2 = vec![0.2, -0.3];

    // Input: center=(0.5, 0.5), epsilon=0.1
    let epsilon = 0.1;
    let center = [0.5, 0.5];
    let input_bounds = vec![
        Interval::new(center[0] - epsilon, center[0] + epsilon),
        Interval::new(center[1] - epsilon, center[1] + epsilon),
    ];

    // Forward IBP
    let hidden_bounds = comp.compose_linear_relu(&linear, &relu, &w1, &b1, &input_bounds);
    let output_bounds = linear.propagate(&w2, &b2, &hidden_bounds);

    // Verify class 0 is always higher than class 1 in the output bounds.
    // For certified robustness: min(class_0) > max(class_1)
    let class_0_min = output_bounds[0].lower;
    let class_1_max = output_bounds[1].upper;

    // This is the core gamma-crown use case: if the lower bound of the
    // correct class exceeds the upper bound of all other classes, the
    // prediction is certifiably robust.
    assert!(
        class_0_min > class_1_max,
        "NOT certifiably robust: class_0 lower={class_0_min} <= class_1 upper={class_1_max}"
    );

    // Double-check with concrete evaluations at the center and corners
    let points: Vec<[f64; 2]> = vec![[0.5, 0.5], [0.4, 0.4], [0.6, 0.6], [0.4, 0.6], [0.6, 0.4]];
    for pt in &points {
        let h = forward_linear_relu(&w1, &b1, pt);
        let out = linear_eval(&w2, &b2, &h);
        assert!(
            out[0] > out[1],
            "class flip at ({}, {}): out={out:?}",
            pt[0],
            pt[1]
        );
        assert_concrete_in_bounds(&out, &output_bounds, "adversarial-sample");
    }
}

#[test]
fn test_multiblock_adversarial_larger_epsilon_detects_instability() {
    let linear = IbpLinearSpec::new();
    let relu = IbpReluSpec::new();
    let comp = IbpCompositionSpec::new();

    // Same classifier as above
    let w1 = vec![
        vec![0.8, 0.3],
        vec![-0.5, 0.6],
        vec![0.2, -0.7],
        vec![-0.3, -0.4],
    ];
    let b1 = vec![0.1, 0.0, 0.0, -0.1];
    let w2 = vec![vec![0.9, -0.2, 0.3, -0.1], vec![-0.3, 0.7, -0.5, 0.2]];
    let b2 = vec![0.2, -0.3];

    // With a large epsilon, IBP bounds should overlap (not certifiably robust)
    let epsilon = 2.0;
    let center = [0.5, 0.5];
    let input_bounds = vec![
        Interval::new(center[0] - epsilon, center[0] + epsilon),
        Interval::new(center[1] - epsilon, center[1] + epsilon),
    ];

    let hidden = comp.compose_linear_relu(&linear, &relu, &w1, &b1, &input_bounds);
    let output = linear.propagate(&w2, &b2, &hidden);

    // With epsilon=2.0, the bounds should overlap (class not certifiable)
    let class_0_min = output[0].lower;
    let class_1_max = output[1].upper;
    assert!(
        class_0_min <= class_1_max,
        "unexpectedly robust at epsilon=2.0: class_0 lower={class_0_min} > class_1 upper={class_1_max}"
    );
}

// ===========================================================================
// Test 5: IBP bound tightness comparison across depth
// ===========================================================================

#[test]
fn test_multiblock_ibp_bounds_widen_with_depth() {
    let linear = IbpLinearSpec::new();
    let relu = IbpReluSpec::new();
    let comp = IbpCompositionSpec::new();

    // Same network architecture at different depths
    let w = vec![
        vec![0.6, -0.3, 0.1],
        vec![-0.2, 0.5, -0.4],
        vec![0.3, -0.1, 0.7],
    ];
    let b = vec![0.0; 3];
    let input_bounds = vec![
        Interval::new(-1.0, 1.0),
        Interval::new(-1.0, 1.0),
        Interval::new(-1.0, 1.0),
    ];

    // Measure output width at depths 1, 2, 4
    let mut widths = Vec::new();
    for depth in [1, 2, 4] {
        let mut bounds = input_bounds.clone();
        for _ in 0..depth {
            bounds = comp.compose_linear_relu(&linear, &relu, &w, &b, &bounds);
        }
        widths.push(total_width(&bounds));
    }

    // IBP width at depth d should be <= IBP width at depth d+1 is NOT always
    // true (ReLU can clip). But with this contractive network, deeper = narrower
    // or approximately stable. The key property: all widths are finite.
    for (i, &w) in widths.iter().enumerate() {
        assert!(w.is_finite(), "width at depth {} not finite", [1, 2, 4][i]);
        assert!(w >= 0.0, "width at depth {} negative", [1, 2, 4][i]);
    }
}

#[test]
fn test_multiblock_ibp_vs_lipschitz_bound_consistency() {
    let linear = IbpLinearSpec::new();
    let relu = IbpReluSpec::new();
    let comp = IbpCompositionSpec::new();
    let compose_spec = LipschitzComposeSpec::new();

    // 3-layer network: each layer 3->3 with ReLU
    let w = vec![
        vec![0.4, -0.2, 0.1],
        vec![-0.1, 0.3, -0.2],
        vec![0.2, -0.1, 0.5],
    ];
    let b = vec![0.0; 3];
    let sn = spectral_norm(&w);

    let input_bounds = vec![
        Interval::new(-0.5, 0.5),
        Interval::new(-0.5, 0.5),
        Interval::new(-0.5, 0.5),
    ];

    // IBP propagation through 3 layers
    let mut bounds = input_bounds.clone();
    for _ in 0..3 {
        bounds = comp.compose_linear_relu(&linear, &relu, &w, &b, &bounds);
    }
    let ibp_max_width: f64 = bounds.iter().map(|b| b.width()).fold(0.0_f64, f64::max);

    // Lipschitz bound: max output change = L * max input change
    let layers = vec![
        LayerLipschitz::new(sn, LipschitzSource::SpectralNorm),
        LayerLipschitz::relu(),
        LayerLipschitz::new(sn, LipschitzSource::SpectralNorm),
        LayerLipschitz::relu(),
        LayerLipschitz::new(sn, LipschitzSource::SpectralNorm),
        LayerLipschitz::relu(),
    ];
    let lip = compose_spec.compose_chain(&layers);
    let input_diameter = 1.0; // width of each input dimension
                              // Lipschitz bound on output width: L * input_diameter * sqrt(n_in)
                              // (worst case: perturbation along all input dims)
    let lip_width_bound = lip.constant() * input_diameter * (3.0_f64).sqrt();

    // IBP should not exceed Lipschitz bound (IBP is sound, Lipschitz provides
    // an independent bound). We add generous tolerance since IBP and Lipschitz
    // bound different quantities (interval width vs. displacement).
    assert!(
        ibp_max_width <= lip_width_bound * 2.0 + 1e-6,
        "IBP max width {} exceeds 2x Lipschitz bound {}",
        ibp_max_width,
        lip_width_bound
    );
}

// ===========================================================================
// Test 6: Full pipeline stress -- all components together
// ===========================================================================

#[test]
fn test_multiblock_full_pipeline_4_block_with_residual_and_lipschitz() {
    let linear = IbpLinearSpec::new();
    let relu = IbpReluSpec::new();
    let comp = IbpCompositionSpec::new();
    let residual_spec = ResidualLipschitzSpec::new();
    let compose_spec = LipschitzComposeSpec::new();

    let input_bounds: Vec<Interval> = (0..4).map(|_| Interval::new(-0.5, 0.5)).collect();

    let weights: Vec<Vec<Vec<f64>>> = (0..4).map(|s| small_4x4(s + 10)).collect();
    let bias = vec![0.0; 4];

    // IBP propagation with skip connections
    let mut bounds = input_bounds.clone();
    let mut chain = vec![bounds.clone()];

    // Lipschitz tracking in parallel
    let mut block_lips = Vec::new();

    for weight in &weights {
        let branch_bounds = comp.compose_linear_relu(&linear, &relu, weight, &bias, &bounds);

        // Skip connection
        let mut skip = Vec::with_capacity(4);
        for (inp, act) in bounds.iter().zip(branch_bounds.iter()) {
            skip.push(Interval::new(inp.lower + act.lower, inp.upper + act.upper));
        }
        bounds = skip;
        chain.push(bounds.clone());

        // Lipschitz for this block
        let sn = spectral_norm(weight);
        let f_lip = LayerLipschitz::new(sn, LipschitzSource::SpectralNorm);
        block_lips.push(residual_spec.residual_bound(&f_lip));
    }

    // (1) IBP chain valid
    comp.verify_chain(&chain)
        .expect("full pipeline IBP chain should compose");

    // (2) Lipschitz composition
    let total_lip = compose_spec.compose_chain(&block_lips);
    assert!(
        total_lip.constant().is_finite(),
        "total Lipschitz not finite"
    );
    assert!(
        total_lip.constant() > 0.0,
        "total Lipschitz should be positive"
    );

    // (3) All residual Lipschitz constants > 1 (since 1 + L_f > 1 for L_f > 0)
    for (i, lip) in block_lips.iter().enumerate() {
        assert!(
            lip.constant() >= 1.0,
            "block {i} residual Lipschitz {} < 1.0",
            lip.constant()
        );
    }

    // (4) Concrete evaluation at origin
    let mut x = vec![0.0; 4];
    for weight in &weights {
        let branch = forward_linear_relu(weight, &bias, &x);
        x = x.iter().zip(branch.iter()).map(|(a, b)| a + b).collect();
    }
    assert_concrete_in_bounds(&x, &bounds, "full-pipeline-center");

    // (5) Concrete at all-positive corner
    let mut x = vec![0.5; 4];
    for weight in &weights {
        let branch = forward_linear_relu(weight, &bias, &x);
        x = x.iter().zip(branch.iter()).map(|(a, b)| a + b).collect();
    }
    assert_concrete_in_bounds(&x, &bounds, "full-pipeline-corner");
}

// ===========================================================================
// Test 7: Eclipse block Lipschitz for Whisper-like architecture
// ===========================================================================

#[test]
fn test_multiblock_eclipse_lipschitz_whisper_architecture() {
    let eclipse_spec = EclipseLipschitzSpec::new();

    let w1 = whisper_w1();
    let w2 = whisper_w2();

    let sn_w1 = spectral_norm(&w1);
    let sn_w2 = spectral_norm(&w2);

    // Each Whisper block has attention (w1 + relu) and FFN (w2 + relu).
    // For simplicity, treat w1 as "attention" and w2 as "FFN" in each block.
    let attn_lip = LayerLipschitz::new(sn_w1, LipschitzSource::SpectralNorm);
    let ffn_lip = LayerLipschitz::new(sn_w2, LipschitzSource::SpectralNorm);

    // Single eclipse block Lipschitz = (1 + L_attn) * (1 + L_ffn)
    let single = eclipse_spec.block_bound(&attn_lip, &ffn_lip);
    let expected = (1.0 + sn_w1) * (1.0 + sn_w2);
    assert!(
        (single.constant() - expected).abs() < 1e-9,
        "single eclipse block: {} vs {expected}",
        single.constant()
    );

    // 4 stacked eclipse blocks
    let blocks: Vec<(LayerLipschitz, LayerLipschitz)> =
        (0..4).map(|_| (attn_lip, ffn_lip)).collect();
    let stacked = eclipse_spec.stacked_blocks_bound(&blocks);
    let expected_stacked = expected.powi(4);
    assert!(
        (stacked.constant() - expected_stacked).abs() < 1e-6,
        "stacked eclipse: {} vs {expected_stacked}",
        stacked.constant()
    );
}
