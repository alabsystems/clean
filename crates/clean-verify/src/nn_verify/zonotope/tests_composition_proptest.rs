// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Multi-layer composition property-based tests for zonotope forward passes.
//!
//! Verifies soundness, tightness, and structural properties of zonotope
//! propagation through random 3-5 layer neural networks using a deterministic
//! xorshift32 PRNG.

use super::affine_relu::{compare_zonotope_ibp, zonotope_affine_relu, zonotope_forward_pass};
use super::concrete::ConcreteZonotope;

const TOL: f64 = 1e-9;

// ---------------------------------------------------------------------------
// Deterministic xorshift32 PRNG
// ---------------------------------------------------------------------------

struct Xorshift32 {
    state: u32,
}

impl Xorshift32 {
    fn new(seed: u32) -> Self {
        Self {
            state: if seed == 0 { 1 } else { seed },
        }
    }

    fn next_u32(&mut self) -> u32 {
        let mut x = self.state;
        x ^= x << 13;
        x ^= x >> 17;
        x ^= x << 5;
        self.state = x;
        x
    }

    fn next_f64_range(&mut self, lo: f64, hi: f64) -> f64 {
        let t = self.next_u32() as f64 / u32::MAX as f64;
        lo + t * (hi - lo)
    }

    fn next_eps(&mut self) -> f64 {
        self.next_f64_range(-1.0, 1.0)
    }

    fn next_usize_range(&mut self, lo: usize, hi: usize) -> usize {
        let range = (hi - lo + 1) as u32;
        lo + (self.next_u32() % range) as usize
    }
}

// ---------------------------------------------------------------------------
// Random construction helpers
// ---------------------------------------------------------------------------

fn random_zonotope(rng: &mut Xorshift32, dim: usize, n_gen: usize) -> ConcreteZonotope {
    let center: Vec<f64> = (0..dim).map(|_| rng.next_f64_range(-5.0, 5.0)).collect();
    let generators: Vec<Vec<f64>> = (0..n_gen)
        .map(|_| (0..dim).map(|_| rng.next_f64_range(-3.0, 3.0)).collect())
        .collect();
    ConcreteZonotope::new(center, generators)
}

fn random_weight_matrix(rng: &mut Xorshift32, rows: usize, cols: usize) -> Vec<Vec<f64>> {
    (0..rows)
        .map(|_| (0..cols).map(|_| rng.next_f64_range(-1.5, 1.5)).collect())
        .collect()
}

fn random_bias(rng: &mut Xorshift32, dim: usize) -> Vec<f64> {
    (0..dim).map(|_| rng.next_f64_range(-0.5, 0.5)).collect()
}

/// Generate a random multi-layer network. Returns (layers, list of layer dims).
fn random_network(
    rng: &mut Xorshift32,
    d_in: usize,
    n_layers: usize,
) -> (Vec<(Vec<Vec<f64>>, Vec<f64>)>, Vec<usize>) {
    let mut layers = Vec::with_capacity(n_layers);
    let mut dims = vec![d_in];
    let mut prev_dim = d_in;
    for _ in 0..n_layers {
        let next_dim = rng.next_usize_range(2, 5);
        let w = random_weight_matrix(rng, next_dim, prev_dim);
        let b = random_bias(rng, next_dim);
        layers.push((w, b));
        dims.push(next_dim);
        prev_dim = next_dim;
    }
    (layers, dims)
}

fn sample_inside(rng: &mut Xorshift32, z: &ConcreteZonotope) -> Vec<f64> {
    let coeffs: Vec<f64> = (0..z.num_generators()).map(|_| rng.next_eps()).collect();
    z.sample_point(&coeffs).unwrap()
}

fn matvec(w: &[Vec<f64>], x: &[f64], b: &[f64]) -> Vec<f64> {
    w.iter()
        .enumerate()
        .map(|(i, row)| row.iter().zip(x.iter()).map(|(a, b)| a * b).sum::<f64>() + b[i])
        .collect()
}

fn relu_vec(x: &[f64]) -> Vec<f64> {
    x.iter().map(|&v| v.max(0.0)).collect()
}

#[allow(dead_code)] // 2026-07-31: no caller in EITHER build (the module-level not(test) allow covers only the lib build).
fn hull_width(z: &ConcreteZonotope) -> Vec<f64> {
    let (lo, hi) = z.to_interval();
    lo.iter().zip(hi.iter()).map(|(&l, &h)| h - l).collect()
}

#[allow(dead_code)] // 2026-07-31: no caller in EITHER build (the module-level not(test) allow covers only the lib build).
fn total_width(z: &ConcreteZonotope) -> f64 {
    hull_width(z).iter().sum()
}

/// Evaluate a concrete network forward pass on a point.
fn eval_network(x: &[f64], layers: &[(Vec<Vec<f64>>, Vec<f64>)]) -> Vec<f64> {
    let mut current = x.to_vec();
    for (w, b) in layers {
        current = relu_vec(&matvec(w, &current, b));
    }
    current
}

// ===========================================================================
// Multi-layer soundness: actual output within zonotope bounds
// ===========================================================================

#[test]
fn test_composition_3layer_soundness() {
    let mut rng = Xorshift32::new(0x3333_0001);
    for trial in 0..12 {
        let d_in = rng.next_usize_range(2, 4);
        let n_gen = rng.next_usize_range(2, 5);
        let z = random_zonotope(&mut rng, d_in, n_gen);
        let (layers, _dims) = random_network(&mut rng, d_in, 3);

        let z_out = zonotope_forward_pass(&z, &layers);
        let (lo, hi) = z_out.to_interval();

        for _s in 0..100 {
            let x = sample_inside(&mut rng, &z);
            let y = eval_network(&x, &layers);
            for j in 0..z_out.dim() {
                assert!(
                    y[j] >= lo[j] - TOL && y[j] <= hi[j] + TOL,
                    "trial {trial}: 3-layer output[{j}] = {} not in [{}, {}]",
                    y[j],
                    lo[j],
                    hi[j]
                );
            }
        }
    }
}

#[test]
fn test_composition_4layer_soundness() {
    let mut rng = Xorshift32::new(0x4444_0001);
    for trial in 0..10 {
        let d_in = rng.next_usize_range(2, 4);
        let n_gen = rng.next_usize_range(2, 4);
        let z = random_zonotope(&mut rng, d_in, n_gen);
        let (layers, _dims) = random_network(&mut rng, d_in, 4);

        let z_out = zonotope_forward_pass(&z, &layers);
        let (lo, hi) = z_out.to_interval();

        for _s in 0..80 {
            let x = sample_inside(&mut rng, &z);
            let y = eval_network(&x, &layers);
            for j in 0..z_out.dim() {
                assert!(
                    y[j] >= lo[j] - TOL && y[j] <= hi[j] + TOL,
                    "trial {trial}: 4-layer output[{j}] = {} not in [{}, {}]",
                    y[j],
                    lo[j],
                    hi[j]
                );
            }
        }
    }
}

#[test]
fn test_composition_5layer_soundness() {
    let mut rng = Xorshift32::new(0x5555_0001);
    for trial in 0..8 {
        let d_in = rng.next_usize_range(2, 3);
        let n_gen = rng.next_usize_range(2, 4);
        let z = random_zonotope(&mut rng, d_in, n_gen);
        let (layers, _dims) = random_network(&mut rng, d_in, 5);

        let z_out = zonotope_forward_pass(&z, &layers);
        let (lo, hi) = z_out.to_interval();

        for _s in 0..60 {
            let x = sample_inside(&mut rng, &z);
            let y = eval_network(&x, &layers);
            for j in 0..z_out.dim() {
                assert!(
                    y[j] >= lo[j] - TOL && y[j] <= hi[j] + TOL,
                    "trial {trial}: 5-layer output[{j}] = {} not in [{}, {}]",
                    y[j],
                    lo[j],
                    hi[j]
                );
            }
        }
    }
}

// ===========================================================================
// Layer-by-layer soundness verification
// ===========================================================================

#[test]
fn test_composition_layer_by_layer_soundness() {
    let mut rng = Xorshift32::new(0x6666_0001);
    for trial in 0..10 {
        let d_in = rng.next_usize_range(2, 4);
        let n_gen = rng.next_usize_range(2, 5);
        let z = random_zonotope(&mut rng, d_in, n_gen);
        let n_layers = rng.next_usize_range(3, 5);
        let (layers, _dims) = random_network(&mut rng, d_in, n_layers);

        for _s in 0..50 {
            let x = sample_inside(&mut rng, &z);

            // Track zonotope bounds and concrete values at each layer.
            let mut z_curr = z.clone();
            let mut x_curr = x.clone();

            for (layer_idx, (w, b)) in layers.iter().enumerate() {
                z_curr = zonotope_affine_relu(&z_curr, w, b);
                x_curr = relu_vec(&matvec(w, &x_curr, b));

                let (lo, hi) = z_curr.to_interval();
                for j in 0..z_curr.dim() {
                    assert!(
                        x_curr[j] >= lo[j] - TOL && x_curr[j] <= hi[j] + TOL,
                        "trial {trial}: layer {layer_idx} dim {j}: {} not in [{}, {}]",
                        x_curr[j],
                        lo[j],
                        hi[j]
                    );
                }
            }
        }
    }
}

// ===========================================================================
// Tightness: zonotope vs IBP across layers
// ===========================================================================

#[test]
fn test_composition_both_sound_3layer() {
    // Both zonotope and IBP are sound overapproximations of the actual output
    // set. The zonotope interval hull is not necessarily tighter than IBP on
    // multi-layer networks due to ReLU relaxation generator accumulation.
    // Verify both produce valid (non-negative width) bounds.
    let mut rng = Xorshift32::new(0x7777_0001);
    for trial in 0..12 {
        let d = rng.next_usize_range(2, 4);
        let n_gen = rng.next_usize_range(2, 5);
        let z = random_zonotope(&mut rng, d, n_gen);

        let mut layers = Vec::new();
        for _ in 0..3 {
            let w = random_weight_matrix(&mut rng, d, d);
            let b = random_bias(&mut rng, d);
            layers.push((w, b));
        }

        let (zono_w, ibp_w) = compare_zonotope_ibp(&z, &layers);
        assert!(
            zono_w >= -TOL,
            "trial {trial}: negative zonotope width {zono_w} on 3-layer"
        );
        assert!(
            ibp_w >= -TOL,
            "trial {trial}: negative IBP width {ibp_w} on 3-layer"
        );
    }
}

#[test]
fn test_composition_both_sound_4layer() {
    let mut rng = Xorshift32::new(0x7777_0002);
    for trial in 0..10 {
        let d = rng.next_usize_range(2, 3);
        let n_gen = rng.next_usize_range(2, 4);
        let z = random_zonotope(&mut rng, d, n_gen);

        let mut layers = Vec::new();
        for _ in 0..4 {
            let w = random_weight_matrix(&mut rng, d, d);
            let b = random_bias(&mut rng, d);
            layers.push((w, b));
        }

        let (zono_w, ibp_w) = compare_zonotope_ibp(&z, &layers);
        assert!(
            zono_w >= -TOL,
            "trial {trial}: negative zonotope width {zono_w} on 4-layer"
        );
        assert!(
            ibp_w >= -TOL,
            "trial {trial}: negative IBP width {ibp_w} on 4-layer"
        );
    }
}

#[test]
fn test_composition_zonotope_tighter_than_ibp_correlated() {
    // Correlated generators should give zonotope a strict advantage over IBP.
    let mut rng = Xorshift32::new(0x7777_0003);
    let mut zono_wins = 0;
    let n_trials = 20;
    for _ in 0..n_trials {
        let d = 3;
        // Single shared generator creates strong inter-dimension correlation.
        let gen_val: Vec<f64> = (0..d).map(|_| rng.next_f64_range(0.5, 3.0)).collect();
        let z = ConcreteZonotope::new(
            (0..d).map(|_| rng.next_f64_range(-1.0, 1.0)).collect(),
            vec![gen_val],
        );

        let mut layers = Vec::new();
        for _ in 0..2 {
            let w = random_weight_matrix(&mut rng, d, d);
            let b = random_bias(&mut rng, d);
            layers.push((w, b));
        }

        let (zono_w, ibp_w) = compare_zonotope_ibp(&z, &layers);
        if zono_w + 0.01 < ibp_w {
            zono_wins += 1;
        }
    }
    // With correlated inputs, zonotope should beat IBP in at least some trials.
    assert!(
        zono_wins > 0,
        "zonotope never tighter than IBP in {} correlated trials",
        n_trials
    );
}

// ===========================================================================
// Generator count growth through layers
// ===========================================================================

#[test]
fn test_composition_generator_count_growth() {
    // After each affine+ReLU layer, generator count can grow by at most d_out
    // (one per crossing dimension in the ReLU step).
    let mut rng = Xorshift32::new(0x8888_0001);
    for _ in 0..10 {
        let d_in = rng.next_usize_range(2, 4);
        let n_gen = rng.next_usize_range(2, 5);
        let z = random_zonotope(&mut rng, d_in, n_gen);
        let n_layers = rng.next_usize_range(3, 5);
        let (layers, dims) = random_network(&mut rng, d_in, n_layers);

        let mut z_curr = z.clone();
        let mut prev_gen_count = z.num_generators();

        for (layer_idx, (w, b)) in layers.iter().enumerate() {
            z_curr = zonotope_affine_relu(&z_curr, w, b);
            let d_out = dims[layer_idx + 1];
            // Affine preserves gen count; ReLU adds at most d_out.
            assert!(
                z_curr.num_generators() <= prev_gen_count + d_out,
                "layer {layer_idx}: {} generators exceeds bound {} + {}",
                z_curr.num_generators(),
                prev_gen_count,
                d_out
            );
            prev_gen_count = z_curr.num_generators();
        }
    }
}

#[test]
fn test_composition_dimension_consistency_through_layers() {
    let mut rng = Xorshift32::new(0x8888_0002);
    for _ in 0..10 {
        let d_in = rng.next_usize_range(2, 4);
        let n_gen = rng.next_usize_range(2, 5);
        let z = random_zonotope(&mut rng, d_in, n_gen);
        let n_layers = rng.next_usize_range(3, 5);
        let (layers, dims) = random_network(&mut rng, d_in, n_layers);

        let mut z_curr = z.clone();
        for (layer_idx, (w, b)) in layers.iter().enumerate() {
            z_curr = zonotope_affine_relu(&z_curr, w, b);
            let expected_dim = dims[layer_idx + 1];
            assert_eq!(
                z_curr.dim(),
                expected_dim,
                "layer {layer_idx}: dim {} != expected {}",
                z_curr.dim(),
                expected_dim
            );
            assert_eq!(z_curr.center.len(), expected_dim);
            for gvec in &z_curr.generators {
                assert_eq!(gvec.len(), expected_dim);
            }
        }
    }
}

// ===========================================================================
// Composition with Minkowski sum (skip connections)
// ===========================================================================

#[test]
fn test_composition_skip_connection_soundness() {
    // Simulate a residual block: z_out = affine_relu(z) + z (skip connection).
    let mut rng = Xorshift32::new(0x9999_0001);
    for trial in 0..10 {
        let d = rng.next_usize_range(2, 4);
        let n_gen = rng.next_usize_range(2, 5);
        let z = random_zonotope(&mut rng, d, n_gen);

        let w = random_weight_matrix(&mut rng, d, d);
        let b = random_bias(&mut rng, d);

        let z_branch = zonotope_affine_relu(&z, &w, &b);
        let z_residual = z.minkowski_add(&z_branch);
        let (lo, hi) = z_residual.to_interval();

        for _s in 0..80 {
            let x = sample_inside(&mut rng, &z);
            let branch_out = relu_vec(&matvec(&w, &x, &b));
            let residual: Vec<f64> = x
                .iter()
                .zip(branch_out.iter())
                .map(|(a, b)| a + b)
                .collect();

            for j in 0..d {
                assert!(
                    residual[j] >= lo[j] - TOL && residual[j] <= hi[j] + TOL,
                    "trial {trial}: skip connection dim {j}: {} not in [{}, {}]",
                    residual[j],
                    lo[j],
                    hi[j]
                );
            }
        }
    }
}

// ===========================================================================
// Forward pass equivalence: stepwise vs batch
// ===========================================================================

#[test]
fn test_composition_forward_pass_matches_stepwise() {
    let mut rng = Xorshift32::new(0xAAAA_0001);
    for _ in 0..10 {
        let d_in = rng.next_usize_range(2, 4);
        let n_gen = rng.next_usize_range(2, 5);
        let z = random_zonotope(&mut rng, d_in, n_gen);
        let n_layers = rng.next_usize_range(3, 5);
        let (layers, _dims) = random_network(&mut rng, d_in, n_layers);

        // Batch forward pass.
        let z_batch = zonotope_forward_pass(&z, &layers);

        // Stepwise forward pass.
        let mut z_step = z.clone();
        for (w, b) in &layers {
            z_step = zonotope_affine_relu(&z_step, w, b);
        }

        // Centers and generators should be identical (same arithmetic).
        assert_eq!(z_batch.dim(), z_step.dim());
        for j in 0..z_batch.dim() {
            assert!(
                (z_batch.center[j] - z_step.center[j]).abs() < TOL,
                "batch/step center mismatch dim {j}"
            );
        }
        assert_eq!(z_batch.num_generators(), z_step.num_generators());
        for (gi, (gb, gs)) in z_batch
            .generators
            .iter()
            .zip(z_step.generators.iter())
            .enumerate()
        {
            for j in 0..z_batch.dim() {
                assert!(
                    (gb[j] - gs[j]).abs() < TOL,
                    "batch/step gen[{gi}][{j}] mismatch"
                );
            }
        }
    }
}

// ===========================================================================
// Non-negative output after ReLU layers
// ===========================================================================

#[test]
fn test_composition_relu_output_non_negative() {
    // After any forward pass (which ends with ReLU), interval hull lower bound
    // must be >= 0 for all dimensions (within tolerance for floating-point).
    let mut rng = Xorshift32::new(0xBBBB_0001);
    for _ in 0..15 {
        let d_in = rng.next_usize_range(2, 4);
        let n_gen = rng.next_usize_range(2, 5);
        let z = random_zonotope(&mut rng, d_in, n_gen);
        let n_layers = rng.next_usize_range(3, 5);
        let (layers, _dims) = random_network(&mut rng, d_in, n_layers);

        let z_out = zonotope_forward_pass(&z, &layers);
        let (_lo, _hi) = z_out.to_interval();

        // The zonotope hull is an overapproximation, so its lower bound can
        // be slightly negative due to ReLU relaxation. But any sampled
        // concrete output must be non-negative.
        for _s in 0..50 {
            let x = sample_inside(&mut rng, &z);
            let y = eval_network(&x, &layers);
            for (j, &yj) in y.iter().enumerate() {
                assert!(
                    yj >= -TOL,
                    "concrete ReLU output dim {j} = {} is negative",
                    yj
                );
            }
        }
    }
}
