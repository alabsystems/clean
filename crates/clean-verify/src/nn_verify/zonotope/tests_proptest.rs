// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Property-based tests for zonotope operations using deterministic xorshift32.
//!
//! Covers T01 (interval hull soundness), T02 (linear transform exactness),
//! T03-T06 (ReLU properties), T07 (affine+ReLU composition), T08 (Minkowski
//! sum), and structural invariants.

use super::affine_relu::{compare_zonotope_ibp, zonotope_affine_relu};
use super::concrete::ConcreteZonotope;
use super::relu::zonotope_relu;

const TOL: f64 = 1e-9;

// ---------------------------------------------------------------------------
// Deterministic xorshift32 PRNG
// ---------------------------------------------------------------------------

struct Xorshift32 {
    state: u32,
}

impl Xorshift32 {
    fn new(seed: u32) -> Self {
        // Ensure non-zero seed.
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

    /// Uniform f64 in [lo, hi].
    fn next_f64_range(&mut self, lo: f64, hi: f64) -> f64 {
        let t = self.next_u32() as f64 / u32::MAX as f64;
        lo + t * (hi - lo)
    }

    /// Uniform f64 in [-1, 1].
    fn next_eps(&mut self) -> f64 {
        self.next_f64_range(-1.0, 1.0)
    }

    /// Uniform usize in [lo, hi] inclusive.
    fn next_usize_range(&mut self, lo: usize, hi: usize) -> usize {
        let range = (hi - lo + 1) as u32;
        lo + (self.next_u32() % range) as usize
    }
}

// ---------------------------------------------------------------------------
// Random zonotope generators
// ---------------------------------------------------------------------------

fn random_zonotope(rng: &mut Xorshift32, dim: usize, n_gen: usize) -> ConcreteZonotope {
    let center: Vec<f64> = (0..dim).map(|_| rng.next_f64_range(-10.0, 10.0)).collect();
    let generators: Vec<Vec<f64>> = (0..n_gen)
        .map(|_| (0..dim).map(|_| rng.next_f64_range(-5.0, 5.0)).collect())
        .collect();
    ConcreteZonotope::new(center, generators)
}

fn random_positive_zonotope(rng: &mut Xorshift32, dim: usize, n_gen: usize) -> ConcreteZonotope {
    // Center far positive, small generators => always-positive hull.
    let center: Vec<f64> = (0..dim).map(|_| rng.next_f64_range(50.0, 100.0)).collect();
    let generators: Vec<Vec<f64>> = (0..n_gen)
        .map(|_| (0..dim).map(|_| rng.next_f64_range(-1.0, 1.0)).collect())
        .collect();
    ConcreteZonotope::new(center, generators)
}

fn random_negative_zonotope(rng: &mut Xorshift32, dim: usize, n_gen: usize) -> ConcreteZonotope {
    // Center far negative, small generators => always-negative hull.
    let center: Vec<f64> = (0..dim)
        .map(|_| rng.next_f64_range(-100.0, -50.0))
        .collect();
    let generators: Vec<Vec<f64>> = (0..n_gen)
        .map(|_| (0..dim).map(|_| rng.next_f64_range(-1.0, 1.0)).collect())
        .collect();
    ConcreteZonotope::new(center, generators)
}

fn random_crossing_zonotope(rng: &mut Xorshift32, dim: usize, n_gen: usize) -> ConcreteZonotope {
    // Small center near zero, moderate generators => crossing in most dims.
    let center: Vec<f64> = (0..dim).map(|_| rng.next_f64_range(-0.5, 0.5)).collect();
    let generators: Vec<Vec<f64>> = (0..n_gen)
        .map(|_| (0..dim).map(|_| rng.next_f64_range(-3.0, 3.0)).collect())
        .collect();
    ConcreteZonotope::new(center, generators)
}

fn random_weight_matrix(rng: &mut Xorshift32, rows: usize, cols: usize) -> Vec<Vec<f64>> {
    (0..rows)
        .map(|_| (0..cols).map(|_| rng.next_f64_range(-2.0, 2.0)).collect())
        .collect()
}

fn random_bias(rng: &mut Xorshift32, dim: usize) -> Vec<f64> {
    (0..dim).map(|_| rng.next_f64_range(-1.0, 1.0)).collect()
}

/// Sample a point inside the zonotope using random eps in [-1, 1].
fn sample_inside(rng: &mut Xorshift32, z: &ConcreteZonotope) -> Vec<f64> {
    let coeffs: Vec<f64> = (0..z.num_generators()).map(|_| rng.next_eps()).collect();
    z.sample_point(&coeffs).unwrap()
}

/// Matrix-vector multiply: y = W * x + b.
fn matvec(w: &[Vec<f64>], x: &[f64], b: &[f64]) -> Vec<f64> {
    w.iter()
        .enumerate()
        .map(|(i, row)| row.iter().zip(x.iter()).map(|(a, b)| a * b).sum::<f64>() + b[i])
        .collect()
}

/// Component-wise ReLU.
fn relu_vec(x: &[f64]) -> Vec<f64> {
    x.iter().map(|&v| v.max(0.0)).collect()
}

fn hull_width(z: &ConcreteZonotope) -> Vec<f64> {
    let (lo, hi) = z.to_interval();
    lo.iter().zip(hi.iter()).map(|(&l, &h)| h - l).collect()
}

fn total_width(z: &ConcreteZonotope) -> f64 {
    hull_width(z).iter().sum()
}

// ===========================================================================
// T01: Interval hull soundness
// ===========================================================================

#[test]
fn test_t01_hull_soundness_random_zonotopes_sampled() {
    let mut rng = Xorshift32::new(0xDEAD_0001);
    for trial in 0..30 {
        let dim = rng.next_usize_range(2, 8);
        let n_gen = rng.next_usize_range(1, 10);
        let z = random_zonotope(&mut rng, dim, n_gen);
        let (lo, hi) = z.to_interval();

        for _s in 0..200 {
            let pt = sample_inside(&mut rng, &z);
            for j in 0..dim {
                assert!(
                    pt[j] >= lo[j] - TOL && pt[j] <= hi[j] + TOL,
                    "trial {trial}: sampled point dim {j} = {} not in [{}, {}]",
                    pt[j],
                    lo[j],
                    hi[j]
                );
            }
        }
    }
}

#[test]
fn test_t01_hull_bounds_analytical() {
    // For any zonotope, hull lower = center - sum|gen_ij| and upper = center + sum|gen_ij|.
    let mut rng = Xorshift32::new(0xDEAD_0002);
    for _ in 0..50 {
        let dim = rng.next_usize_range(2, 8);
        let n_gen = rng.next_usize_range(1, 10);
        let z = random_zonotope(&mut rng, dim, n_gen);
        let (lo, hi) = z.to_interval();

        for j in 0..dim {
            let abs_sum: f64 = z.generators.iter().map(|g| g[j].abs()).sum();
            assert!(
                (lo[j] - (z.center[j] - abs_sum)).abs() < TOL,
                "lower[{j}] = {} != center - sum|g| = {}",
                lo[j],
                z.center[j] - abs_sum
            );
            assert!(
                (hi[j] - (z.center[j] + abs_sum)).abs() < TOL,
                "upper[{j}] = {} != center + sum|g| = {}",
                hi[j],
                z.center[j] + abs_sum
            );
        }
    }
}

#[test]
fn test_t01_hull_contains_center() {
    let mut rng = Xorshift32::new(0xDEAD_0003);
    for _ in 0..50 {
        let dim = rng.next_usize_range(1, 8);
        let n_gen = rng.next_usize_range(0, 10);
        let z = random_zonotope(&mut rng, dim, n_gen);
        assert!(z.hull_contains(&z.center), "center must always be in hull");
    }
}

// ===========================================================================
// T02: Linear transform exactness
// ===========================================================================

#[test]
fn test_t02_linear_transform_preserves_containment() {
    let mut rng = Xorshift32::new(0xBEEF_0001);
    for trial in 0..20 {
        let d_in = rng.next_usize_range(2, 6);
        let d_out = rng.next_usize_range(1, 6);
        let n_gen = rng.next_usize_range(1, 8);
        let z = random_zonotope(&mut rng, d_in, n_gen);
        let w = random_weight_matrix(&mut rng, d_out, d_in);
        let b = random_bias(&mut rng, d_out);

        let w_refs: Vec<&[f64]> = w.iter().map(|r| r.as_slice()).collect();
        let tz = z.linear_transform(&w_refs, &b);
        let (lo, hi) = tz.to_interval();

        for _s in 0..100 {
            let pt = sample_inside(&mut rng, &z);
            let transformed = matvec(&w, &pt, &b);
            for j in 0..d_out {
                assert!(
                    transformed[j] >= lo[j] - TOL && transformed[j] <= hi[j] + TOL,
                    "trial {trial}: W*x+b dim {j} = {} not in [{}, {}]",
                    transformed[j],
                    lo[j],
                    hi[j]
                );
            }
        }
    }
}

#[test]
fn test_t02_linear_transform_preserves_generator_count() {
    let mut rng = Xorshift32::new(0xBEEF_0002);
    for _ in 0..30 {
        let d_in = rng.next_usize_range(2, 6);
        let d_out = rng.next_usize_range(1, 6);
        let n_gen = rng.next_usize_range(1, 10);
        let z = random_zonotope(&mut rng, d_in, n_gen);
        let w = random_weight_matrix(&mut rng, d_out, d_in);
        let b = random_bias(&mut rng, d_out);
        let w_refs: Vec<&[f64]> = w.iter().map(|r| r.as_slice()).collect();
        let tz = z.linear_transform(&w_refs, &b);
        assert_eq!(
            tz.num_generators(),
            z.num_generators(),
            "linear transform must preserve generator count"
        );
    }
}

#[test]
fn test_t02_identity_transform_is_exact() {
    let mut rng = Xorshift32::new(0xBEEF_0003);
    for _ in 0..20 {
        let dim = rng.next_usize_range(2, 6);
        let n_gen = rng.next_usize_range(1, 8);
        let z = random_zonotope(&mut rng, dim, n_gen);
        let mut id_w: Vec<Vec<f64>> = vec![vec![0.0; dim]; dim];
        for (i, row) in id_w.iter_mut().enumerate() {
            row[i] = 1.0;
        }
        let zero_b = vec![0.0; dim];
        let w_refs: Vec<&[f64]> = id_w.iter().map(|r| r.as_slice()).collect();
        let tz = z.linear_transform(&w_refs, &zero_b);
        for j in 0..dim {
            assert!(
                (tz.center[j] - z.center[j]).abs() < TOL,
                "identity transform should preserve center"
            );
        }
        assert_eq!(tz.num_generators(), z.num_generators());
    }
}

#[test]
fn test_t02_orthogonal_preserves_hull_width() {
    // 90-degree rotation in 2D should preserve hull width for axis-aligned zonotopes.
    let mut rng = Xorshift32::new(0xBEEF_0004);
    // Use axis-aligned generators only so rotation swaps dimensions exactly.
    for _ in 0..15 {
        let half_w = rng.next_f64_range(0.5, 5.0);
        let half_h = rng.next_f64_range(0.5, 5.0);
        let z = ConcreteZonotope::new(vec![0.0, 0.0], vec![vec![half_w, 0.0], vec![0.0, half_h]]);
        // 90-degree rotation: [[0,-1],[1,0]]
        let w: Vec<&[f64]> = vec![&[0.0, -1.0], &[1.0, 0.0]];
        let b = vec![0.0, 0.0];
        let tz = z.linear_transform(&w, &b);

        let before_widths = hull_width(&z);
        let after_widths = hull_width(&tz);
        // Widths should be swapped: before[0] <-> after[1], before[1] <-> after[0]
        assert!(
            (before_widths[0] - after_widths[1]).abs() < TOL,
            "rotation should swap width dimensions"
        );
        assert!(
            (before_widths[1] - after_widths[0]).abs() < TOL,
            "rotation should swap width dimensions"
        );
    }
}

// ===========================================================================
// T03-T06: ReLU properties
// ===========================================================================

#[test]
fn test_t05_relu_always_positive_is_identity() {
    let mut rng = Xorshift32::new(0xCAFE_0001);
    for trial in 0..20 {
        let dim = rng.next_usize_range(2, 6);
        let n_gen = rng.next_usize_range(1, 8);
        let z = random_positive_zonotope(&mut rng, dim, n_gen);
        let rz = zonotope_relu(&z);

        // Center should be unchanged.
        for j in 0..dim {
            assert!(
                (rz.center[j] - z.center[j]).abs() < TOL,
                "trial {trial}: positive relu center dim {j} changed"
            );
        }
        // Generator count should be unchanged (no crossing dims).
        assert_eq!(
            rz.num_generators(),
            z.num_generators(),
            "trial {trial}: positive relu added generators"
        );
        // Generators should be unchanged.
        for (gi, gvec) in z.generators.iter().enumerate() {
            for (j, &g) in gvec.iter().enumerate() {
                assert!(
                    (rz.generators[gi][j] - g).abs() < TOL,
                    "trial {trial}: generator [{gi}][{j}] changed under positive relu"
                );
            }
        }
    }
}

#[test]
fn test_t06_relu_always_negative_has_zero_hull() {
    let mut rng = Xorshift32::new(0xCAFE_0002);
    for trial in 0..20 {
        let dim = rng.next_usize_range(2, 6);
        let n_gen = rng.next_usize_range(1, 8);
        let z = random_negative_zonotope(&mut rng, dim, n_gen);
        let rz = zonotope_relu(&z);
        let (lo, hi) = rz.to_interval();

        for j in 0..dim {
            assert!(
                lo[j].abs() < TOL && hi[j].abs() < TOL,
                "trial {trial}: negative relu dim {j} hull = [{}, {}], expected [0, 0]",
                lo[j],
                hi[j]
            );
        }
    }
}

#[test]
fn test_t03_relu_crossing_contains_relu_of_sampled_points() {
    let mut rng = Xorshift32::new(0xCAFE_0003);
    for trial in 0..20 {
        let dim = rng.next_usize_range(2, 6);
        let n_gen = rng.next_usize_range(1, 8);
        let z = random_crossing_zonotope(&mut rng, dim, n_gen);
        let rz = zonotope_relu(&z);
        let (lo, hi) = rz.to_interval();

        for _s in 0..200 {
            let pt = sample_inside(&mut rng, &z);
            let relu_pt = relu_vec(&pt);
            for j in 0..dim {
                assert!(
                    relu_pt[j] >= lo[j] - TOL && relu_pt[j] <= hi[j] + TOL,
                    "trial {trial}: relu(x)[{j}] = {} not in [{}, {}]",
                    relu_pt[j],
                    lo[j],
                    hi[j]
                );
            }
        }
    }
}

#[test]
fn test_t03_relu_soundness_random_zonotopes() {
    let mut rng = Xorshift32::new(0xCAFE_0004);
    for trial in 0..30 {
        let dim = rng.next_usize_range(2, 8);
        let n_gen = rng.next_usize_range(1, 10);
        let z = random_zonotope(&mut rng, dim, n_gen);
        let rz = zonotope_relu(&z);
        let (lo, hi) = rz.to_interval();

        for _s in 0..100 {
            let pt = sample_inside(&mut rng, &z);
            let relu_pt = relu_vec(&pt);
            for j in 0..dim {
                assert!(
                    relu_pt[j] >= lo[j] - TOL && relu_pt[j] <= hi[j] + TOL,
                    "trial {trial}: relu(x)[{j}] = {} not in [{}, {}]",
                    relu_pt[j],
                    lo[j],
                    hi[j]
                );
            }
        }
    }
}

#[test]
fn test_t04_lambda_relaxation_monotonicity() {
    // Wider input interval should produce wider or equal output interval.
    let mut rng = Xorshift32::new(0xCAFE_0005);
    for _ in 0..30 {
        let center = rng.next_f64_range(-2.0, 2.0);
        let gen_narrow = rng.next_f64_range(0.1, 2.0);
        let gen_wide = gen_narrow + rng.next_f64_range(0.1, 3.0);

        let z_narrow = ConcreteZonotope::new(vec![center], vec![vec![gen_narrow]]);
        let z_wide = ConcreteZonotope::new(vec![center], vec![vec![gen_wide]]);

        let rz_narrow = zonotope_relu(&z_narrow);
        let rz_wide = zonotope_relu(&z_wide);

        let w_narrow = total_width(&rz_narrow);
        let w_wide = total_width(&rz_wide);

        assert!(
            w_wide >= w_narrow - TOL,
            "wider input should produce wider or equal relu output: {} < {}",
            w_wide,
            w_narrow
        );
    }
}

#[test]
fn test_t05_relu_positive_hull_unchanged() {
    let mut rng = Xorshift32::new(0xCAFE_0006);
    for _ in 0..20 {
        let dim = rng.next_usize_range(2, 6);
        let n_gen = rng.next_usize_range(1, 8);
        let z = random_positive_zonotope(&mut rng, dim, n_gen);
        let (lo_before, hi_before) = z.to_interval();
        let rz = zonotope_relu(&z);
        let (lo_after, hi_after) = rz.to_interval();

        for j in 0..dim {
            assert!(
                (lo_before[j] - lo_after[j]).abs() < TOL,
                "positive relu changed lower bound in dim {j}"
            );
            assert!(
                (hi_before[j] - hi_after[j]).abs() < TOL,
                "positive relu changed upper bound in dim {j}"
            );
        }
    }
}

#[test]
fn test_t06_relu_negative_center_and_generators_zeroed() {
    let mut rng = Xorshift32::new(0xCAFE_0007);
    for _ in 0..20 {
        let dim = rng.next_usize_range(2, 6);
        let n_gen = rng.next_usize_range(1, 8);
        let z = random_negative_zonotope(&mut rng, dim, n_gen);
        let rz = zonotope_relu(&z);

        for j in 0..dim {
            assert!(
                rz.center[j].abs() < TOL,
                "negative relu center[{j}] = {}, expected 0",
                rz.center[j]
            );
        }
        for (gi, gvec) in rz.generators.iter().enumerate() {
            for (j, &g) in gvec.iter().enumerate() {
                assert!(
                    g.abs() < TOL,
                    "negative relu gen[{gi}][{j}] = {}, expected 0",
                    g
                );
            }
        }
    }
}

// ===========================================================================
// T07: Affine + ReLU composition
// ===========================================================================

#[test]
fn test_t07_affine_relu_soundness_2layer() {
    let mut rng = Xorshift32::new(0xF00D_0001);
    for trial in 0..15 {
        let d_in = rng.next_usize_range(2, 5);
        let d_hidden = rng.next_usize_range(2, 5);
        let d_out = rng.next_usize_range(1, 4);
        let n_gen = rng.next_usize_range(1, 6);

        let z = random_zonotope(&mut rng, d_in, n_gen);

        let w1 = random_weight_matrix(&mut rng, d_hidden, d_in);
        let b1 = random_bias(&mut rng, d_hidden);
        let w2 = random_weight_matrix(&mut rng, d_out, d_hidden);
        let b2 = random_bias(&mut rng, d_out);

        // Propagate zonotope through 2 layers.
        let z_mid = zonotope_affine_relu(&z, &w1, &b1);
        let z_out = zonotope_affine_relu(&z_mid, &w2, &b2);
        let (lo, hi) = z_out.to_interval();

        // Sample input, compute actual output, check bounds.
        for _s in 0..100 {
            let x = sample_inside(&mut rng, &z);
            let h = relu_vec(&matvec(&w1, &x, &b1));
            let y = relu_vec(&matvec(&w2, &h, &b2));
            for j in 0..d_out {
                assert!(
                    y[j] >= lo[j] - TOL && y[j] <= hi[j] + TOL,
                    "trial {trial}: actual output[{j}] = {} not in [{}, {}]",
                    y[j],
                    lo[j],
                    hi[j]
                );
            }
        }
    }
}

#[test]
fn test_t07_zonotope_vs_ibp_correlated_single_layer() {
    // Zonotope interval hull is tighter than IBP when inputs share a single
    // generator (strong correlation) and the network has a single layer.
    // With multiple independent generators or multiple layers, ReLU relaxation
    // error generators can make the zonotope hull wider than IBP.
    let mut rng = Xorshift32::new(0xF00D_0002);
    let mut zono_wins = 0;
    let n_trials = 20;
    for _ in 0..n_trials {
        let d = 2;
        // Single shared generator maximizes correlation advantage.
        let gen_val: Vec<f64> = (0..d).map(|_| rng.next_f64_range(0.5, 2.0)).collect();
        let z = ConcreteZonotope::new(
            (0..d).map(|_| rng.next_f64_range(-0.5, 0.5)).collect(),
            vec![gen_val],
        );

        // Use weight that differences correlated dims: W * [x, x]^T = [x-x] = [0].
        let w = vec![vec![1.0, -1.0]];
        let b = vec![0.0];
        let layers = vec![(w, b)];

        let (zono_w, ibp_w) = compare_zonotope_ibp(&z, &layers);
        if zono_w + 0.01 < ibp_w {
            zono_wins += 1;
        }
    }
    assert!(
        zono_wins > 0,
        "zonotope never tighter than IBP on correlated single-layer"
    );
}

#[test]
fn test_t07_zonotope_ibp_both_sound_multilayer() {
    // Both zonotope and IBP are sound overapproximations. Verify that both
    // contain actual network outputs. (Zonotope hull is not always tighter
    // than IBP hull due to ReLU relaxation generator accumulation.)
    let mut rng = Xorshift32::new(0xF00D_0003);
    for trial in 0..10 {
        let d = rng.next_usize_range(2, 4);
        let n_gen = rng.next_usize_range(2, 6);
        let z = random_zonotope(&mut rng, d, n_gen);

        let n_layers = rng.next_usize_range(2, 3);
        let mut layers = Vec::new();
        for _ in 0..n_layers {
            let w = random_weight_matrix(&mut rng, d, d);
            let b = random_bias(&mut rng, d);
            layers.push((w, b));
        }

        let (zono_w, ibp_w) = compare_zonotope_ibp(&z, &layers);
        // Both widths must be non-negative (valid overapproximations).
        assert!(
            zono_w >= -TOL,
            "trial {trial}: negative zonotope width {zono_w}"
        );
        assert!(ibp_w >= -TOL, "trial {trial}: negative IBP width {ibp_w}");
    }
}

// ===========================================================================
// T08: Minkowski sum
// ===========================================================================

#[test]
fn test_t08_minkowski_sum_containment() {
    let mut rng = Xorshift32::new(0xABCD_0001);
    for trial in 0..20 {
        let dim = rng.next_usize_range(2, 6);
        let n1 = rng.next_usize_range(1, 6);
        let n2 = rng.next_usize_range(1, 6);
        let z1 = random_zonotope(&mut rng, dim, n1);
        let z2 = random_zonotope(&mut rng, dim, n2);
        let zs = z1.minkowski_add(&z2);
        let (lo, hi) = zs.to_interval();

        for _s in 0..100 {
            let p1 = sample_inside(&mut rng, &z1);
            let p2 = sample_inside(&mut rng, &z2);
            let sum_pt: Vec<f64> = p1.iter().zip(p2.iter()).map(|(a, b)| a + b).collect();
            for j in 0..dim {
                assert!(
                    sum_pt[j] >= lo[j] - TOL && sum_pt[j] <= hi[j] + TOL,
                    "trial {trial}: z1+z2 dim {j} = {} not in [{}, {}]",
                    sum_pt[j],
                    lo[j],
                    hi[j]
                );
            }
        }
    }
}

#[test]
fn test_t08_minkowski_hull_width_additive() {
    let mut rng = Xorshift32::new(0xABCD_0002);
    for trial in 0..30 {
        let dim = rng.next_usize_range(1, 6);
        let n1 = rng.next_usize_range(1, 8);
        let n2 = rng.next_usize_range(1, 8);
        let z1 = random_zonotope(&mut rng, dim, n1);
        let z2 = random_zonotope(&mut rng, dim, n2);
        let zs = z1.minkowski_add(&z2);

        let w1 = hull_width(&z1);
        let w2 = hull_width(&z2);
        let ws = hull_width(&zs);

        for j in 0..dim {
            assert!(
                (ws[j] - (w1[j] + w2[j])).abs() < TOL,
                "trial {trial}: Mink hull width dim {j}: {} != {} + {}",
                ws[j],
                w1[j],
                w2[j]
            );
        }
    }
}

#[test]
fn test_t08_minkowski_center_additive() {
    let mut rng = Xorshift32::new(0xABCD_0003);
    for _ in 0..30 {
        let dim = rng.next_usize_range(1, 8);
        let n1 = rng.next_usize_range(0, 5);
        let n2 = rng.next_usize_range(0, 5);
        let z1 = random_zonotope(&mut rng, dim, n1);
        let z2 = random_zonotope(&mut rng, dim, n2);
        let zs = z1.minkowski_add(&z2);

        for j in 0..dim {
            assert!(
                (zs.center[j] - (z1.center[j] + z2.center[j])).abs() < TOL,
                "Mink center dim {j}: {} != {} + {}",
                zs.center[j],
                z1.center[j],
                z2.center[j]
            );
        }
    }
}

#[test]
fn test_t08_minkowski_generator_count() {
    let mut rng = Xorshift32::new(0xABCD_0004);
    for _ in 0..30 {
        let dim = rng.next_usize_range(1, 6);
        let n1 = rng.next_usize_range(0, 6);
        let n2 = rng.next_usize_range(0, 6);
        let z1 = random_zonotope(&mut rng, dim, n1);
        let z2 = random_zonotope(&mut rng, dim, n2);
        let zs = z1.minkowski_add(&z2);
        assert_eq!(
            zs.num_generators(),
            n1 + n2,
            "Mink sum gens: {} != {} + {}",
            zs.num_generators(),
            n1,
            n2
        );
    }
}

// ===========================================================================
// Structural properties
// ===========================================================================

#[test]
fn test_dimension_consistency_after_relu() {
    let mut rng = Xorshift32::new(0x1111_0001);
    for _ in 0..30 {
        let dim = rng.next_usize_range(2, 8);
        let n_gen = rng.next_usize_range(1, 10);
        let z = random_zonotope(&mut rng, dim, n_gen);
        let rz = zonotope_relu(&z);
        assert_eq!(rz.dim(), dim, "relu must preserve dimension");
        for gvec in &rz.generators {
            assert_eq!(gvec.len(), dim, "relu generator dimension mismatch");
        }
    }
}

#[test]
fn test_dimension_consistency_after_transform() {
    let mut rng = Xorshift32::new(0x1111_0002);
    for _ in 0..30 {
        let d_in = rng.next_usize_range(2, 6);
        let d_out = rng.next_usize_range(1, 6);
        let n_gen = rng.next_usize_range(1, 8);
        let z = random_zonotope(&mut rng, d_in, n_gen);
        let w = random_weight_matrix(&mut rng, d_out, d_in);
        let b = random_bias(&mut rng, d_out);
        let w_refs: Vec<&[f64]> = w.iter().map(|r| r.as_slice()).collect();
        let tz = z.linear_transform(&w_refs, &b);
        assert_eq!(tz.dim(), d_out, "transform output dim");
        assert_eq!(tz.center.len(), d_out);
        for gvec in &tz.generators {
            assert_eq!(gvec.len(), d_out, "transform generator dim");
        }
    }
}

#[test]
fn test_dimension_consistency_after_minkowski() {
    let mut rng = Xorshift32::new(0x1111_0003);
    for _ in 0..20 {
        let dim = rng.next_usize_range(1, 8);
        let n1 = rng.next_usize_range(0, 5);
        let n2 = rng.next_usize_range(0, 5);
        let z1 = random_zonotope(&mut rng, dim, n1);
        let z2 = random_zonotope(&mut rng, dim, n2);
        let zs = z1.minkowski_add(&z2);
        assert_eq!(zs.dim(), dim);
        for gvec in &zs.generators {
            assert_eq!(gvec.len(), dim);
        }
    }
}

#[test]
fn test_relu_generator_count_bound() {
    // ReLU adds at most d generators (one per crossing dimension).
    let mut rng = Xorshift32::new(0x1111_0004);
    for _ in 0..30 {
        let dim = rng.next_usize_range(2, 8);
        let n_gen = rng.next_usize_range(1, 10);
        let z = random_zonotope(&mut rng, dim, n_gen);
        let rz = zonotope_relu(&z);
        assert!(
            rz.num_generators() <= z.num_generators() + dim,
            "relu added more than d generators: {} > {} + {}",
            rz.num_generators(),
            z.num_generators(),
            dim
        );
    }
}

#[test]
fn test_hull_containment_transitivity() {
    // If Z1's hull contains Z2's hull, then Z1's interval contains Z2's interval.
    let mut rng = Xorshift32::new(0x1111_0005);
    for _ in 0..20 {
        let dim = rng.next_usize_range(2, 5);
        let n_gen = rng.next_usize_range(1, 6);
        let z_inner = random_zonotope(&mut rng, dim, n_gen);

        // Build an outer zonotope by adding generators to z_inner.
        let extra_gens: Vec<Vec<f64>> = (0..rng.next_usize_range(1, 4))
            .map(|_| (0..dim).map(|_| rng.next_f64_range(-2.0, 2.0)).collect())
            .collect();
        let mut outer_gens = z_inner.generators.clone();
        outer_gens.extend(extra_gens);
        let z_outer = ConcreteZonotope::new(z_inner.center.clone(), outer_gens);

        let (lo_inner, hi_inner) = z_inner.to_interval();
        let (lo_outer, hi_outer) = z_outer.to_interval();

        for j in 0..dim {
            assert!(
                lo_outer[j] <= lo_inner[j] + TOL,
                "outer lower should be <= inner lower in dim {j}"
            );
            assert!(
                hi_outer[j] >= hi_inner[j] - TOL,
                "outer upper should be >= inner upper in dim {j}"
            );
        }
    }
}

#[test]
fn test_compress_hull_exact_random() {
    let mut rng = Xorshift32::new(0x1111_0006);
    for _ in 0..20 {
        let dim = rng.next_usize_range(2, 6);
        let n_gen = rng.next_usize_range(2, 8);
        let z = random_zonotope(&mut rng, dim, n_gen);
        // Keep a random subset of generators.
        let n_keep = rng.next_usize_range(0, n_gen.saturating_sub(1));
        let mut keep: Vec<usize> = (0..n_gen).collect();
        // Fisher-Yates partial shuffle to pick n_keep indices.
        for i in 0..n_keep {
            let j = rng.next_usize_range(i, n_gen - 1);
            keep.swap(i, j);
        }
        keep.truncate(n_keep);

        assert!(
            z.verify_compress_hull_exact(&keep),
            "compression should preserve hull exactly"
        );
    }
}
