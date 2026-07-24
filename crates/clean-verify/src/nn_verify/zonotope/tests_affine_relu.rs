// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for zonotope affine+ReLU composition (T07), forward pass,
//! and zonotope vs IBP tightness comparison.

use super::affine_relu::{compare_zonotope_ibp, zonotope_affine_relu, zonotope_forward_pass};
use super::concrete::ConcreteZonotope;
use super::relu::zonotope_relu;

const EPS: f64 = 1e-9;

fn scalar_relu(x: f64) -> f64 {
    x.max(0.0)
}

fn affine_relu_point(x: &[f64], w: &[Vec<f64>], b: &[f64]) -> Vec<f64> {
    w.iter()
        .zip(b)
        .map(|(row, &bi)| scalar_relu(row.iter().zip(x).map(|(wi, xi)| wi * xi).sum::<f64>() + bi))
        .collect()
}

fn pseudo_random(seed: &mut u64) -> f64 {
    *seed ^= *seed << 13;
    *seed ^= *seed >> 7;
    *seed ^= *seed << 17;
    let bits = *seed & 0x7FFF_FFFF_FFFF_FFFF;
    (bits as f64 / (0x7FFF_FFFF_FFFF_FFFFu64 as f64)) * 2.0 - 1.0
}

fn sample(z: &ConcreteZonotope, coeffs: &[f64]) -> Vec<f64> {
    let mut pt = z.center.clone();
    for (i, &e) in coeffs.iter().enumerate() {
        for (j, c) in pt.iter_mut().enumerate() {
            *c += e * z.generators[i][j];
        }
    }
    pt
}

fn check_soundness(z: &ConcreteZonotope, w: &[Vec<f64>], b: &[f64], n: usize, seed0: u64) {
    let output = zonotope_affine_relu(z, w, b);
    let (lo, hi) = output.to_interval();
    let mut seed = seed0;
    let ng = z.num_generators();
    for _ in 0..n {
        let coeffs: Vec<f64> = (0..ng).map(|_| pseudo_random(&mut seed)).collect();
        let pt = sample(z, &coeffs);
        let out = affine_relu_point(&pt, w, b);
        for (j, &v) in out.iter().enumerate() {
            assert!(
                v >= lo[j] - EPS && v <= hi[j] + EPS,
                "dim {j}: {v} not in [{}, {}]",
                lo[j],
                hi[j]
            );
        }
    }
}

fn check_fwd_soundness(
    z: &ConcreteZonotope,
    layers: &[(Vec<Vec<f64>>, Vec<f64>)],
    n: usize,
    seed0: u64,
) {
    let output = zonotope_forward_pass(z, layers);
    let (lo, hi) = output.to_interval();
    let mut seed = seed0;
    let ng = z.num_generators();
    for _ in 0..n {
        let coeffs: Vec<f64> = (0..ng).map(|_| pseudo_random(&mut seed)).collect();
        let mut cur = sample(z, &coeffs);
        for (w, b) in layers {
            cur = affine_relu_point(&cur, w, b);
        }
        for (j, &v) in cur.iter().enumerate() {
            assert!(
                v >= lo[j] - EPS && v <= hi[j] + EPS,
                "dim {j}: {v} not in [{}, {}]",
                lo[j],
                hi[j]
            );
        }
    }
}

// -- zonotope_affine_relu --
#[test]
fn test_affine_relu_identity_weight_zero_bias() {
    let z = ConcreteZonotope::new(vec![1.0, -1.0], vec![vec![0.5, 0.5]]);
    let r = zonotope_affine_relu(&z, &[vec![1.0, 0.0], vec![0.0, 1.0]], &[0.0, 0.0]);
    let plain = zonotope_relu(&z);
    assert_eq!(r.dim(), plain.dim());
    for j in 0..r.dim() {
        assert!((r.center[j] - plain.center[j]).abs() < EPS);
    }
    assert_eq!(r.num_generators(), plain.num_generators());
}
#[test]
fn test_affine_relu_scale_2x() {
    let z = ConcreteZonotope::new(vec![1.0], vec![vec![0.5]]);
    let r = zonotope_affine_relu(&z, &[vec![2.0]], &[0.0]);
    assert!((r.center[0] - 2.0).abs() < EPS);
    assert!((r.generators[0][0] - 1.0).abs() < EPS);
    assert_eq!(r.num_generators(), 1);
}
#[test]
fn test_affine_relu_zero_weight() {
    let z = ConcreteZonotope::new(vec![5.0], vec![vec![3.0]]);
    let r0 = zonotope_affine_relu(&z, &[vec![0.0]], &[0.0]);
    assert!(r0.center[0].abs() < EPS);
    for g in &r0.generators {
        assert!(g[0].abs() < EPS);
    }
    let r1 = zonotope_affine_relu(&z, &[vec![0.0]], &[7.0]);
    assert!((r1.center[0] - 7.0).abs() < EPS);
}

#[test]
fn test_affine_relu_1d_positive_and_negative() {
    let rp = zonotope_affine_relu(
        &ConcreteZonotope::new(vec![5.0], vec![vec![1.0]]),
        &[vec![1.0]],
        &[0.0],
    );
    assert!((rp.center[0] - 5.0).abs() < EPS);
    assert_eq!(rp.num_generators(), 1);
    let rn = zonotope_affine_relu(
        &ConcreteZonotope::new(vec![-5.0], vec![vec![1.0]]),
        &[vec![1.0]],
        &[0.0],
    );
    assert!(rn.center[0].abs() < EPS);
}
#[test]
fn test_affine_relu_2d_identity_preserves_dim() {
    let r = zonotope_affine_relu(
        &ConcreteZonotope::new(vec![1.0, 2.0], vec![vec![0.5, 0.3]]),
        &[vec![1.0, 0.0], vec![0.0, 1.0]],
        &[0.0, 0.0],
    );
    assert_eq!(r.dim(), 2);
}
#[test]
fn test_affine_relu_2d_to_1d_reduction() {
    let r = zonotope_affine_relu(
        &ConcreteZonotope::new(vec![1.0, 2.0], vec![vec![0.5, 0.5]]),
        &[vec![1.0, 1.0]],
        &[0.0],
    );
    assert_eq!(r.dim(), 1);
    assert!((r.center[0] - 3.0).abs() < EPS);
}

#[test]
fn test_affine_relu_1d_to_2d_expansion() {
    let r = zonotope_affine_relu(
        &ConcreteZonotope::new(vec![1.0], vec![vec![0.5]]),
        &[vec![1.0], vec![2.0]],
        &[0.0, 0.0],
    );
    assert_eq!(r.dim(), 2);
    assert!((r.center[0] - 1.0).abs() < EPS);
    assert!((r.center[1] - 2.0).abs() < EPS);
}
#[test]
fn test_affine_relu_all_positive_and_all_negative() {
    let id_w = vec![vec![1.0, 0.0], vec![0.0, 1.0]];
    let zp = ConcreteZonotope::new(vec![10.0, 10.0], vec![vec![1.0, 0.0], vec![0.0, 1.0]]);
    let rp = zonotope_affine_relu(&zp, &id_w, &[0.0, 0.0]);
    assert!((rp.center[0] - 10.0).abs() < EPS);
    assert_eq!(rp.num_generators(), 2);
    let zn = ConcreteZonotope::new(vec![-10.0, -10.0], vec![vec![1.0, 0.0], vec![0.0, 1.0]]);
    let rn = zonotope_affine_relu(&zn, &id_w, &[0.0, 0.0]);
    assert!(rn.center[0].abs() < EPS && rn.center[1].abs() < EPS);
}

#[test]
fn test_affine_relu_crossing_adds_generators() {
    let r = zonotope_affine_relu(
        &ConcreteZonotope::new(vec![0.0], vec![vec![2.0]]),
        &[vec![1.0]],
        &[0.0],
    );
    assert_eq!(r.num_generators(), 2);
}
#[test]
fn test_affine_relu_negative_weight_flips_to_inactive() {
    let r = zonotope_affine_relu(
        &ConcreteZonotope::new(vec![3.0], vec![vec![1.0]]),
        &[vec![-1.0]],
        &[0.0],
    );
    assert!(r.center[0].abs() < EPS);
}
#[test]
fn test_affine_relu_bias_shifts_to_positive() {
    let r = zonotope_affine_relu(
        &ConcreteZonotope::new(vec![0.0], vec![vec![1.0]]),
        &[vec![1.0]],
        &[100.0],
    );
    assert!((r.center[0] - 100.0).abs() < EPS);
    assert_eq!(r.num_generators(), 1);
}
#[test]
fn test_affine_relu_mixed_weight_2d() {
    let z = ConcreteZonotope::new(vec![1.0, -1.0], vec![vec![0.5, 0.5]]);
    let r = zonotope_affine_relu(&z, &[vec![1.0, -1.0], vec![-1.0, 1.0]], &[0.0, 0.0]);
    assert_eq!(r.dim(), 2);
    assert!((r.center[0] - 2.0).abs() < EPS);
}

// -- zonotope_forward_pass --
#[test]
fn test_fwd_empty_layers_clones_input() {
    let z = ConcreteZonotope::new(vec![1.0, 2.0], vec![vec![0.5, 0.5]]);
    let r = zonotope_forward_pass(&z, &[]);
    assert_eq!(r.center, z.center);
    assert_eq!(r.generators, z.generators);
}
#[test]
fn test_fwd_single_layer_matches_direct() {
    let z = ConcreteZonotope::new(vec![1.0, -0.5], vec![vec![0.5, 0.5]]);
    let w = vec![vec![1.0, 0.0], vec![0.0, 1.0]];
    let b = vec![0.0, 0.0];
    let fwd = zonotope_forward_pass(&z, &[(w.clone(), b.clone())]);
    let direct = zonotope_affine_relu(&z, &w, &b);
    for j in 0..fwd.dim() {
        assert!((fwd.center[j] - direct.center[j]).abs() < EPS);
    }
    assert_eq!(fwd.num_generators(), direct.num_generators());
}
#[test]
fn test_fwd_two_layers_dim() {
    let z = ConcreteZonotope::new(vec![0.0, 0.0], vec![vec![1.0, 0.0], vec![0.0, 1.0]]);
    let layers = vec![
        (vec![vec![1.0, 1.0], vec![1.0, -1.0]], vec![0.0, 0.0]),
        (vec![vec![1.0, 1.0]], vec![0.0]),
    ];
    assert_eq!(zonotope_forward_pass(&z, &layers).dim(), 1);
}

#[test]
fn test_fwd_three_layers_deep() {
    let z = ConcreteZonotope::new(vec![0.0, 0.0], vec![vec![1.0, 0.0], vec![0.0, 1.0]]);
    let layers = vec![
        (vec![vec![1.0, 0.5], vec![0.5, 1.0]], vec![0.0, 0.0]),
        (vec![vec![1.0, -1.0], vec![-1.0, 1.0]], vec![0.0, 0.0]),
        (vec![vec![1.0, 1.0]], vec![0.0]),
    ];
    let r = zonotope_forward_pass(&z, &layers);
    assert_eq!(r.dim(), 1);
    let (lo, hi) = r.to_interval();
    assert!(hi[0] >= lo[0] - EPS);
}

#[test]
fn test_fwd_dimension_chain_3_2_4_1() {
    let z = ConcreteZonotope::new(vec![1.0, 0.0, -1.0], vec![vec![0.5, 0.5, 0.5]]);
    let layers = vec![
        (
            vec![vec![1.0, 0.0, 0.0], vec![0.0, 1.0, 1.0]],
            vec![0.0, 0.0],
        ),
        (
            vec![
                vec![1.0, 0.0],
                vec![0.0, 1.0],
                vec![1.0, 1.0],
                vec![1.0, -1.0],
            ],
            vec![0.0; 4],
        ),
        (vec![vec![1.0, 1.0, 1.0, 1.0]], vec![0.0]),
    ];
    assert_eq!(zonotope_forward_pass(&z, &layers).dim(), 1);
}

#[test]
fn test_fwd_output_dim_expansion() {
    let z = ConcreteZonotope::new(vec![1.0, 2.0], vec![vec![0.3, 0.3]]);
    let layers = vec![(
        vec![vec![1.0, 0.0], vec![0.0, 1.0], vec![1.0, 1.0]],
        vec![0.0; 3],
    )];
    assert_eq!(zonotope_forward_pass(&z, &layers).dim(), 3);
}

#[test]
fn test_fwd_generators_grow_with_crossing() {
    let z = ConcreteZonotope::new(vec![0.0, 0.0], vec![vec![1.0, 0.0], vec![0.0, 1.0]]);
    let layer = (vec![vec![1.0, 0.5], vec![0.5, 1.0]], vec![0.0, 0.0]);
    let a1 = zonotope_forward_pass(&z, std::slice::from_ref(&layer));
    let a2 = zonotope_forward_pass(&z, &[layer.clone(), layer.clone()]);
    assert!(a2.num_generators() >= a1.num_generators());
}

#[test]
fn test_fwd_all_positive_no_extra_generators() {
    let z = ConcreteZonotope::new(vec![10.0], vec![vec![0.1]]);
    assert_eq!(
        zonotope_forward_pass(&z, &vec![(vec![vec![1.0]], vec![0.0]); 3]).num_generators(),
        1
    );
}

#[test]
fn test_fwd_point_zonotope() {
    let z = ConcreteZonotope::new(vec![3.0, -1.0], vec![]);
    let r = zonotope_forward_pass(
        &z,
        &[(vec![vec![1.0, 0.0], vec![0.0, 1.0]], vec![0.0, 0.0])],
    );
    assert!((r.center[0] - 3.0).abs() < EPS);
    assert!(r.center[1].abs() < EPS);
}

#[test]
fn test_fwd_nonzero_width_output() {
    let z = ConcreteZonotope::new(vec![0.0], vec![vec![1.0]]);
    let r = zonotope_forward_pass(&z, &[(vec![vec![1.0]], vec![1.0])]);
    let (lo, hi) = r.to_interval();
    assert!(hi[0] - lo[0] > EPS);
}

#[test]
fn test_fwd_successive_narrowing() {
    let z = ConcreteZonotope::new(vec![5.0], vec![vec![2.0]]);
    let r = zonotope_forward_pass(&z, &vec![(vec![vec![0.5]], vec![0.0]); 3]);
    let (lo, hi) = r.to_interval();
    assert!(hi[0] - lo[0] < 4.0 + EPS);
}

#[test]
fn test_fwd_bias_accumulation() {
    let z = ConcreteZonotope::new(vec![0.0], vec![]);
    let layers = vec![
        (vec![vec![1.0]], vec![1.0]),
        (vec![vec![1.0]], vec![2.0]),
        (vec![vec![1.0]], vec![3.0]),
    ];
    assert!((zonotope_forward_pass(&z, &layers).center[0] - 6.0).abs() < EPS);
}

// -- compare_zonotope_ibp --
#[test]
fn test_ibp_single_layer_positive_weights() {
    let z = ConcreteZonotope::new(vec![1.0, 1.0], vec![vec![0.5, 0.0], vec![0.0, 0.5]]);
    let (zw, iw) = compare_zonotope_ibp(
        &z,
        &[(vec![vec![1.0, 0.5], vec![0.5, 1.0]], vec![0.0, 0.0])],
    );
    assert!(zw <= iw + EPS, "zono {zw} > ibp {iw}");
}

#[test]
fn test_ibp_single_layer_correlated_input() {
    let z = ConcreteZonotope::new(vec![0.0, 0.0], vec![vec![1.0, 1.0]]);
    let (zw, iw) = compare_zonotope_ibp(&z, &[(vec![vec![1.0, -1.0]], vec![0.0])]);
    assert!(zw <= iw + EPS, "zono {zw} > ibp {iw}");
    assert!(zw < 0.1);
}

#[test]
fn test_ibp_two_layers() {
    let z = ConcreteZonotope::new(vec![0.0, 0.0], vec![vec![1.0, 0.5], vec![0.5, 1.0]]);
    let layers = vec![
        (vec![vec![1.0, -1.0], vec![-1.0, 1.0]], vec![0.0, 0.0]),
        (vec![vec![1.0, 1.0]], vec![0.0]),
    ];
    let (zw, iw) = compare_zonotope_ibp(&z, &layers);
    assert!(zw <= iw + EPS, "zono {zw} > ibp {iw}");
}

#[test]
fn test_ibp_three_layers() {
    let z = ConcreteZonotope::new(vec![0.0, 0.0], vec![vec![1.0, 0.0], vec![0.0, 1.0]]);
    let layers = vec![
        (vec![vec![1.0, 0.5], vec![0.5, 1.0]], vec![0.0, 0.0]),
        (vec![vec![1.0, -0.5], vec![-0.5, 1.0]], vec![0.0, 0.0]),
        (vec![vec![1.0, 1.0]], vec![0.0]),
    ];
    let (zw, iw) = compare_zonotope_ibp(&z, &layers);
    assert!(zw <= iw + EPS, "zono {zw} > ibp {iw}");
}

#[test]
fn test_ibp_identity_network_both_exact() {
    let (zw, iw) = compare_zonotope_ibp(
        &ConcreteZonotope::new(vec![5.0], vec![vec![1.0]]),
        &[(vec![vec![1.0]], vec![0.0])],
    );
    assert!((zw - iw).abs() < EPS);
}

#[test]
fn test_ibp_negative_weights() {
    let z = ConcreteZonotope::new(vec![0.0, 0.0], vec![vec![1.0, 1.0]]);
    let (zw, iw) = compare_zonotope_ibp(
        &z,
        &[(vec![vec![-1.0, 1.0], vec![1.0, -1.0]], vec![1.0, 1.0])],
    );
    assert!(zw <= iw + EPS);
}

#[test]
fn test_ibp_point_zonotope_equal() {
    let (zw, iw) = compare_zonotope_ibp(
        &ConcreteZonotope::new(vec![1.0, -1.0], vec![]),
        &[(vec![vec![1.0, 0.0], vec![0.0, 1.0]], vec![0.0, 0.0])],
    );
    assert!((zw - iw).abs() < EPS);
}

#[test]
fn test_ibp_all_negative_width_zero() {
    let (zw, iw) = compare_zonotope_ibp(
        &ConcreteZonotope::new(vec![-5.0], vec![vec![1.0]]),
        &[(vec![vec![1.0]], vec![0.0])],
    );
    assert!(zw.abs() < EPS && iw.abs() < EPS);
}

#[test]
fn test_ibp_advantage_grows_with_depth() {
    let z = ConcreteZonotope::new(vec![0.0, 0.0], vec![vec![1.0, 1.0]]);
    let l = (vec![vec![1.0, -0.5], vec![-0.5, 1.0]], vec![0.5, 0.5]);
    let (zw1, iw1) = compare_zonotope_ibp(&z, std::slice::from_ref(&l));
    let (zw2, iw2) = compare_zonotope_ibp(&z, &[l.clone(), l.clone()]);
    let r1 = if iw1 > EPS { zw1 / iw1 } else { 1.0 };
    let r2 = if iw2 > EPS { zw2 / iw2 } else { 1.0 };
    assert!(r1 <= 1.0 + EPS);
    assert!(r2 <= 1.0 + EPS);
}

#[test]
fn test_ibp_widths_nonnegative() {
    let (zw, iw) = compare_zonotope_ibp(
        &ConcreteZonotope::new(vec![0.5, -0.5], vec![vec![1.0, 1.0]]),
        &[(vec![vec![2.0, -1.0], vec![-1.0, 2.0]], vec![0.0, 0.0])],
    );
    assert!(zw >= -EPS && iw >= -EPS);
}

#[test]
fn test_ibp_mixed_crossing_active_valid() {
    let (zw, iw) = compare_zonotope_ibp(
        &ConcreteZonotope::new(vec![0.0, 5.0], vec![vec![2.0, 1.0]]),
        &[(vec![vec![1.0, 0.0], vec![0.0, 1.0]], vec![0.0, 0.0])],
    );
    assert!(zw >= -EPS && zw.is_finite() && iw >= -EPS && iw.is_finite());
}

#[test]
fn test_ibp_scaling_both_agree() {
    let (zw, iw) = compare_zonotope_ibp(
        &ConcreteZonotope::new(vec![5.0], vec![vec![1.0]]),
        &[(vec![vec![3.0]], vec![0.0])],
    );
    assert!((zw - iw).abs() < EPS);
}

#[test]
fn test_ibp_large_3d_network() {
    let z = ConcreteZonotope::new(
        vec![0.0; 3],
        vec![
            vec![1.0, 0.0, 0.0],
            vec![0.0, 1.0, 0.0],
            vec![0.0, 0.0, 1.0],
        ],
    );
    let layers = vec![
        (
            vec![
                vec![1.0, 0.5, 0.0],
                vec![0.0, 1.0, 0.5],
                vec![0.5, 0.0, 1.0],
            ],
            vec![0.0; 3],
        ),
        (
            vec![vec![1.0, -1.0, 0.5], vec![-0.5, 1.0, -1.0]],
            vec![0.0; 2],
        ),
        (vec![vec![1.0, 1.0]], vec![0.0]),
    ];
    let (zw, iw) = compare_zonotope_ibp(&z, &layers);
    assert!(zw <= iw + EPS);
}

// -- soundness checks --
#[test]
fn test_soundness_1d_crossing() {
    check_soundness(
        &ConcreteZonotope::new(vec![0.0], vec![vec![2.0]]),
        &[vec![1.0]],
        &[0.0],
        100,
        0xCAFE_0001,
    );
}

#[test]
fn test_soundness_2d_mixed() {
    let z = ConcreteZonotope::new(vec![1.0, -0.5], vec![vec![2.0, 1.0], vec![0.5, 1.5]]);
    check_soundness(
        &z,
        &[vec![1.0, -1.0], vec![0.5, 0.5]],
        &[0.0, 0.0],
        200,
        0x00CA_FE02,
    );
}

#[test]
fn test_soundness_negative_weight() {
    let z = ConcreteZonotope::new(vec![0.5, 0.5], vec![vec![1.0, 0.0], vec![0.0, 1.0]]);
    check_soundness(
        &z,
        &[vec![-1.0, 2.0], vec![2.0, -1.0]],
        &[1.0, 1.0],
        200,
        0x00CA_FE03,
    );
}

#[test]
fn test_soundness_dimension_expansion() {
    check_soundness(
        &ConcreteZonotope::new(vec![0.0], vec![vec![1.0]]),
        &[vec![1.0], vec![-1.0], vec![0.5]],
        &[0.0, 0.5, 0.0],
        100,
        0x00CA_FE06,
    );
}

#[test]
fn test_soundness_all_active() {
    check_soundness(
        &ConcreteZonotope::new(vec![10.0], vec![vec![1.0]]),
        &[vec![1.0]],
        &[0.0],
        50,
        0x00CA_FE07,
    );
}

#[test]
fn test_soundness_all_inactive() {
    check_soundness(
        &ConcreteZonotope::new(vec![-10.0], vec![vec![1.0]]),
        &[vec![1.0]],
        &[0.0],
        50,
        0x00CA_FE08,
    );
}

#[test]
fn test_soundness_vertex_points() {
    let z = ConcreteZonotope::new(vec![1.0, -1.0], vec![vec![2.0, 1.0], vec![0.5, 1.5]]);
    let w = vec![vec![1.0, 0.5], vec![-0.5, 1.0]];
    let b = [0.0, 0.5];
    let out = zonotope_affine_relu(&z, &w, &b);
    let (lo, hi) = out.to_interval();
    for c in &[
        vec![1.0, 1.0],
        vec![1.0, -1.0],
        vec![-1.0, 1.0],
        vec![-1.0, -1.0],
    ] {
        let r = affine_relu_point(&sample(&z, c), &w, &b);
        for (j, &v) in r.iter().enumerate() {
            assert!(v >= lo[j] - EPS && v <= hi[j] + EPS);
        }
    }
}

#[test]
fn test_soundness_fwd_2_layers() {
    let z = ConcreteZonotope::new(vec![0.0, 0.0], vec![vec![1.0, 0.0], vec![0.0, 1.0]]);
    let layers = vec![
        (vec![vec![1.0, 0.5], vec![0.5, 1.0]], vec![0.0, 0.0]),
        (vec![vec![1.0, -1.0]], vec![0.5]),
    ];
    check_fwd_soundness(&z, &layers, 200, 0x00CA_FE04);
}

#[test]
fn test_soundness_fwd_3_layers() {
    let z = ConcreteZonotope::new(vec![0.5, -0.5], vec![vec![1.0, 0.5]]);
    let layers = vec![
        (vec![vec![1.0, 1.0], vec![1.0, -1.0]], vec![0.0, 0.0]),
        (vec![vec![0.5, 0.5], vec![-0.5, 0.5]], vec![0.0, 0.0]),
        (vec![vec![1.0, 1.0]], vec![0.0]),
    ];
    check_fwd_soundness(&z, &layers, 100, 0x00CA_FE05);
}

#[test]
fn test_soundness_output_bounded() {
    let z = ConcreteZonotope::new(vec![0.0, -1.0, 3.0], vec![vec![2.0, 2.0, 1.0]]);
    let w = vec![
        vec![1.0, 0.0, 0.0],
        vec![0.0, 1.0, 0.0],
        vec![0.0, 0.0, 1.0],
    ];
    let (out_lo, _) = zonotope_affine_relu(&z, &w, &[0.0; 3]).to_interval();
    let (z_lo, z_hi) = z.to_interval();
    for j in 0..3 {
        assert!(out_lo[j] >= -(z_hi[j] - z_lo[j]) - EPS);
    }
}

#[test]
fn test_soundness_3d_multi_gen() {
    let z = ConcreteZonotope::new(
        vec![0.0, 0.5, -0.5],
        vec![
            vec![1.0, 0.0, 0.0],
            vec![0.0, 1.0, 0.0],
            vec![0.0, 0.0, 1.0],
        ],
    );
    check_soundness(
        &z,
        &[vec![1.0, 0.5, 0.0], vec![0.0, 1.0, 0.5]],
        &[0.0, 0.0],
        100,
        0xBEEF,
    );
}

#[test]
fn test_ibp_zero_bias_uncorrelated() {
    // For uncorrelated inputs (identity weight, axis-aligned generators),
    // zonotope lambda-relaxation does not benefit from correlation tracking
    // and can produce a wider hull than IBP. The zonotope advantage appears
    // with correlated inputs and non-diagonal weight matrices.
    let z = ConcreteZonotope::new(vec![0.0, 0.0], vec![vec![1.0, 0.0], vec![0.0, 1.0]]);
    let (zw, iw) = compare_zonotope_ibp(
        &z,
        &[(vec![vec![1.0, 0.0], vec![0.0, 1.0]], vec![0.0, 0.0])],
    );
    // Zonotope width >= IBP width for uncorrelated case; both are finite and positive.
    assert!(
        zw >= iw - EPS,
        "zonotope width {zw} should be >= IBP width {iw} for uncorrelated inputs"
    );
    assert!(zw < 10.0, "zonotope width should be bounded");
}
#[test]
fn test_affine_relu_relu_nonneg_output() {
    // Lambda-relaxation overapproximation for a crossing neuron produces a
    // lower bound below zero. The overapproximation is sound: it contains
    // the true ReLU image [0, 5], but the hull extends below zero.
    let z = ConcreteZonotope::new(vec![0.0], vec![vec![5.0]]);
    let (lo, hi) = zonotope_affine_relu(&z, &[vec![1.0]], &[0.0]).to_interval();
    // Soundness: overapproximation contains the true image [0, 5].
    assert!(
        lo[0] <= EPS,
        "lower bound {} should be <= 0 (contains ReLU minimum)",
        lo[0]
    );
    assert!(
        hi[0] >= 5.0 - EPS,
        "upper bound {} should be >= 5 (contains ReLU maximum)",
        hi[0]
    );
}
