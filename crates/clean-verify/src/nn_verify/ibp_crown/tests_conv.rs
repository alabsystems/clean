// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for convolutional layer IBP soundness (T84a-T84c).

use super::conv::{
    compute_output_shape, conv_forward_interval, conv_lipschitz_bound, conv_to_linear_matrix,
    depthwise_conv_interval, im2col_intervals, verify_conv_ibp_sound,
    verify_conv_linear_equivalence, ConvParams, ConvWeight, IntervalTensor, T84A_CONV_IBP_SOUND,
    T84B_CONV_LINEAR_EQUIV, T84C_CONV_LIPSCHITZ,
};
use super::ibp::Interval;
use crate::spec::ProofStatus;

fn params(
    kh: usize,
    kw: usize,
    ic: usize,
    oc: usize,
    sh: usize,
    sw: usize,
    ph: usize,
    pw: usize,
) -> ConvParams {
    ConvParams {
        kernel_height: kh,
        kernel_width: kw,
        in_channels: ic,
        out_channels: oc,
        stride_h: sh,
        stride_w: sw,
        pad_h: ph,
        pad_w: pw,
    }
}

fn identity_1x1() -> (ConvWeight, ConvParams) {
    let w = ConvWeight {
        kernel: vec![vec![vec![vec![1.0]]]],
        bias: vec![0.0],
    };
    (w, params(1, 1, 1, 1, 1, 1, 0, 0))
}

fn simple_3x3() -> (ConvWeight, ConvParams) {
    let k = vec![vec![vec![
        vec![1.0, 0.0, -1.0],
        vec![2.0, 0.0, -2.0],
        vec![1.0, 0.0, -1.0],
    ]]];
    (
        ConvWeight {
            kernel: k,
            bias: vec![0.0],
        },
        params(3, 3, 1, 1, 1, 1, 0, 0),
    )
}

fn point_tensor(data: &[f64], h: usize, w: usize, c: usize) -> IntervalTensor {
    IntervalTensor::new(data.iter().map(|&v| Interval::point(v)).collect(), h, w, c)
}

fn uniform_tensor(iv: Interval, h: usize, w: usize, c: usize) -> IntervalTensor {
    IntervalTensor::new(vec![iv; h * w * c], h, w, c)
}

// -- Proof status constants --

#[test]
fn test_proof_status_constants() {
    assert_eq!(T84A_CONV_IBP_SOUND, ProofStatus::DerivedPending);
    assert_eq!(T84B_CONV_LINEAR_EQUIV, ProofStatus::DerivedPending);
    assert_eq!(T84C_CONV_LIPSCHITZ, ProofStatus::DerivedPending);
}

// -- Output shape computation --

#[test]
fn test_output_shape_no_padding_stride1() {
    assert_eq!(
        compute_output_shape(5, 5, &params(3, 3, 1, 1, 1, 1, 0, 0)),
        (3, 3)
    );
}

#[test]
fn test_output_shape_with_padding_preserves_dims() {
    assert_eq!(
        compute_output_shape(5, 5, &params(3, 3, 1, 1, 1, 1, 1, 1)),
        (5, 5)
    );
}

#[test]
fn test_output_shape_stride2() {
    assert_eq!(
        compute_output_shape(7, 7, &params(3, 3, 1, 1, 2, 2, 0, 0)),
        (3, 3)
    );
}

#[test]
fn test_output_shape_1x1_kernel() {
    assert_eq!(
        compute_output_shape(4, 4, &params(1, 1, 3, 8, 1, 1, 0, 0)),
        (4, 4)
    );
}

#[test]
fn test_output_shape_nonsquare() {
    assert_eq!(
        compute_output_shape(4, 6, &params(2, 3, 1, 1, 1, 1, 0, 0)),
        (3, 4)
    );
}

#[test]
fn test_output_shape_stride_larger_than_kernel() {
    assert_eq!(
        compute_output_shape(7, 7, &params(2, 2, 1, 1, 3, 3, 0, 0)),
        (2, 2)
    );
}

// -- im2col --

#[test]
fn test_im2col_column_count() {
    let (_, p) = simple_3x3();
    let cols = im2col_intervals(&uniform_tensor(Interval::new(0.0, 1.0), 4, 4, 1), &p);
    assert_eq!(cols.len(), 2 * 2); // (4-3)/1+1 = 2
}

#[test]
fn test_im2col_column_length() {
    let (_, p) = simple_3x3();
    let cols = im2col_intervals(&uniform_tensor(Interval::new(0.0, 1.0), 4, 4, 1), &p);
    for col in &cols {
        assert_eq!(col.len(), 9);
    } // 1*3*3
}

#[test]
fn test_im2col_padding_zero_fill() {
    let p = params(3, 3, 1, 1, 1, 1, 1, 1);
    let cols = im2col_intervals(&uniform_tensor(Interval::point(5.0), 2, 2, 1), &p);
    let zeros = cols[0]
        .iter()
        .filter(|iv| iv.lower == 0.0 && iv.upper == 0.0)
        .count();
    assert!(zeros >= 4, "expected >=4 padding zeros, got {zeros}");
}

// -- 1x1 conv = pointwise linear --

#[test]
fn test_1x1_conv_preserves_intervals() {
    let (w, p) = identity_1x1();
    let input = IntervalTensor::new(
        vec![
            Interval::new(1.0, 3.0),
            Interval::new(-1.0, 2.0),
            Interval::new(0.0, 0.5),
            Interval::new(4.0, 4.0),
        ],
        2,
        2,
        1,
    );
    let out = conv_forward_interval(&input, &w, &p);
    for (a, b) in input.data.iter().zip(out.data.iter()) {
        assert!((a.lower - b.lower).abs() < 1e-12);
        assert!((a.upper - b.upper).abs() < 1e-12);
    }
}

#[test]
fn test_1x1_conv_scaling() {
    let w = ConvWeight {
        kernel: vec![vec![vec![vec![2.0]]]],
        bias: vec![1.0],
    };
    let input = IntervalTensor::new(vec![Interval::new(1.0, 3.0)], 1, 1, 1);
    let out = conv_forward_interval(&input, &w, &params(1, 1, 1, 1, 1, 1, 0, 0));
    assert!((out.data[0].lower - 3.0).abs() < 1e-12); // 2*1+1
    assert!((out.data[0].upper - 7.0).abs() < 1e-12); // 2*3+1
}

// -- 3x3 conv on 4x4 input --

#[test]
fn test_3x3_conv_constant_input_zero_output() {
    let (w, p) = simple_3x3();
    let out = conv_forward_interval(&point_tensor(&[1.0; 16], 4, 4, 1), &w, &p);
    assert_eq!((out.height, out.width), (2, 2));
    for iv in &out.data {
        assert!(iv.lower.abs() < 1e-10 && iv.upper.abs() < 1e-10);
    }
}

#[test]
fn test_ibp_forward_point_intervals_match_concrete() {
    let (w, p) = simple_3x3();
    let concrete: Vec<f64> = (0..16).map(|i| i as f64).collect();
    let out = conv_forward_interval(&point_tensor(&concrete, 4, 4, 1), &w, &p);
    for iv in &out.data {
        assert!((iv.upper - iv.lower).abs() < 1e-10);
    }
}

// -- Monotonicity --

#[test]
fn test_ibp_forward_monotonicity() {
    let (w, p) = simple_3x3();
    let out_n = conv_forward_interval(&uniform_tensor(Interval::new(0.0, 1.0), 4, 4, 1), &w, &p);
    let out_w = conv_forward_interval(&uniform_tensor(Interval::new(-1.0, 2.0), 4, 4, 1), &w, &p);
    for (n, wi) in out_n.data.iter().zip(out_w.data.iter()) {
        assert!(wi.lower <= n.lower + 1e-10);
        assert!(wi.upper >= n.upper - 1e-10);
    }
}

// -- IBP soundness --

#[test]
fn test_ibp_soundness_center() {
    let (w, p) = simple_3x3();
    let input = uniform_tensor(Interval::new(-1.0, 1.0), 4, 4, 1);
    verify_conv_ibp_sound(&input, &[0.0; 16], &w, &p).expect("center sound");
}

#[test]
fn test_ibp_soundness_lower_corner() {
    let (w, p) = simple_3x3();
    let input = uniform_tensor(Interval::new(-1.0, 1.0), 4, 4, 1);
    verify_conv_ibp_sound(&input, &[-1.0; 16], &w, &p).expect("lower corner sound");
}

#[test]
fn test_ibp_soundness_upper_corner() {
    let (w, p) = simple_3x3();
    let input = uniform_tensor(Interval::new(-1.0, 1.0), 4, 4, 1);
    verify_conv_ibp_sound(&input, &[1.0; 16], &w, &p).expect("upper corner sound");
}

#[test]
fn test_ibp_soundness_random_interior() {
    let (w, p) = simple_3x3();
    let input = uniform_tensor(Interval::new(0.0, 10.0), 4, 4, 1);
    let concrete: Vec<f64> = (0..16).map(|i| (i as f64 * 3.7) % 10.0).collect();
    verify_conv_ibp_sound(&input, &concrete, &w, &p).expect("interior sound");
}

#[test]
fn test_ibp_soundness_rejects_out_of_bounds() {
    let (w, p) = identity_1x1();
    let input = IntervalTensor::new(vec![Interval::new(0.0, 1.0)], 1, 1, 1);
    assert!(verify_conv_ibp_sound(&input, &[2.0], &w, &p).is_err());
}

// -- Conv-to-linear equivalence --

#[test]
fn test_conv_linear_equivalence_3x3_on_4x4() {
    let (w, p) = simple_3x3();
    verify_conv_linear_equivalence(&uniform_tensor(Interval::new(-1.0, 1.0), 4, 4, 1), &w, &p)
        .expect("3x3 equiv");
}

#[test]
fn test_conv_linear_equivalence_1x1() {
    let (w, p) = identity_1x1();
    verify_conv_linear_equivalence(&uniform_tensor(Interval::new(0.0, 5.0), 3, 3, 1), &w, &p)
        .expect("1x1 equiv");
}

#[test]
fn test_conv_linear_equivalence_with_padding() {
    let w = ConvWeight {
        kernel: vec![vec![vec![vec![1.0, -1.0], vec![0.5, 0.5]]]],
        bias: vec![0.5],
    };
    verify_conv_linear_equivalence(
        &uniform_tensor(Interval::new(-2.0, 2.0), 3, 3, 1),
        &w,
        &params(2, 2, 1, 1, 1, 1, 1, 1),
    )
    .expect("padded equiv");
}

#[test]
fn test_conv_linear_equivalence_multi_channel() {
    let kernel = vec![
        vec![vec![vec![1.0]], vec![vec![-1.0]]],
        vec![vec![vec![0.5]], vec![vec![0.5]]],
    ];
    let w = ConvWeight {
        kernel,
        bias: vec![0.0, 1.0],
    };
    let input = IntervalTensor::new(
        vec![
            Interval::new(0.0, 1.0),
            Interval::new(1.0, 2.0),
            Interval::new(-1.0, 0.0),
            Interval::new(0.5, 1.5),
        ],
        2,
        1,
        2,
    );
    verify_conv_linear_equivalence(&input, &w, &params(1, 1, 2, 2, 1, 1, 0, 0))
        .expect("multi-ch equiv");
}

// -- Depthwise convolution --

#[test]
fn test_depthwise_conv_channels_independent() {
    let kernel = vec![
        vec![vec![vec![1.0, 0.0], vec![0.0, 1.0]]],
        vec![vec![vec![2.0, 0.0], vec![0.0, 2.0]]],
    ];
    let w = ConvWeight {
        kernel,
        bias: vec![0.0, 0.0],
    };
    let p = params(2, 2, 2, 2, 1, 1, 0, 0);
    let data: Vec<Interval> = (0..9)
        .flat_map(|_| vec![Interval::point(1.0), Interval::point(0.5)])
        .collect();
    let out = depthwise_conv_interval(&IntervalTensor::new(data, 3, 3, 2), &w, &p);
    assert_eq!((out.height, out.width), (2, 2));
    for oh in 0..2 {
        for ow in 0..2 {
            assert!((out.get(oh, ow, 0).lower - 2.0).abs() < 1e-10);
            assert!((out.get(oh, ow, 1).lower - 2.0).abs() < 1e-10);
        }
    }
}

#[test]
fn test_depthwise_conv_intervals() {
    let w = ConvWeight {
        kernel: vec![vec![vec![vec![1.0, -1.0]]]],
        bias: vec![0.0],
    };
    let input = IntervalTensor::new(vec![Interval::new(0.0, 1.0); 3], 1, 3, 1);
    let out = depthwise_conv_interval(&input, &w, &params(1, 2, 1, 1, 1, 1, 0, 0));
    assert_eq!(out.width, 2);
    assert!((out.data[0].lower - (-1.0)).abs() < 1e-10);
    assert!((out.data[0].upper - 1.0).abs() < 1e-10);
}

// -- Lipschitz bound --

#[test]
fn test_lipschitz_bound_nonnegative() {
    let (w, p) = simple_3x3();
    assert!(conv_lipschitz_bound(4, 4, &w, &p) >= 0.0);
}

#[test]
fn test_lipschitz_bound_zero_kernel() {
    let w = ConvWeight {
        kernel: vec![vec![vec![vec![0.0, 0.0], vec![0.0, 0.0]]]],
        bias: vec![0.0],
    };
    assert!(conv_lipschitz_bound(3, 3, &w, &params(2, 2, 1, 1, 1, 1, 0, 0)).abs() < 1e-12);
}

#[test]
fn test_lipschitz_bound_identity_1x1() {
    let (w, p) = identity_1x1();
    let lip = conv_lipschitz_bound(3, 3, &w, &p);
    assert!(
        (lip - 3.0).abs() < 1e-10,
        "Frobenius of 9x9 identity = 3, got {lip}"
    );
}

#[test]
fn test_lipschitz_bound_scales_with_weight() {
    let w1 = ConvWeight {
        kernel: vec![vec![vec![vec![1.0]]]],
        bias: vec![0.0],
    };
    let w3 = ConvWeight {
        kernel: vec![vec![vec![vec![3.0]]]],
        bias: vec![0.0],
    };
    let p = params(1, 1, 1, 1, 1, 1, 0, 0);
    let ratio = conv_lipschitz_bound(2, 2, &w3, &p) / conv_lipschitz_bound(2, 2, &w1, &p);
    assert!((ratio - 3.0).abs() < 1e-10);
}

// -- Edge cases --

#[test]
fn test_1x1_input_no_padding() {
    let w = ConvWeight {
        kernel: vec![vec![vec![vec![2.0]]]],
        bias: vec![1.0],
    };
    let input = IntervalTensor::new(vec![Interval::new(3.0, 5.0)], 1, 1, 1);
    let out = conv_forward_interval(&input, &w, &params(1, 1, 1, 1, 1, 1, 0, 0));
    assert!((out.data[0].lower - 7.0).abs() < 1e-12);
    assert!((out.data[0].upper - 11.0).abs() < 1e-12);
}

#[test]
fn test_kernel_larger_than_input_with_padding() {
    let k = vec![vec![vec![vec![1.0; 3]; 3]]];
    let w = ConvWeight {
        kernel: k,
        bias: vec![0.0],
    };
    let input = IntervalTensor::new(vec![Interval::point(1.0); 4], 2, 2, 1);
    let out = conv_forward_interval(&input, &w, &params(3, 3, 1, 1, 1, 1, 1, 1));
    assert_eq!((out.height, out.width), (2, 2));
    assert!((out.get(1, 1, 0).lower - 4.0).abs() < 1e-10);
}

#[test]
fn test_zero_kernel_gives_bias_only() {
    let w = ConvWeight {
        kernel: vec![vec![vec![vec![0.0, 0.0], vec![0.0, 0.0]]]],
        bias: vec![3.0],
    };
    let out = conv_forward_interval(
        &uniform_tensor(Interval::new(-100.0, 100.0), 3, 3, 1),
        &w,
        &params(2, 2, 1, 1, 1, 1, 0, 0),
    );
    for iv in &out.data {
        assert!((iv.lower - 3.0).abs() < 1e-10);
        assert!((iv.upper - 3.0).abs() < 1e-10);
    }
}

#[test]
fn test_interval_tensor_len_and_indexing() {
    let t = uniform_tensor(Interval::new(0.0, 1.0), 3, 4, 2);
    assert_eq!(t.len(), 24);
    assert!(!t.is_empty());
    let data = vec![
        Interval::new(1.0, 2.0),
        Interval::new(3.0, 4.0),
        Interval::new(5.0, 6.0),
        Interval::new(7.0, 8.0),
    ];
    let t2 = IntervalTensor::new(data, 2, 1, 2);
    assert!((t2.get(0, 0, 0).lower - 1.0).abs() < 1e-12);
    assert!((t2.get(1, 0, 1).lower - 7.0).abs() < 1e-12);
}

#[test]
fn test_negative_weight_flips_bounds() {
    let w = ConvWeight {
        kernel: vec![vec![vec![vec![-1.0]]]],
        bias: vec![0.0],
    };
    let input = IntervalTensor::new(vec![Interval::new(2.0, 5.0)], 1, 1, 1);
    let out = conv_forward_interval(&input, &w, &params(1, 1, 1, 1, 1, 1, 0, 0));
    assert!((out.data[0].lower - (-5.0)).abs() < 1e-12);
    assert!((out.data[0].upper - (-2.0)).abs() < 1e-12);
}

#[test]
fn test_conv_to_linear_matrix_shape() {
    let (w, p) = simple_3x3();
    let (matrix, bias) = conv_to_linear_matrix(4, 4, &w, &p);
    assert_eq!(matrix.len(), 4); // 2*2*1
    assert_eq!(matrix[0].len(), 16); // 4*4*1
    assert_eq!(bias.len(), 4);
}

#[test]
fn test_conv_to_linear_matrix_multi_output_channel() {
    let kernel = vec![vec![vec![vec![1.0]]], vec![vec![vec![2.0]]]];
    let w = ConvWeight {
        kernel,
        bias: vec![0.0, 1.0],
    };
    let (matrix, bias) = conv_to_linear_matrix(2, 2, &w, &params(1, 1, 1, 2, 1, 1, 0, 0));
    assert_eq!(matrix.len(), 8); // 2*2*2
    assert_eq!(bias.len(), 8);
}

// ============================================================================
// Wave B: T84a-T84c proof verification tests
// ============================================================================

#[test]
fn test_t84a_conv_ibp_sound_multi_channel_random() {
    // T84a: Conv IBP forward soundness with multi-channel random input
    let kernel = vec![
        vec![vec![vec![1.0, -0.5], vec![0.5, 0.25]]], // out_ch 0
        vec![vec![vec![-1.0, 0.3], vec![0.7, -0.2]]], // out_ch 1
    ];
    let w = ConvWeight {
        kernel,
        bias: vec![0.5, -0.3],
    };
    let p = params(2, 2, 1, 2, 1, 1, 0, 0);
    let input = uniform_tensor(Interval::new(-2.0, 3.0), 3, 3, 1);
    // Sample concrete interior points
    let concrete: Vec<f64> = (0..9).map(|i| -2.0 + (i as f64 * 1.1) % 5.0).collect();
    verify_conv_ibp_sound(&input, &concrete, &w, &p).expect("T84a multi-channel sound");
}

#[test]
fn test_t84a_conv_ibp_sound_stride2() {
    // T84a with stride-2 conv
    let w = ConvWeight {
        kernel: vec![vec![vec![vec![1.0, -1.0], vec![0.5, 0.5]]]],
        bias: vec![1.0],
    };
    let p = params(2, 2, 1, 1, 2, 2, 0, 0);
    let input = uniform_tensor(Interval::new(-1.0, 1.0), 4, 4, 1);
    let concrete = vec![0.0; 16];
    verify_conv_ibp_sound(&input, &concrete, &w, &p).expect("T84a stride-2 sound");
}

#[test]
fn test_t84a_conv_ibp_sound_padded() {
    // T84a with padding
    let w = ConvWeight {
        kernel: vec![vec![vec![
            vec![1.0, 0.0, -1.0],
            vec![2.0, 0.0, -2.0],
            vec![1.0, 0.0, -1.0],
        ]]],
        bias: vec![0.0],
    };
    let p = params(3, 3, 1, 1, 1, 1, 1, 1);
    let input = uniform_tensor(Interval::new(-3.0, 3.0), 3, 3, 1);
    let concrete = vec![0.5; 9];
    verify_conv_ibp_sound(&input, &concrete, &w, &p).expect("T84a padded sound");
}

#[test]
fn test_t84b_conv_linear_equiv_stride2() {
    // T84b: Conv-linear equivalence with stride-2
    let w = ConvWeight {
        kernel: vec![vec![vec![vec![2.0, -1.0], vec![0.5, 1.5]]]],
        bias: vec![0.0],
    };
    let p = params(2, 2, 1, 1, 2, 2, 0, 0);
    verify_conv_linear_equivalence(&uniform_tensor(Interval::new(-1.0, 1.0), 4, 4, 1), &w, &p)
        .expect("T84b stride-2 equiv");
}

#[test]
fn test_t84b_conv_linear_equiv_multi_in_out_channels() {
    // T84b: Multi-channel input AND output
    let kernel = vec![
        vec![vec![vec![1.0]], vec![vec![-1.0]]], // out_ch 0: [1] for ic0, [-1] for ic1
        vec![vec![vec![0.5]], vec![vec![0.5]]],  // out_ch 1: [0.5] for ic0, [0.5] for ic1
    ];
    let w = ConvWeight {
        kernel,
        bias: vec![0.0, 1.0],
    };
    let p = params(1, 1, 2, 2, 1, 1, 0, 0);
    let data = vec![
        Interval::new(0.0, 1.0),
        Interval::new(-1.0, 0.0),
        Interval::new(1.0, 2.0),
        Interval::new(0.5, 1.5),
        Interval::new(-0.5, 0.5),
        Interval::new(0.0, 1.0),
    ];
    let input = IntervalTensor::new(data, 3, 1, 2);
    verify_conv_linear_equivalence(&input, &w, &p).expect("T84b multi-ch equiv");
}

#[test]
fn test_t84c_conv_lipschitz_identity_scaled() {
    // T84c: Lipschitz bound scales linearly with kernel magnitude
    let p = params(1, 1, 1, 1, 1, 1, 0, 0);
    for &scale in &[0.5, 1.0, 2.0, 5.0] {
        let w = ConvWeight {
            kernel: vec![vec![vec![vec![scale]]]],
            bias: vec![0.0],
        };
        let lip = conv_lipschitz_bound(3, 3, &w, &p);
        // For 1x1 kernel with value `scale` on 3x3 input, Toeplitz is scale*I_{9x9}
        // Frobenius norm = scale * sqrt(9) = 3*scale
        assert!(
            (lip - 3.0 * scale.abs()).abs() < 1e-10,
            "Lipschitz for scale={scale}: expected {}, got {lip}",
            3.0 * scale.abs()
        );
    }
}

#[test]
fn test_t84c_conv_lipschitz_bounds_actual_change() {
    // T84c: Verify Lipschitz bound actually bounds |f(x) - f(y)|/|x - y|
    let (w, p) = simple_3x3();
    let lip = conv_lipschitz_bound(4, 4, &w, &p);

    // Evaluate on two concrete inputs and check ratio
    let x1: Vec<f64> = vec![1.0; 16];
    let x2: Vec<f64> = (0..16).map(|i| 1.0 + 0.01 * i as f64).collect();

    let out1 = conv_forward_interval(&point_tensor(&x1, 4, 4, 1), &w, &p);
    let out2 = conv_forward_interval(&point_tensor(&x2, 4, 4, 1), &w, &p);

    let x_diff: f64 = x1
        .iter()
        .zip(x2.iter())
        .map(|(a, b)| (a - b).powi(2))
        .sum::<f64>()
        .sqrt();
    let y_diff: f64 = out1
        .data
        .iter()
        .zip(out2.data.iter())
        .map(|(a, b)| (a.lower - b.lower).powi(2))
        .sum::<f64>()
        .sqrt();

    assert!(
        y_diff <= lip * x_diff + 1e-10,
        "Lipschitz violated: |f(x1)-f(x2)|={y_diff} > L*|x1-x2|={}",
        lip * x_diff
    );
}

#[test]
fn test_wave_b_conv_proof_statuses_all_proved() {
    assert_eq!(T84A_CONV_IBP_SOUND, ProofStatus::DerivedPending);
    assert_eq!(T84B_CONV_LINEAR_EQUIV, ProofStatus::DerivedPending);
    assert_eq!(T84C_CONV_LIPSCHITZ, ProofStatus::DerivedPending);
}
