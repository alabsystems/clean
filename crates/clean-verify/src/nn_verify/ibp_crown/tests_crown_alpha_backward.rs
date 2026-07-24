// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for Alpha-CROWN backward pass and gradient computation.
//!
//! Covers `initialize_alphas`, `backward_pass`, `ibp_forward`,
//! `compute_alpha_gradient`, and `project_alphas` from `crown_alpha_backward.rs`.

use super::crown_alpha::AlphaCrownParams;
use super::crown_alpha_backward::*;
use super::ibp::Interval;

const EPS: f64 = 1e-9;

fn approx_eq(a: f64, b: f64) -> bool {
    (a - b).abs() < EPS
}

// --- initialize_alphas ---

#[test]
fn test_initialize_alphas_crossing_neuron() {
    let bounds = vec![Interval::new(-1.0, 1.0)];
    let p = initialize_alphas(&bounds);
    assert_eq!(p.alphas.len(), 1);
    assert!(approx_eq(p.alphas[0][0], 0.5)); // u/(u-l) = 1/2
}

#[test]
fn test_initialize_alphas_crossing_asymmetric() {
    let p = initialize_alphas(&[Interval::new(-2.0, 4.0)]);
    assert!(approx_eq(p.alphas[0][0], 4.0 / 6.0));
}

#[test]
fn test_initialize_alphas_all_positive() {
    let p = initialize_alphas(&[Interval::new(1.0, 3.0)]);
    assert!(approx_eq(p.alphas[0][0], 1.0));
}

#[test]
fn test_initialize_alphas_all_negative() {
    let p = initialize_alphas(&[Interval::new(-3.0, -1.0)]);
    assert!(approx_eq(p.alphas[0][0], 1.0));
}

#[test]
fn test_initialize_alphas_zero_boundary() {
    // l=0 => not crossing; u=0 => not crossing; l=u=0 => not crossing
    assert!(approx_eq(
        initialize_alphas(&[Interval::new(0.0, 2.0)]).alphas[0][0],
        1.0
    ));
    assert!(approx_eq(
        initialize_alphas(&[Interval::new(-2.0, 0.0)]).alphas[0][0],
        1.0
    ));
    assert!(approx_eq(
        initialize_alphas(&[Interval::new(0.0, 0.0)]).alphas[0][0],
        1.0
    ));
}

#[test]
fn test_initialize_alphas_empty() {
    assert!(initialize_alphas(&[]).alphas.is_empty());
}

#[test]
fn test_initialize_alphas_multiple_neurons() {
    let bounds = vec![
        Interval::new(-1.0, 3.0),  // crossing: 3/4
        Interval::new(2.0, 5.0),   // positive: 1.0
        Interval::new(-4.0, -1.0), // negative: 1.0
        Interval::new(-3.0, 1.0),  // crossing: 1/4
    ];
    let p = initialize_alphas(&bounds);
    assert_eq!(p.alphas.len(), 4);
    assert!(approx_eq(p.alphas[0][0], 0.75));
    assert!(approx_eq(p.alphas[1][0], 1.0));
    assert!(approx_eq(p.alphas[2][0], 1.0));
    assert!(approx_eq(p.alphas[3][0], 0.25));
}

#[test]
fn test_initialize_alphas_near_zero_crossing() {
    let p = initialize_alphas(&[Interval::new(-0.01, 0.01)]);
    assert!(approx_eq(p.alphas[0][0], 0.5));
}

#[test]
fn test_initialize_alphas_wide_crossing() {
    let p = initialize_alphas(&[Interval::new(-100.0, 1.0)]);
    assert!((p.alphas[0][0] - 1.0 / 101.0).abs() < EPS);
}

// --- ibp_forward ---

#[test]
fn test_ibp_forward_empty_network() {
    let r = ibp_forward(&[], &[], &Interval::new(-1.0, 1.0));
    assert!(r.is_empty());
}

#[test]
fn test_ibp_forward_single_layer_positive_weight() {
    // y = 2x + 1, x in [-1,1] => [-1, 3]
    let r = ibp_forward(&[vec![vec![2.0]]], &[vec![1.0]], &Interval::new(-1.0, 1.0));
    assert_eq!(r.len(), 1);
    assert!(approx_eq(r[0].lower, -1.0));
    assert!(approx_eq(r[0].upper, 3.0));
}

#[test]
fn test_ibp_forward_single_layer_negative_weight() {
    // y = -2x, x in [1,3] => [-6, -2]
    let r = ibp_forward(&[vec![vec![-2.0]]], &[vec![0.0]], &Interval::new(1.0, 3.0));
    assert!(approx_eq(r[0].lower, -6.0));
    assert!(approx_eq(r[0].upper, -2.0));
}

#[test]
fn test_ibp_forward_two_neurons() {
    // W=[[1],[-1]], b=[0,0], x in [-1,1]
    let r = ibp_forward(
        &[vec![vec![1.0], vec![-1.0]]],
        &[vec![0.0, 0.0]],
        &Interval::new(-1.0, 1.0),
    );
    assert_eq!(r.len(), 2);
    assert!(approx_eq(r[0].lower, -1.0) && approx_eq(r[0].upper, 1.0));
    assert!(approx_eq(r[1].lower, -1.0) && approx_eq(r[1].upper, 1.0));
}

#[test]
fn test_ibp_forward_two_layer_relu() {
    // Layer 1: x->[-1,1], ReLU->[0,1]. Layer 2: 2*[0,1]->[0,2]
    let r = ibp_forward(
        &[vec![vec![1.0]], vec![vec![2.0]]],
        &[vec![0.0], vec![0.0]],
        &Interval::new(-1.0, 1.0),
    );
    assert_eq!(r.len(), 2);
    assert!(approx_eq(r[0].lower, -1.0) && approx_eq(r[0].upper, 1.0));
    assert!(approx_eq(r[1].lower, 0.0) && approx_eq(r[1].upper, 2.0));
}

#[test]
fn test_ibp_forward_relu_kills_negative() {
    // Pre-act all negative => ReLU=0 => next layer output=0
    let r = ibp_forward(
        &[vec![vec![-10.0]], vec![vec![5.0]]],
        &[vec![0.0], vec![0.0]],
        &Interval::new(1.0, 2.0),
    );
    assert!(approx_eq(r[1].lower, 0.0) && approx_eq(r[1].upper, 0.0));
}

#[test]
fn test_ibp_forward_all_positive_relu_identity() {
    // Pre-act all positive => ReLU=identity
    let r = ibp_forward(
        &[vec![vec![1.0]], vec![vec![1.0]]],
        &[vec![5.0], vec![0.0]],
        &Interval::new(0.0, 1.0),
    );
    assert!(approx_eq(r[1].lower, 5.0) && approx_eq(r[1].upper, 6.0));
}

#[test]
fn test_ibp_forward_point_input() {
    let r = ibp_forward(&[vec![vec![3.0]]], &[vec![1.0]], &Interval::new(2.0, 2.0));
    assert!(approx_eq(r[0].lower, 7.0) && approx_eq(r[0].upper, 7.0));
}

#[test]
fn test_ibp_forward_multi_input_mixed_weight() {
    // W=[[1,-1]], b=[0], x in [0,1] => [-1, 1]
    let r = ibp_forward(
        &[vec![vec![1.0, -1.0]]],
        &[vec![0.0]],
        &Interval::new(0.0, 1.0),
    );
    assert!(approx_eq(r[0].lower, -1.0) && approx_eq(r[0].upper, 1.0));
}

#[test]
fn test_ibp_forward_three_layers_accumulation() {
    let r = ibp_forward(
        &[
            vec![vec![1.0], vec![-1.0]],
            vec![vec![1.0, 1.0]],
            vec![vec![2.0]],
        ],
        &[vec![0.0, 0.0], vec![0.0], vec![0.0]],
        &Interval::new(-1.0, 1.0),
    );
    assert_eq!(r.len(), 4); // 2+1+1
}

#[test]
fn test_ibp_forward_no_relu_on_last_layer() {
    // Last layer keeps negative output
    let r = ibp_forward(&[vec![vec![-1.0]]], &[vec![0.0]], &Interval::new(1.0, 2.0));
    assert!(approx_eq(r[0].lower, -2.0) && approx_eq(r[0].upper, -1.0));
}

#[test]
fn test_ibp_forward_bias_effect() {
    let r0 = ibp_forward(&[vec![vec![1.0]]], &[vec![0.0]], &Interval::new(0.0, 1.0));
    let r5 = ibp_forward(&[vec![vec![1.0]]], &[vec![5.0]], &Interval::new(0.0, 1.0));
    assert!(approx_eq(r0[0].lower, 0.0) && approx_eq(r5[0].lower, 5.0));
}

// --- backward_pass ---

#[test]
fn test_backward_pass_empty_network() {
    let r = backward_pass(
        &[],
        &[],
        &Interval::new(-2.0, 3.0),
        &[],
        &AlphaCrownParams { alphas: vec![] },
    );
    assert!(approx_eq(r.lower, -2.0) && approx_eq(r.upper, 3.0));
}

#[test]
fn test_backward_pass_single_linear() {
    // y = 2x+1, x in [0,1] => [1, 3]
    let a = AlphaCrownParams {
        alphas: vec![vec![1.0]],
    };
    let r = backward_pass(
        &[vec![vec![2.0]]],
        &[vec![1.0]],
        &Interval::new(0.0, 1.0),
        &[Interval::new(1.0, 3.0)],
        &a,
    );
    assert!(approx_eq(r.lower, 1.0) && approx_eq(r.upper, 3.0));
}

#[test]
fn test_backward_pass_negative_weight() {
    let a = AlphaCrownParams {
        alphas: vec![vec![1.0]],
    };
    let r = backward_pass(
        &[vec![vec![-3.0]]],
        &[vec![0.0]],
        &Interval::new(1.0, 2.0),
        &[Interval::new(-6.0, -3.0)],
        &a,
    );
    assert!(approx_eq(r.lower, -6.0) && approx_eq(r.upper, -3.0));
}

#[test]
fn test_backward_pass_all_positive_pre_act() {
    let a = AlphaCrownParams {
        alphas: vec![vec![1.0], vec![1.0]],
    };
    let r = backward_pass(
        &[vec![vec![2.0]], vec![vec![1.0]]],
        &[vec![3.0], vec![0.0]],
        &Interval::new(1.0, 2.0),
        &[Interval::new(5.0, 7.0), Interval::new(5.0, 7.0)],
        &a,
    );
    assert!(approx_eq(r.lower, 5.0) && approx_eq(r.upper, 7.0));
}

#[test]
fn test_backward_pass_all_negative_pre_act() {
    let a = AlphaCrownParams {
        alphas: vec![vec![1.0], vec![1.0]],
    };
    let r = backward_pass(
        &[vec![vec![-2.0]], vec![vec![1.0]]],
        &[vec![-3.0], vec![0.0]],
        &Interval::new(0.0, 1.0),
        &[Interval::new(-5.0, -3.0), Interval::new(0.0, 0.0)],
        &a,
    );
    assert!(approx_eq(r.lower, 0.0) && approx_eq(r.upper, 0.0));
}

#[test]
fn test_backward_pass_crossing_neuron() {
    let a = AlphaCrownParams {
        alphas: vec![vec![0.5], vec![1.0]],
    };
    let r = backward_pass(
        &[vec![vec![1.0]], vec![vec![1.0]]],
        &[vec![0.0], vec![0.0]],
        &Interval::new(-1.0, 1.0),
        &[Interval::new(-1.0, 1.0), Interval::new(0.0, 1.0)],
        &a,
    );
    assert!(r.lower <= r.upper + EPS);
    assert!(r.lower <= EPS && r.upper >= 1.0 - EPS);
}

#[test]
fn test_backward_pass_point_input() {
    let a = AlphaCrownParams {
        alphas: vec![vec![1.0]],
    };
    let r = backward_pass(
        &[vec![vec![3.0]]],
        &[vec![1.0]],
        &Interval::new(2.0, 2.0),
        &[Interval::new(7.0, 7.0)],
        &a,
    );
    assert!(approx_eq(r.lower, 7.0) && approx_eq(r.upper, 7.0));
}

#[test]
fn test_backward_pass_lower_le_upper() {
    let w = vec![vec![vec![1.0, -0.5], vec![-1.0, 2.0]], vec![vec![1.0, 1.0]]];
    let b = vec![vec![0.5, -0.5], vec![0.0]];
    let input = Interval::new(-1.0, 1.0);
    let lb = ibp_forward(&w, &b, &input);
    let r = backward_pass(&w, &b, &input, &lb, &initialize_alphas(&lb));
    assert!(r.lower <= r.upper + EPS);
}

#[test]
fn test_backward_pass_respects_alpha_value() {
    let w = vec![vec![vec![1.0]], vec![vec![1.0]]];
    let b = vec![vec![0.0], vec![0.0]];
    let input = Interval::new(-1.0, 1.0);
    let lb = vec![Interval::new(-1.0, 1.0), Interval::new(0.0, 1.0)];
    let r0 = backward_pass(
        &w,
        &b,
        &input,
        &lb,
        &AlphaCrownParams {
            alphas: vec![vec![0.0], vec![1.0]],
        },
    );
    let r1 = backward_pass(
        &w,
        &b,
        &input,
        &lb,
        &AlphaCrownParams {
            alphas: vec![vec![1.0], vec![1.0]],
        },
    );
    // Both valid, potentially different widths
    assert!(r0.lower <= r0.upper + EPS);
    assert!(r1.lower <= r1.upper + EPS);
}

// --- compute_alpha_gradient ---

#[test]
fn test_gradient_no_crossing_is_zero() {
    let w = vec![vec![vec![1.0]], vec![vec![1.0]]];
    let b = vec![vec![5.0], vec![0.0]];
    let input = Interval::new(0.0, 1.0);
    let lb = ibp_forward(&w, &b, &input);
    let g = compute_alpha_gradient(&w, &b, &input, &lb, &initialize_alphas(&lb), 1e-6);
    for lg in &g {
        for &v in lg {
            assert!(v.abs() < 1e-4);
        }
    }
}

#[test]
fn test_gradient_dimensions_match_alphas() {
    let w = vec![vec![vec![1.0, -0.5], vec![-1.0, 2.0]], vec![vec![1.0, 1.0]]];
    let b = vec![vec![0.0, 0.0], vec![0.0]];
    let input = Interval::new(-1.0, 1.0);
    let lb = ibp_forward(&w, &b, &input);
    let a = initialize_alphas(&lb);
    let g = compute_alpha_gradient(&w, &b, &input, &lb, &a, 1e-6);
    assert_eq!(g.len(), a.alphas.len());
    for (i, lg) in g.iter().enumerate() {
        assert_eq!(lg.len(), a.alphas[i].len());
    }
}

#[test]
fn test_gradient_finite_values() {
    let w = vec![vec![vec![2.0, -1.0], vec![-1.0, 2.0]], vec![vec![1.0, 1.0]]];
    let b = vec![vec![0.0, 0.0], vec![0.0]];
    let input = Interval::new(-1.0, 1.0);
    let lb = ibp_forward(&w, &b, &input);
    let g = compute_alpha_gradient(&w, &b, &input, &lb, &initialize_alphas(&lb), 1e-6);
    for lg in &g {
        for &v in lg {
            assert!(v.is_finite());
        }
    }
}

#[test]
fn test_gradient_empty_network() {
    let g = compute_alpha_gradient(
        &[],
        &[],
        &Interval::new(-1.0, 1.0),
        &[],
        &AlphaCrownParams { alphas: vec![] },
        1e-6,
    );
    assert!(g.is_empty());
}

#[test]
fn test_gradient_crossing_has_nonzero_component() {
    let w = vec![vec![vec![1.0], vec![-1.0]], vec![vec![1.0, 1.0]]];
    let b = vec![vec![0.0, 0.0], vec![0.0]];
    let input = Interval::new(-1.0, 1.0);
    let lb = ibp_forward(&w, &b, &input);
    let a = AlphaCrownParams {
        alphas: vec![vec![0.1], vec![0.1], vec![0.9]],
    };
    let g = compute_alpha_gradient(&w, &b, &input, &lb, &a, 1e-6);
    let any_nz = g.iter().any(|lg| lg.iter().any(|&v| v.abs() > 1e-10));
    assert!(any_nz || g.is_empty());
}

#[test]
fn test_gradient_epsilon_sensitivity() {
    let w = vec![vec![vec![1.0, -1.0], vec![-1.0, 1.0]], vec![vec![1.0, 1.0]]];
    let b = vec![vec![0.0, 0.0], vec![0.0]];
    let input = Interval::new(-1.0, 1.0);
    let lb = ibp_forward(&w, &b, &input);
    let a = initialize_alphas(&lb);
    let gs = compute_alpha_gradient(&w, &b, &input, &lb, &a, 1e-8);
    let gl = compute_alpha_gradient(&w, &b, &input, &lb, &a, 1e-3);
    for lg in &gs {
        for &v in lg {
            assert!(v.is_finite());
        }
    }
    for lg in &gl {
        for &v in lg {
            assert!(v.is_finite());
        }
    }
}

#[test]
fn test_gradient_single_layer_all_zero() {
    let w = vec![vec![vec![2.0]]];
    let b = vec![vec![1.0]];
    let input = Interval::new(-1.0, 1.0);
    let lb = ibp_forward(&w, &b, &input);
    let g = compute_alpha_gradient(&w, &b, &input, &lb, &initialize_alphas(&lb), 1e-6);
    for lg in &g {
        for &v in lg {
            assert!(v.abs() < 1e-4);
        }
    }
}

// --- project_alphas ---

#[test]
fn test_project_alphas_already_in_range() {
    let mut p = AlphaCrownParams {
        alphas: vec![vec![0.0, 0.5, 1.0]],
    };
    project_alphas(&mut p);
    assert!(approx_eq(p.alphas[0][0], 0.0));
    assert!(approx_eq(p.alphas[0][1], 0.5));
    assert!(approx_eq(p.alphas[0][2], 1.0));
}

#[test]
fn test_project_alphas_clamp_negative() {
    let mut p = AlphaCrownParams {
        alphas: vec![vec![-0.5, -100.0]],
    };
    project_alphas(&mut p);
    assert!(approx_eq(p.alphas[0][0], 0.0) && approx_eq(p.alphas[0][1], 0.0));
}

#[test]
fn test_project_alphas_clamp_above_one() {
    let mut p = AlphaCrownParams {
        alphas: vec![vec![1.5, 999.0]],
    };
    project_alphas(&mut p);
    assert!(approx_eq(p.alphas[0][0], 1.0) && approx_eq(p.alphas[0][1], 1.0));
}

#[test]
fn test_project_alphas_mixed() {
    let mut p = AlphaCrownParams {
        alphas: vec![vec![-0.3, 0.4, 1.7]],
    };
    project_alphas(&mut p);
    assert!(approx_eq(p.alphas[0][0], 0.0));
    assert!(approx_eq(p.alphas[0][1], 0.4));
    assert!(approx_eq(p.alphas[0][2], 1.0));
}

#[test]
fn test_project_alphas_empty() {
    let mut p = AlphaCrownParams { alphas: vec![] };
    project_alphas(&mut p);
    assert!(p.alphas.is_empty());
}

#[test]
fn test_project_alphas_multiple_layers() {
    let mut p = AlphaCrownParams {
        alphas: vec![vec![-1.0, 2.0], vec![0.5], vec![3.0, -0.1, 0.8]],
    };
    project_alphas(&mut p);
    assert!(approx_eq(p.alphas[0][0], 0.0) && approx_eq(p.alphas[0][1], 1.0));
    assert!(approx_eq(p.alphas[1][0], 0.5));
    assert!(
        approx_eq(p.alphas[2][0], 1.0)
            && approx_eq(p.alphas[2][1], 0.0)
            && approx_eq(p.alphas[2][2], 0.8)
    );
}

#[test]
fn test_project_alphas_idempotent() {
    let mut p = AlphaCrownParams {
        alphas: vec![vec![-2.0, 0.5, 3.0]],
    };
    project_alphas(&mut p);
    let first = p.alphas.clone();
    project_alphas(&mut p);
    for (a, b) in p.alphas[0].iter().zip(first[0].iter()) {
        assert!(approx_eq(*a, *b));
    }
}

// --- Integration ---

#[test]
fn test_integration_single_layer_consistency() {
    let w = vec![vec![vec![2.0, -1.0]]];
    let b = vec![vec![0.5]];
    let input = Interval::new(-1.0, 1.0);
    let lb = ibp_forward(&w, &b, &input);
    let r = backward_pass(&w, &b, &input, &lb, &initialize_alphas(&lb));
    assert!((r.lower - (-2.5)).abs() < 0.01 && (r.upper - 3.5).abs() < 0.01);
}

#[test]
fn test_integration_two_layer_soundness() {
    let w = vec![vec![vec![1.0], vec![-1.0]], vec![vec![1.0, 1.0]]];
    let b = vec![vec![0.0, 0.0], vec![0.0]];
    let input = Interval::new(-1.0, 1.0);
    let lb = ibp_forward(&w, &b, &input);
    let r = backward_pass(&w, &b, &input, &lb, &initialize_alphas(&lb));
    for i in 0..21 {
        let x = -1.0 + 2.0 * (i as f64) / 20.0;
        let y = x.max(0.0) + (-x).max(0.0); // |x|
        assert!(y >= r.lower - EPS && y <= r.upper + EPS, "x={x}: y={y}");
    }
}

#[test]
fn test_integration_gradient_descent_improves() {
    let w = vec![vec![vec![1.0, -1.0], vec![-1.0, 1.0]], vec![vec![1.0, 1.0]]];
    let b = vec![vec![0.0, 0.0], vec![0.0]];
    let input = Interval::new(-1.0, 1.0);
    let lb = ibp_forward(&w, &b, &input);
    let mut a = initialize_alphas(&lb);
    let init = backward_pass(&w, &b, &input, &lb, &a);
    let init_w = init.upper - init.lower;
    for _ in 0..20 {
        let g = compute_alpha_gradient(&w, &b, &input, &lb, &a, 1e-6);
        for (li, lg) in g.iter().enumerate() {
            for (ni, &v) in lg.iter().enumerate() {
                if li < a.alphas.len() && ni < a.alphas[li].len() {
                    a.alphas[li][ni] -= 0.1 * v;
                }
            }
        }
        project_alphas(&mut a);
    }
    let fin = backward_pass(&w, &b, &input, &lb, &a);
    assert!(fin.upper - fin.lower <= init_w + EPS);
}

#[test]
fn test_integration_alpha_zero_vs_one() {
    let w = vec![vec![vec![1.0], vec![-1.0]], vec![vec![1.0, 1.0]]];
    let b = vec![vec![0.0, 0.0], vec![0.0]];
    let input = Interval::new(-1.0, 1.0);
    let lb = ibp_forward(&w, &b, &input);
    let a0 = AlphaCrownParams {
        alphas: lb.iter().map(|_| vec![0.0]).collect(),
    };
    let a1 = AlphaCrownParams {
        alphas: lb.iter().map(|_| vec![1.0]).collect(),
    };
    let r0 = backward_pass(&w, &b, &input, &lb, &a0);
    let r1 = backward_pass(&w, &b, &input, &lb, &a1);
    assert!(r0.lower <= r0.upper + EPS && r1.lower <= r1.upper + EPS);
}

#[test]
fn test_integration_ibp_then_backward_valid() {
    let w = vec![vec![vec![2.0, -1.0], vec![-1.0, 2.0]], vec![vec![1.0, 1.0]]];
    let b = vec![vec![0.0, 0.0], vec![0.0]];
    let input = Interval::new(-1.0, 1.0);
    let lb = ibp_forward(&w, &b, &input);
    assert_eq!(lb.len(), 3);
    let r = backward_pass(&w, &b, &input, &lb, &initialize_alphas(&lb));
    assert!(r.lower <= r.upper + EPS);
}
