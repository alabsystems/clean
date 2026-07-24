// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for interval matrix arithmetic (mat.rs).

use super::*;

const EPS: f64 = 1e-9;
fn approx_eq(a: f64, b: f64) -> bool {
    (a - b).abs() < EPS
}

// -- Constructors --

#[test]
fn test_new_valid() {
    let m = IntervalMatrix::new(2, 2, vec![1.0, 2.0, 3.0, 4.0], vec![2.0, 3.0, 4.0, 5.0]);
    assert!(m.is_ok());
    let m = m.unwrap();
    assert_eq!(m.rows(), 2);
    assert_eq!(m.cols(), 2);
}

#[test]
fn test_new_invalid_interval() {
    let m = IntervalMatrix::new(1, 1, vec![5.0], vec![3.0]);
    assert!(matches!(
        m.unwrap_err(),
        IntervalMatrixError::InvalidInterval { row: 0, col: 0, .. }
    ));
}

#[test]
fn test_new_data_length_mismatch() {
    assert!(matches!(
        IntervalMatrix::new(2, 2, vec![1.0, 2.0], vec![3.0, 4.0]).unwrap_err(),
        IntervalMatrixError::DataLengthMismatch { .. }
    ));
}

#[test]
fn test_zeros() {
    let m = IntervalMatrix::zeros(3, 4);
    assert_eq!(m.rows(), 3);
    assert_eq!(m.cols(), 4);
    for i in 0..3 {
        for j in 0..4 {
            assert_eq!(m.lo(i, j), 0.0);
            assert_eq!(m.hi(i, j), 0.0);
        }
    }
}

#[test]
fn test_zeros_empty() {
    let m = IntervalMatrix::zeros(0, 0);
    assert_eq!(m.rows(), 0);
    assert_eq!(m.cols(), 0);
}

#[test]
fn test_identity_1x1() {
    let m = IntervalMatrix::identity(1);
    assert_eq!(m.lo(0, 0), 1.0);
    assert_eq!(m.hi(0, 0), 1.0);
}

#[test]
fn test_identity_3x3() {
    let m = IntervalMatrix::identity(3);
    for i in 0..3 {
        for j in 0..3 {
            let expected = if i == j { 1.0 } else { 0.0 };
            assert_eq!(m.lo(i, j), expected);
            assert_eq!(m.hi(i, j), expected);
        }
    }
}

#[test]
fn test_identity_0x0() {
    let m = IntervalMatrix::identity(0);
    assert_eq!(m.rows(), 0);
}

// -- Accessors and transpose --

#[test]
fn test_accessors() {
    let m = IntervalMatrix::new(1, 2, vec![1.0, 3.0], vec![2.0, 4.0]).unwrap();
    assert_eq!(m.lo(0, 0), 1.0);
    assert_eq!(m.hi(0, 0), 2.0);
    assert_eq!(m.lo(0, 1), 3.0);
    assert_eq!(m.hi(0, 1), 4.0);
}

#[test]
fn test_transpose_square() {
    let m = IntervalMatrix::new(2, 2, vec![1.0, 2.0, 3.0, 4.0], vec![5.0, 6.0, 7.0, 8.0]).unwrap();
    let t = m.transpose();
    assert_eq!(t.rows(), 2);
    assert_eq!(t.lo(0, 1), 3.0);
    assert_eq!(t.lo(1, 0), 2.0);
}

#[test]
fn test_transpose_rectangular() {
    let m = IntervalMatrix::new(
        2,
        3,
        vec![1.0, 2.0, 3.0, 4.0, 5.0, 6.0],
        vec![1.0, 2.0, 3.0, 4.0, 5.0, 6.0],
    )
    .unwrap();
    let t = m.transpose();
    assert_eq!(t.rows(), 3);
    assert_eq!(t.cols(), 2);
    assert_eq!(t.lo(2, 1), 6.0);
}

#[test]
fn test_transpose_involutive() {
    let m = IntervalMatrix::new(
        2,
        3,
        vec![1.0, 2.0, 3.0, 4.0, 5.0, 6.0],
        vec![2.0, 3.0, 4.0, 5.0, 6.0, 7.0],
    )
    .unwrap();
    assert_eq!(m.transpose().transpose(), m);
}

// -- verify_containment --

#[test]
fn test_containment_point_matrix() {
    let m = IntervalMatrix::new(2, 2, vec![1.0, 2.0, 3.0, 4.0], vec![1.0, 2.0, 3.0, 4.0]).unwrap();
    assert!(m.verify_containment(&[1.0, 2.0, 3.0, 4.0]).is_ok());
}

#[test]
fn test_containment_inside() {
    let m = IntervalMatrix::new(1, 2, vec![0.0, 0.0], vec![10.0, 10.0]).unwrap();
    assert!(m.verify_containment(&[5.0, 5.0]).is_ok());
}

#[test]
fn test_containment_outside() {
    let m = IntervalMatrix::new(1, 1, vec![0.0], vec![1.0]).unwrap();
    assert!(m.verify_containment(&[2.0]).is_err());
}

#[test]
fn test_containment_wrong_size() {
    assert!(IntervalMatrix::zeros(2, 2)
        .verify_containment(&[0.0; 3])
        .is_err());
}

// -- interval_matrix_add --

#[test]
fn test_add_basic() {
    let a = IntervalMatrix::new(1, 2, vec![1.0, 2.0], vec![3.0, 4.0]).unwrap();
    let b = IntervalMatrix::new(1, 2, vec![10.0, 20.0], vec![30.0, 40.0]).unwrap();
    let c = interval_matrix_add(&a, &b).unwrap();
    assert!(approx_eq(c.lo(0, 0), 11.0));
    assert!(approx_eq(c.hi(0, 1), 44.0));
}

#[test]
fn test_add_dimension_mismatch() {
    assert!(
        interval_matrix_add(&IntervalMatrix::zeros(2, 3), &IntervalMatrix::zeros(3, 2)).is_err()
    );
}

#[test]
fn test_add_identity_is_zeros() {
    let a = IntervalMatrix::new(2, 2, vec![1.0, 2.0, 3.0, 4.0], vec![5.0, 6.0, 7.0, 8.0]).unwrap();
    assert_eq!(
        interval_matrix_add(&a, &IntervalMatrix::zeros(2, 2)).unwrap(),
        a
    );
}

// -- hadamard_product --

#[test]
fn test_hadamard_positive() {
    let a = IntervalMatrix::new(1, 2, vec![2.0, 3.0], vec![4.0, 5.0]).unwrap();
    let b = IntervalMatrix::new(1, 2, vec![1.0, 2.0], vec![3.0, 4.0]).unwrap();
    let c = hadamard_product(&a, &b).unwrap();
    assert!(approx_eq(c.lo(0, 0), 2.0));
    assert!(approx_eq(c.hi(0, 0), 12.0));
}

#[test]
fn test_hadamard_mixed_signs() {
    let a = IntervalMatrix::new(1, 1, vec![-2.0], vec![3.0]).unwrap();
    let b = IntervalMatrix::new(1, 1, vec![-1.0], vec![4.0]).unwrap();
    let c = hadamard_product(&a, &b).unwrap();
    assert!(approx_eq(c.lo(0, 0), -8.0));
    assert!(approx_eq(c.hi(0, 0), 12.0));
}

#[test]
fn test_hadamard_dimension_mismatch() {
    assert!(hadamard_product(&IntervalMatrix::zeros(1, 2), &IntervalMatrix::zeros(2, 1)).is_err());
}

#[test]
fn test_hadamard_with_zeros() {
    let a = IntervalMatrix::new(1, 2, vec![1.0, 2.0], vec![3.0, 4.0]).unwrap();
    let c = hadamard_product(&a, &IntervalMatrix::zeros(1, 2)).unwrap();
    assert!(approx_eq(c.lo(0, 0), 0.0));
    assert!(approx_eq(c.hi(0, 0), 0.0));
}

// -- interval_matrix_multiply --

#[test]
fn test_multiply_point_matrices() {
    let a = IntervalMatrix::new(2, 2, vec![1.0, 2.0, 3.0, 4.0], vec![1.0, 2.0, 3.0, 4.0]).unwrap();
    let b = IntervalMatrix::new(2, 2, vec![5.0, 6.0, 7.0, 8.0], vec![5.0, 6.0, 7.0, 8.0]).unwrap();
    let c = interval_matrix_multiply(&a, &b).unwrap();
    assert!(approx_eq(c.lo(0, 0), 19.0));
    assert!(approx_eq(c.lo(1, 1), 50.0));
}

#[test]
fn test_multiply_identity_left() {
    let a = IntervalMatrix::new(2, 2, vec![1.0, 2.0, 3.0, 4.0], vec![5.0, 6.0, 7.0, 8.0]).unwrap();
    assert_eq!(
        interval_matrix_multiply(&IntervalMatrix::identity(2), &a).unwrap(),
        a
    );
}

#[test]
fn test_multiply_identity_right() {
    let a = IntervalMatrix::new(2, 2, vec![1.0, 2.0, 3.0, 4.0], vec![5.0, 6.0, 7.0, 8.0]).unwrap();
    assert_eq!(
        interval_matrix_multiply(&a, &IntervalMatrix::identity(2)).unwrap(),
        a
    );
}

#[test]
fn test_multiply_rectangular() {
    let a = IntervalMatrix::new(
        2,
        3,
        vec![1.0, 0.0, 0.0, 0.0, 1.0, 0.0],
        vec![1.0, 0.0, 0.0, 0.0, 1.0, 0.0],
    )
    .unwrap();
    let b = IntervalMatrix::new(3, 1, vec![7.0, 8.0, 9.0], vec![7.0, 8.0, 9.0]).unwrap();
    let c = interval_matrix_multiply(&a, &b).unwrap();
    assert_eq!(c.rows(), 2);
    assert_eq!(c.cols(), 1);
    assert!(approx_eq(c.lo(0, 0), 7.0));
    assert!(approx_eq(c.lo(1, 0), 8.0));
}

#[test]
fn test_multiply_inner_dim_mismatch() {
    assert!(
        interval_matrix_multiply(&IntervalMatrix::zeros(2, 3), &IntervalMatrix::zeros(4, 2))
            .is_err()
    );
}

#[test]
fn test_multiply_interval_widening() {
    let a = IntervalMatrix::new(1, 1, vec![1.0], vec![2.0]).unwrap();
    let b = IntervalMatrix::new(1, 1, vec![3.0], vec![4.0]).unwrap();
    let c = interval_matrix_multiply(&a, &b).unwrap();
    assert!(approx_eq(c.lo(0, 0), 3.0));
    assert!(approx_eq(c.hi(0, 0), 8.0));
}

#[test]
fn test_multiply_1x1() {
    let a = IntervalMatrix::new(1, 1, vec![2.0], vec![3.0]).unwrap();
    let b = IntervalMatrix::new(1, 1, vec![4.0], vec![5.0]).unwrap();
    let c = interval_matrix_multiply(&a, &b).unwrap();
    assert!(approx_eq(c.lo(0, 0), 8.0));
    assert!(approx_eq(c.hi(0, 0), 15.0));
}

#[test]
fn test_negative_intervals_multiply() {
    let a = IntervalMatrix::new(1, 1, vec![-5.0], vec![-2.0]).unwrap();
    let b = IntervalMatrix::new(1, 1, vec![-3.0], vec![-1.0]).unwrap();
    let c = interval_matrix_multiply(&a, &b).unwrap();
    assert!(approx_eq(c.lo(0, 0), 2.0));
    assert!(approx_eq(c.hi(0, 0), 15.0));
}

// -- interval_matrix_vector_multiply --

#[test]
fn test_matvec_point() {
    let m = IntervalMatrix::new(2, 2, vec![1.0, 2.0, 3.0, 4.0], vec![1.0, 2.0, 3.0, 4.0]).unwrap();
    let (lo, hi) = interval_matrix_vector_multiply(&m, &[5.0, 6.0], &[5.0, 6.0]).unwrap();
    assert!(approx_eq(lo[0], 17.0));
    assert!(approx_eq(hi[0], 17.0));
    assert!(approx_eq(lo[1], 39.0));
}

#[test]
fn test_matvec_interval() {
    let m = IntervalMatrix::new(1, 2, vec![1.0, 1.0], vec![1.0, 1.0]).unwrap();
    let (lo, hi) = interval_matrix_vector_multiply(&m, &[0.0, 0.0], &[1.0, 1.0]).unwrap();
    assert!(approx_eq(lo[0], 0.0));
    assert!(approx_eq(hi[0], 2.0));
}

#[test]
fn test_matvec_dimension_mismatch() {
    assert!(interval_matrix_vector_multiply(
        &IntervalMatrix::zeros(2, 3),
        &[1.0, 2.0],
        &[1.0, 2.0]
    )
    .is_err());
}

// -- verify_multiplication_sound --

#[test]
fn test_verify_multiply_sound_point() {
    let m1 = IntervalMatrix::new(2, 2, vec![1.0, 2.0, 3.0, 4.0], vec![1.0, 2.0, 3.0, 4.0]).unwrap();
    let m2 = IntervalMatrix::new(2, 2, vec![5.0, 6.0, 7.0, 8.0], vec![5.0, 6.0, 7.0, 8.0]).unwrap();
    assert!(
        verify_multiplication_sound(&m1, &m2, &[1.0, 2.0, 3.0, 4.0], &[5.0, 6.0, 7.0, 8.0]).is_ok()
    );
}

#[test]
fn test_verify_multiply_sound_interval() {
    let m1 = IntervalMatrix::new(1, 1, vec![1.0], vec![3.0]).unwrap();
    let m2 = IntervalMatrix::new(1, 1, vec![2.0], vec![4.0]).unwrap();
    assert!(verify_multiplication_sound(&m1, &m2, &[2.0], &[3.0]).is_ok());
}

#[test]
fn test_verify_multiply_sound_concrete_outside() {
    let m1 = IntervalMatrix::new(1, 1, vec![1.0], vec![2.0]).unwrap();
    let m2 = IntervalMatrix::new(1, 1, vec![1.0], vec![2.0]).unwrap();
    assert!(verify_multiplication_sound(&m1, &m2, &[5.0], &[1.0]).is_err());
}

// -- frobenius_norm_interval --

#[test]
fn test_frobenius_point_matrix() {
    let m = IntervalMatrix::new(1, 2, vec![3.0, 4.0], vec![3.0, 4.0]).unwrap();
    let (lo, hi) = frobenius_norm_interval(&m);
    assert!(approx_eq(lo, 5.0));
    assert!(approx_eq(hi, 5.0));
}

#[test]
fn test_frobenius_interval_containing_zero() {
    let m = IntervalMatrix::new(1, 1, vec![-1.0], vec![1.0]).unwrap();
    let (lo, hi) = frobenius_norm_interval(&m);
    assert!(approx_eq(lo, 0.0));
    assert!(approx_eq(hi, 1.0));
}

#[test]
fn test_frobenius_zeros() {
    let (lo, hi) = frobenius_norm_interval(&IntervalMatrix::zeros(3, 3));
    assert!(approx_eq(lo, 0.0));
    assert!(approx_eq(hi, 0.0));
}

#[test]
fn test_frobenius_identity() {
    let (lo, hi) = frobenius_norm_interval(&IntervalMatrix::identity(3));
    assert!(approx_eq(lo, 3.0_f64.sqrt()));
    assert!(approx_eq(hi, 3.0_f64.sqrt()));
}

#[test]
fn test_frobenius_negative_interval() {
    let m = IntervalMatrix::new(1, 1, vec![-5.0], vec![-2.0]).unwrap();
    let (lo, hi) = frobenius_norm_interval(&m);
    assert!(approx_eq(lo, 2.0));
    assert!(approx_eq(hi, 5.0));
}

// -- spectral_radius_bound --

#[test]
fn test_spectral_nonsquare_returns_none() {
    assert!(spectral_radius_bound(&IntervalMatrix::zeros(2, 3)).is_none());
}

#[test]
fn test_spectral_empty() {
    assert!(approx_eq(
        spectral_radius_bound(&IntervalMatrix::zeros(0, 0)).unwrap(),
        0.0
    ));
}

#[test]
fn test_spectral_identity() {
    assert!(approx_eq(
        spectral_radius_bound(&IntervalMatrix::identity(3)).unwrap(),
        1.0
    ));
}

#[test]
fn test_spectral_diagonal() {
    let m = IntervalMatrix::new(
        3,
        3,
        vec![2.0, 0.0, 0.0, 0.0, -3.0, 0.0, 0.0, 0.0, 1.0],
        vec![2.0, 0.0, 0.0, 0.0, -3.0, 0.0, 0.0, 0.0, 1.0],
    )
    .unwrap();
    assert!(approx_eq(spectral_radius_bound(&m).unwrap(), 3.0));
}

#[test]
fn test_spectral_with_off_diagonal() {
    let m = IntervalMatrix::new(2, 2, vec![5.0, 1.0, 1.0, 5.0], vec![5.0, 1.0, 1.0, 5.0]).unwrap();
    assert!(approx_eq(spectral_radius_bound(&m).unwrap(), 6.0));
}

#[test]
fn test_spectral_1x1_interval() {
    let m = IntervalMatrix::new(1, 1, vec![-3.0], vec![2.0]).unwrap();
    assert!(approx_eq(spectral_radius_bound(&m).unwrap(), 3.0));
}

// -- Soundness: random concrete matrices within intervals --

fn pseudo_rand(seed: u64, lo: f64, hi: f64) -> f64 {
    let t =
        ((seed.wrapping_mul(6364136223846793005).wrapping_add(1)) >> 33) as f64 / (u32::MAX as f64);
    lo + t * (hi - lo)
}

#[test]
fn test_multiply_soundness_random_2x2() {
    let m1 =
        IntervalMatrix::new(2, 2, vec![-1.0, 0.0, -2.0, 1.0], vec![1.0, 3.0, 0.0, 4.0]).unwrap();
    let m2 =
        IntervalMatrix::new(2, 2, vec![0.0, -1.0, 1.0, 0.0], vec![2.0, 1.0, 3.0, 2.0]).unwrap();
    for trial in 0..20_u64 {
        let a: Vec<f64> = (0..4_u64)
            .map(|k| {
                pseudo_rand(
                    trial * 100 + k,
                    m1.lo((k / 2) as usize, (k % 2) as usize),
                    m1.hi((k / 2) as usize, (k % 2) as usize),
                )
            })
            .collect();
        let b: Vec<f64> = (0..4_u64)
            .map(|k| {
                pseudo_rand(
                    trial * 100 + k + 50,
                    m2.lo((k / 2) as usize, (k % 2) as usize),
                    m2.hi((k / 2) as usize, (k % 2) as usize),
                )
            })
            .collect();
        verify_multiplication_sound(&m1, &m2, &a, &b)
            .unwrap_or_else(|e| panic!("trial {trial} failed: {e}"));
    }
}

#[test]
fn test_matvec_soundness_random() {
    let m = IntervalMatrix::new(
        2,
        3,
        vec![-1.0, 0.0, -2.0, 1.0, -1.0, 0.0],
        vec![1.0, 3.0, 0.0, 4.0, 1.0, 2.0],
    )
    .unwrap();
    let vl = vec![-1.0, 0.0, -1.0];
    let vh = vec![1.0, 2.0, 1.0];
    let (out_lo, out_hi) = interval_matrix_vector_multiply(&m, &vl, &vh).unwrap();
    for trial in 0..20_u64 {
        let v: Vec<f64> = (0..3_u64)
            .map(|k| pseudo_rand(trial * 10 + k, vl[k as usize], vh[k as usize]))
            .collect();
        for i in 0..2_usize {
            let mut y = 0.0;
            for (j, &vj) in v.iter().enumerate() {
                let w = pseudo_rand(trial * 10 + 30 + (i * 3 + j) as u64, m.lo(i, j), m.hi(i, j));
                y += w * vj;
            }
            assert!(
                y >= out_lo[i] - EPS && y <= out_hi[i] + EPS,
                "trial {trial}, row {i}: y={y} not in [{}, {}]",
                out_lo[i],
                out_hi[i]
            );
        }
    }
}
