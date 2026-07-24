// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for norm types, computation, and theorem properties.

use super::compute::*;
use super::theorems::*;
use super::types::*;
use crate::theories::rational::Rational;
use proptest::prelude::*;

// ---------------------------------------------------------------------------
// Unit tests — types
// ---------------------------------------------------------------------------

#[test]
fn test_norm_kind_display() {
    assert_eq!(NormKind::L1.to_string(), "L1");
    assert_eq!(NormKind::L2.to_string(), "L2");
    assert_eq!(NormKind::Linf.to_string(), "L\u{221e}");
}

#[test]
fn test_vector_basic() {
    let v = Vector::new(vec![1.0, 2.0, 3.0]);
    assert_eq!(v.dim(), 3);
    assert_eq!(v.as_slice(), &[1.0, 2.0, 3.0]);
}

#[test]
fn test_vector_from_vec() {
    let v: Vector<f64> = vec![4.0, 5.0].into();
    assert_eq!(v.dim(), 2);
}

#[test]
fn test_vector_into_inner() {
    let v = Vector::new(vec![1.0, 2.0]);
    assert_eq!(v.into_inner(), vec![1.0, 2.0]);
}

#[test]
fn test_matrix_construction() {
    let m = Matrix::new(vec![1.0, 2.0, 3.0, 4.0], 2, 2).expect("valid dims");
    assert_eq!(m.rows(), 2);
    assert_eq!(m.cols(), 2);
    assert_eq!(*m.get(0, 0), 1.0);
    assert_eq!(*m.get(0, 1), 2.0);
    assert_eq!(*m.get(1, 0), 3.0);
    assert_eq!(*m.get(1, 1), 4.0);
}

#[test]
fn test_matrix_dim_error() {
    let err = Matrix::new(vec![1.0, 2.0, 3.0], 2, 2).unwrap_err();
    assert_eq!(
        err.to_string(),
        "matrix dimension mismatch: expected 2x2=4 elements, got 3"
    );
}

#[test]
fn test_matrix_row_iter() {
    let m = Matrix::new(vec![1.0, 2.0, 3.0, 4.0, 5.0, 6.0], 2, 3).unwrap();
    let rows: Vec<&[f64]> = m.row_iter().collect();
    assert_eq!(rows, vec![&[1.0, 2.0, 3.0][..], &[4.0, 5.0, 6.0][..]]);
}

// ---------------------------------------------------------------------------
// Unit tests — vector norm computation
// ---------------------------------------------------------------------------

#[test]
fn test_l1_norm_basic() {
    let v = Vector::new(vec![1.0, -2.0, 3.0]);
    assert!((l1_norm(&v) - 6.0).abs() < 1e-12);
}

#[test]
fn test_l2_norm_basic() {
    // ||[3, 4]||_2 = 5
    let v = Vector::new(vec![3.0, 4.0]);
    assert!((l2_norm(&v) - 5.0).abs() < 1e-12);
}

#[test]
fn test_linf_norm_basic() {
    let v = Vector::new(vec![1.0, -5.0, 3.0]);
    assert!((linf_norm(&v) - 5.0).abs() < 1e-12);
}

#[test]
fn test_vector_norm_dispatch() {
    let v = Vector::new(vec![3.0, 4.0]);
    assert!((vector_norm(&v, NormKind::L1) - 7.0).abs() < 1e-12);
    assert!((vector_norm(&v, NormKind::L2) - 5.0).abs() < 1e-12);
    assert!((vector_norm(&v, NormKind::Linf) - 4.0).abs() < 1e-12);
}

#[test]
fn test_norm_zero_vector() {
    let v = Vector::new(vec![0.0, 0.0, 0.0]);
    assert_eq!(l1_norm(&v), 0.0);
    assert_eq!(l2_norm(&v), 0.0);
    assert_eq!(linf_norm(&v), 0.0);
}

#[test]
fn test_norm_empty_vector() {
    let v = Vector::new(vec![]);
    assert_eq!(l1_norm(&v), 0.0);
    assert_eq!(l2_norm(&v), 0.0);
    assert_eq!(linf_norm(&v), 0.0);
}

#[test]
fn test_norm_single_element() {
    let v = Vector::new(vec![-7.0]);
    assert!((l1_norm(&v) - 7.0).abs() < 1e-12);
    assert!((l2_norm(&v) - 7.0).abs() < 1e-12);
    assert!((linf_norm(&v) - 7.0).abs() < 1e-12);
}

// ---------------------------------------------------------------------------
// Unit tests — exact rational norms
// ---------------------------------------------------------------------------

#[test]
fn test_l1_norm_exact_basic() {
    let v = Vector::new(vec![
        Rational::new(1, 2),
        Rational::new(-3, 4),
        Rational::new(1, 4),
    ]);
    // |1/2| + |3/4| + |1/4| = 1/2 + 3/4 + 1/4 = 3/2
    let result = l1_norm_exact(&v).expect("no overflow");
    assert_eq!(result, Rational::new(3, 2));
}

#[test]
fn test_linf_norm_exact_basic() {
    let v = Vector::new(vec![
        Rational::new(1, 3),
        Rational::new(-2, 3),
        Rational::new(1, 6),
    ]);
    // max(|1/3|, |2/3|, |1/6|) = 2/3
    let result = linf_norm_exact(&v);
    assert_eq!(result, Rational::new(2, 3));
}

#[test]
fn test_linf_norm_exact_empty() {
    let v: Vector<Rational> = Vector::new(vec![]);
    assert_eq!(linf_norm_exact(&v), Rational::ZERO);
}

// ---------------------------------------------------------------------------
// Unit tests — matrix norms
// ---------------------------------------------------------------------------

#[test]
fn test_matrix_l1_norm_basic() {
    // [[1, -3], [2, 4]]
    // col 0: |1|+|2|=3, col 1: |-3|+|4|=7 → max=7
    let m = Matrix::new(vec![1.0, -3.0, 2.0, 4.0], 2, 2).unwrap();
    assert!((matrix_l1_norm(&m) - 7.0).abs() < 1e-12);
}

#[test]
fn test_matrix_linf_norm_basic() {
    // [[1, -3], [2, 4]]
    // row 0: |1|+|-3|=4, row 1: |2|+|4|=6 → max=6
    let m = Matrix::new(vec![1.0, -3.0, 2.0, 4.0], 2, 2).unwrap();
    assert!((matrix_linf_norm(&m) - 6.0).abs() < 1e-12);
}

#[test]
fn test_matrix_frobenius_norm_basic() {
    // [[1, 2], [3, 4]]: sqrt(1+4+9+16) = sqrt(30)
    let m = Matrix::new(vec![1.0, 2.0, 3.0, 4.0], 2, 2).unwrap();
    assert!((matrix_frobenius_norm(&m) - 30.0_f64.sqrt()).abs() < 1e-12);
}

#[test]
fn test_matrix_empty() {
    let m = Matrix::new(vec![], 0, 0).unwrap();
    assert_eq!(matrix_l1_norm(&m), 0.0);
    assert_eq!(matrix_linf_norm(&m), 0.0);
    assert_eq!(matrix_frobenius_norm(&m), 0.0);
}

// ---------------------------------------------------------------------------
// Unit tests — theorems
// ---------------------------------------------------------------------------

#[test]
fn test_triangle_inequality_concrete() {
    let x = Vector::new(vec![1.0, -2.0, 3.0]);
    let y = Vector::new(vec![-1.0, 4.0, -1.0]);
    assert!(check_triangle_inequality(&x, &y, NormKind::L1));
    assert!(check_triangle_inequality(&x, &y, NormKind::L2));
    assert!(check_triangle_inequality(&x, &y, NormKind::Linf));
}

#[test]
fn test_triangle_inequality_dimension_mismatch() {
    let x = Vector::new(vec![1.0, 2.0]);
    let y = Vector::new(vec![1.0, 2.0, 3.0]);
    assert!(!check_triangle_inequality(&x, &y, NormKind::L1));
}

#[test]
fn test_submultiplicativity_concrete() {
    let a = Matrix::new(vec![1.0, 2.0, 3.0, 4.0], 2, 2).unwrap();
    let x = Vector::new(vec![1.0, -1.0]);
    assert!(check_submultiplicativity(&a, &x, NormKind::L1));
    assert!(check_submultiplicativity(&a, &x, NormKind::L2));
    assert!(check_submultiplicativity(&a, &x, NormKind::Linf));
}

#[test]
fn test_submultiplicativity_dimension_mismatch() {
    let a = Matrix::new(vec![1.0, 2.0, 3.0, 4.0], 2, 2).unwrap();
    let x = Vector::new(vec![1.0, 2.0, 3.0]);
    assert!(!check_submultiplicativity(&a, &x, NormKind::L1));
}

#[test]
fn test_norm_equivalence_chain_concrete() {
    let x = Vector::new(vec![1.0, -2.0, 3.0, -4.0]);
    assert!(check_norm_equivalence_chain(&x));
}

#[test]
fn test_l2_linf_bound_concrete() {
    let x = Vector::new(vec![1.0, 1.0, 1.0, 1.0]);
    // ||x||_2 = 2, sqrt(4)*||x||_inf = 2*1 = 2, so equality
    assert!(check_l2_linf_bound(&x));
}

#[test]
fn test_l1_l2_bound_concrete() {
    let x = Vector::new(vec![1.0, 1.0, 1.0, 1.0]);
    // ||x||_1 = 4, sqrt(4)*||x||_2 = 2*2 = 4, so equality
    assert!(check_l1_l2_bound(&x));
}

// ---------------------------------------------------------------------------
// Property-based tests (proptest)
// ---------------------------------------------------------------------------

/// Strategy for generating Vector<f64> of a given dimension range.
fn arb_vector(min_dim: usize, max_dim: usize) -> impl Strategy<Value = Vector<f64>> {
    prop::collection::vec(-100.0..100.0_f64, min_dim..=max_dim).prop_map(Vector::new)
}

/// Strategy for generating a pair of same-dimension vectors.
fn arb_vector_pair(
    min_dim: usize,
    max_dim: usize,
) -> impl Strategy<Value = (Vector<f64>, Vector<f64>)> {
    (min_dim..=max_dim).prop_flat_map(|n| {
        (
            prop::collection::vec(-100.0..100.0_f64, n).prop_map(Vector::new),
            prop::collection::vec(-100.0..100.0_f64, n).prop_map(Vector::new),
        )
    })
}

/// Strategy for generating a Matrix and compatible Vector.
fn arb_matrix_vector(max_dim: usize) -> impl Strategy<Value = (Matrix<f64>, Vector<f64>)> {
    (1..=max_dim, 1..=max_dim).prop_flat_map(|(rows, cols)| {
        (
            prop::collection::vec(-10.0..10.0_f64, rows * cols)
                .prop_map(move |data| Matrix::new(data, rows, cols).unwrap()),
            prop::collection::vec(-10.0..10.0_f64, cols).prop_map(Vector::new),
        )
    })
}

proptest! {
    #[test]
    fn prop_l1_norm_nonneg(v in arb_vector(0, 20)) {
        prop_assert!(l1_norm(&v) >= 0.0);
    }

    #[test]
    fn prop_l2_norm_nonneg(v in arb_vector(0, 20)) {
        prop_assert!(l2_norm(&v) >= 0.0);
    }

    #[test]
    fn prop_linf_norm_nonneg(v in arb_vector(0, 20)) {
        prop_assert!(linf_norm(&v) >= 0.0);
    }

    #[test]
    fn prop_linf_le_l2(v in arb_vector(1, 20)) {
        let ni = linf_norm(&v);
        let n2 = l2_norm(&v);
        prop_assert!(ni <= n2 + 1e-10 * n2.abs().max(1.0),
            "||x||_inf={ni} > ||x||_2={n2}");
    }

    #[test]
    fn prop_l2_le_l1(v in arb_vector(1, 20)) {
        let n2 = l2_norm(&v);
        let n1 = l1_norm(&v);
        prop_assert!(n2 <= n1 + 1e-10 * n1.abs().max(1.0),
            "||x||_2={n2} > ||x||_1={n1}");
    }

    #[test]
    fn prop_triangle_inequality_l1((x, y) in arb_vector_pair(1, 20)) {
        prop_assert!(check_triangle_inequality(&x, &y, NormKind::L1));
    }

    #[test]
    fn prop_triangle_inequality_l2((x, y) in arb_vector_pair(1, 20)) {
        prop_assert!(check_triangle_inequality(&x, &y, NormKind::L2));
    }

    #[test]
    fn prop_triangle_inequality_linf((x, y) in arb_vector_pair(1, 20)) {
        prop_assert!(check_triangle_inequality(&x, &y, NormKind::Linf));
    }

    #[test]
    fn prop_norm_equivalence_chain(v in arb_vector(1, 20)) {
        prop_assert!(check_norm_equivalence_chain(&v));
    }

    #[test]
    fn prop_l2_linf_bound(v in arb_vector(1, 20)) {
        prop_assert!(check_l2_linf_bound(&v));
    }

    #[test]
    fn prop_l1_l2_bound(v in arb_vector(1, 20)) {
        prop_assert!(check_l1_l2_bound(&v));
    }

    #[test]
    fn prop_submultiplicativity_l1((a, x) in arb_matrix_vector(8)) {
        prop_assert!(check_submultiplicativity(&a, &x, NormKind::L1));
    }

    #[test]
    fn prop_submultiplicativity_linf((a, x) in arb_matrix_vector(8)) {
        prop_assert!(check_submultiplicativity(&a, &x, NormKind::Linf));
    }

    #[test]
    fn prop_submultiplicativity_l2((a, x) in arb_matrix_vector(8)) {
        prop_assert!(check_submultiplicativity(&a, &x, NormKind::L2));
    }

    #[test]
    fn prop_homogeneity_l1(v in arb_vector(1, 20), c in -100.0..100.0_f64) {
        // ||c*x||_1 = |c| * ||x||_1
        let scaled = Vector::new(v.as_slice().iter().map(|x| x * c).collect());
        let lhs = l1_norm(&scaled);
        let rhs = c.abs() * l1_norm(&v);
        prop_assert!((lhs - rhs).abs() < 1e-8 * rhs.abs().max(1.0),
            "homogeneity: ||c*x||_1={lhs} != |c|*||x||_1={rhs}");
    }

    #[test]
    fn prop_homogeneity_l2(v in arb_vector(1, 20), c in -100.0..100.0_f64) {
        let scaled = Vector::new(v.as_slice().iter().map(|x| x * c).collect());
        let lhs = l2_norm(&scaled);
        let rhs = c.abs() * l2_norm(&v);
        prop_assert!((lhs - rhs).abs() < 1e-8 * rhs.abs().max(1.0),
            "homogeneity: ||c*x||_2={lhs} != |c|*||x||_2={rhs}");
    }

    #[test]
    fn prop_homogeneity_linf(v in arb_vector(1, 20), c in -100.0..100.0_f64) {
        let scaled = Vector::new(v.as_slice().iter().map(|x| x * c).collect());
        let lhs = linf_norm(&scaled);
        let rhs = c.abs() * linf_norm(&v);
        prop_assert!((lhs - rhs).abs() < 1e-8 * rhs.abs().max(1.0),
            "homogeneity: ||c*x||_inf={lhs} != |c|*||x||_inf={rhs}");
    }
}
