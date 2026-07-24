// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for L1/L2/Linf norm instances and theorem verifiers.

use num_rational::Rational64;

use super::*;
use crate::spec::ProofStatus;

fn r(n: i64) -> Rational64 {
    Rational64::from_integer(n)
}

fn frac(n: i64, d: i64) -> Rational64 {
    Rational64::new(n, d)
}

// ---------------------------------------------------------------------------
// Proof status tracking
// ---------------------------------------------------------------------------

#[test]
fn test_proof_status_tracking() {
    assert!(matches!(
        T08_L1_L2_LINF_ORDERING,
        ProofStatus::DerivedPending
    ));
    assert!(matches!(T09_HOLDER_INEQUALITY, ProofStatus::DerivedPending));
    assert!(matches!(
        T10_MATRIX_NORM_SUBMULTIPLICATIVE,
        ProofStatus::DerivedPending
    ));
    assert!(matches!(
        T11_TRIANGLE_INEQUALITY,
        ProofStatus::DerivedPending
    ));
    assert!(matches!(T12_DUAL_NORM_DUALITY, ProofStatus::DerivedPending));
}

// ---------------------------------------------------------------------------
// NormKind basics
// ---------------------------------------------------------------------------

#[test]
fn test_norm_kind_debug_clone_eq() {
    let k = NormKind::L1;
    assert_eq!(k, k.clone());
    assert_ne!(NormKind::L1, NormKind::L2);
    assert_ne!(NormKind::L2, NormKind::Linf);
    let _ = format!("{:?}", k);
}

// ---------------------------------------------------------------------------
// Vector norms
// ---------------------------------------------------------------------------

#[test]
fn test_vector_norm_empty() {
    let v: Vec<Rational64> = vec![];
    assert_eq!(vector_norm(&v, NormKind::L1), r(0));
    assert_eq!(vector_norm(&v, NormKind::L2), r(0));
    assert_eq!(vector_norm(&v, NormKind::Linf), r(0));
}

#[test]
fn test_vector_norm_l1() {
    let v = vec![r(3), r(-4), r(0)];
    assert_eq!(vector_norm(&v, NormKind::L1), r(7));
}

#[test]
fn test_vector_norm_l2_squared() {
    let v = vec![r(3), r(-4)];
    // 9 + 16 = 25
    assert_eq!(vector_norm(&v, NormKind::L2), r(25));
}

#[test]
fn test_vector_norm_linf() {
    let v = vec![r(3), r(-4), r(2)];
    assert_eq!(vector_norm(&v, NormKind::Linf), r(4));
}

#[test]
fn test_vector_norm_single_element() {
    let v = vec![r(-5)];
    assert_eq!(vector_norm(&v, NormKind::L1), r(5));
    assert_eq!(vector_norm(&v, NormKind::L2), r(25));
    assert_eq!(vector_norm(&v, NormKind::Linf), r(5));
}

#[test]
fn test_vector_norm_fractional() {
    let v = vec![frac(1, 2), frac(-3, 4)];
    // L1: 1/2 + 3/4 = 5/4
    assert_eq!(vector_norm(&v, NormKind::L1), frac(5, 4));
    // L2: (1/2)^2 + (3/4)^2 = 1/4 + 9/16 = 13/16
    assert_eq!(vector_norm(&v, NormKind::L2), frac(13, 16));
    // Linf: max(1/2, 3/4) = 3/4
    assert_eq!(vector_norm(&v, NormKind::Linf), frac(3, 4));
}

// ---------------------------------------------------------------------------
// Dot product
// ---------------------------------------------------------------------------

#[test]
fn test_dot_product_basic() {
    let u = vec![r(1), r(2), r(3)];
    let v = vec![r(4), r(5), r(6)];
    // 4 + 10 + 18 = 32
    assert_eq!(dot_product(&u, &v).unwrap(), r(32));
}

#[test]
fn test_dot_product_dimension_mismatch() {
    let u = vec![r(1), r(2)];
    let v = vec![r(1)];
    assert!(dot_product(&u, &v).is_err());
}

// ---------------------------------------------------------------------------
// Vector add
// ---------------------------------------------------------------------------

#[test]
fn test_vector_add_basic() {
    let u = vec![r(1), r(-2), r(3)];
    let v = vec![r(4), r(5), r(-6)];
    let sum = vector_add(&u, &v).unwrap();
    assert_eq!(sum, vec![r(5), r(3), r(-3)]);
}

#[test]
fn test_vector_add_dimension_mismatch() {
    let u = vec![r(1)];
    let v = vec![r(1), r(2)];
    assert!(vector_add(&u, &v).is_err());
}

// ---------------------------------------------------------------------------
// Matrix norms
// ---------------------------------------------------------------------------

#[test]
fn test_matrix_norm_l1_induced() {
    // Col 0 abs-sum: |1| + |3| = 4; Col 1 abs-sum: |-2| + |4| = 6
    let m = vec![vec![r(1), r(-2)], vec![r(3), r(4)]];
    assert_eq!(matrix_norm(&m, NormKind::L1).unwrap(), r(6));
}

#[test]
fn test_matrix_norm_linf_induced() {
    // Row 0 abs-sum: |1| + |-2| = 3; Row 1 abs-sum: |3| + |4| = 7
    let m = vec![vec![r(1), r(-2)], vec![r(3), r(4)]];
    assert_eq!(matrix_norm(&m, NormKind::Linf).unwrap(), r(7));
}

#[test]
fn test_matrix_norm_l2_frobenius_upper_bound() {
    // Frobenius squared: 1 + 4 + 9 + 16 = 30
    let m = vec![vec![r(1), r(-2)], vec![r(3), r(4)]];
    assert_eq!(matrix_norm(&m, NormKind::L2).unwrap(), r(30));
}

#[test]
fn test_matrix_norm_identity() {
    let id = vec![vec![r(1), r(0)], vec![r(0), r(1)]];
    assert_eq!(matrix_norm(&id, NormKind::L1).unwrap(), r(1));
    assert_eq!(matrix_norm(&id, NormKind::Linf).unwrap(), r(1));
}

#[test]
fn test_matrix_norm_empty_error() {
    let m: Vec<Vec<Rational64>> = vec![];
    assert!(matrix_norm(&m, NormKind::L1).is_err());
}

#[test]
fn test_matrix_norm_inconsistent_row_error() {
    let m = vec![vec![r(1), r(2)], vec![r(3)]];
    assert!(matrix_norm(&m, NormKind::L1).is_err());
}

// ---------------------------------------------------------------------------
// Matrix multiply
// ---------------------------------------------------------------------------

#[test]
fn test_matrix_multiply_basic() {
    let a = vec![vec![r(1), r(2)], vec![r(3), r(4)]];
    let b = vec![vec![r(5), r(6)], vec![r(7), r(8)]];
    let c = matrix_multiply(&a, &b).unwrap();
    assert_eq!(c, vec![vec![r(19), r(22)], vec![r(43), r(50)]]);
}

#[test]
fn test_matrix_multiply_dimension_mismatch() {
    let a = vec![vec![r(1), r(2)]];
    let b = vec![vec![r(1)]]; // 1x1, but a is 1x2
    assert!(matrix_multiply(&a, &b).is_err());
}

// ---------------------------------------------------------------------------
// Dual norm
// ---------------------------------------------------------------------------

#[test]
fn test_dual_norm_l1_linf() {
    assert_eq!(dual_norm(NormKind::L1), NormKind::Linf);
    assert_eq!(dual_norm(NormKind::Linf), NormKind::L1);
}

#[test]
fn test_dual_norm_l2_self_dual() {
    assert_eq!(dual_norm(NormKind::L2), NormKind::L2);
}

#[test]
fn test_dual_norm_involution() {
    for kind in [NormKind::L1, NormKind::L2, NormKind::Linf] {
        assert_eq!(dual_norm(dual_norm(kind)), kind);
    }
}

// ---------------------------------------------------------------------------
// Theorem: L1/L2/Linf ordering
// ---------------------------------------------------------------------------

#[test]
fn test_l1_l2_linf_ordering_basic() {
    let v = vec![r(3), r(-4), r(1)];
    assert!(verify_l1_l2_linf_ordering(&v));
}

#[test]
fn test_l1_l2_linf_ordering_single() {
    let v = vec![r(7)];
    assert!(verify_l1_l2_linf_ordering(&v));
}

#[test]
fn test_l1_l2_linf_ordering_zeros() {
    let v = vec![r(0), r(0), r(0)];
    assert!(verify_l1_l2_linf_ordering(&v));
}

#[test]
fn test_l1_l2_linf_ordering_fractional() {
    let v = vec![frac(1, 3), frac(-2, 5), frac(7, 10)];
    assert!(verify_l1_l2_linf_ordering(&v));
}

// ---------------------------------------------------------------------------
// Theorem: Holder inequality (L1/Linf pair)
// ---------------------------------------------------------------------------

#[test]
fn test_holder_l1_linf_basic() {
    let u = vec![r(1), r(2), r(3)];
    let v = vec![r(-1), r(4), r(2)];
    assert!(verify_holder_l1_linf(&u, &v).unwrap());
}

#[test]
fn test_holder_l1_linf_zeros() {
    let u = vec![r(0), r(0)];
    let v = vec![r(5), r(10)];
    assert!(verify_holder_l1_linf(&u, &v).unwrap());
}

// ---------------------------------------------------------------------------
// Theorem: Holder inequality (L2/L2 = Cauchy-Schwarz)
// ---------------------------------------------------------------------------

#[test]
fn test_holder_l2_cauchy_schwarz() {
    let u = vec![r(1), r(2), r(3)];
    let v = vec![r(-1), r(4), r(2)];
    assert!(verify_holder_l2(&u, &v).unwrap());
}

#[test]
fn test_holder_l2_parallel_vectors() {
    let u = vec![r(1), r(2)];
    let v = vec![r(2), r(4)];
    // |u.v|^2 = (2+8)^2 = 100, ||u||^2 * ||v||^2 = 5 * 20 = 100
    assert!(verify_holder_l2(&u, &v).unwrap());
}

// ---------------------------------------------------------------------------
// Theorem: Triangle inequality
// ---------------------------------------------------------------------------

#[test]
fn test_triangle_inequality_l1() {
    let u = vec![r(1), r(-2), r(3)];
    let v = vec![r(-4), r(5), r(-1)];
    assert!(verify_triangle_inequality(&u, &v, NormKind::L1).unwrap());
}

#[test]
fn test_triangle_inequality_linf() {
    let u = vec![r(1), r(-2), r(3)];
    let v = vec![r(-4), r(5), r(-1)];
    assert!(verify_triangle_inequality(&u, &v, NormKind::Linf).unwrap());
}

#[test]
fn test_triangle_inequality_l2() {
    let u = vec![r(1), r(-2), r(3)];
    let v = vec![r(-4), r(5), r(-1)];
    assert!(verify_triangle_inequality(&u, &v, NormKind::L2).unwrap());
}

#[test]
fn test_triangle_inequality_zeros() {
    let u = vec![r(0), r(0)];
    let v = vec![r(0), r(0)];
    for kind in [NormKind::L1, NormKind::L2, NormKind::Linf] {
        assert!(verify_triangle_inequality(&u, &v, kind).unwrap());
    }
}

// ---------------------------------------------------------------------------
// Theorem: Matrix norm submultiplicativity
// ---------------------------------------------------------------------------

#[test]
fn test_submultiplicativity_l1() {
    let a = vec![vec![r(1), r(2)], vec![r(3), r(4)]];
    let b = vec![vec![r(5), r(6)], vec![r(7), r(8)]];
    assert!(verify_matrix_norm_submultiplicative(&a, &b, NormKind::L1).unwrap());
}

#[test]
fn test_submultiplicativity_linf() {
    let a = vec![vec![r(1), r(2)], vec![r(3), r(4)]];
    let b = vec![vec![r(5), r(6)], vec![r(7), r(8)]];
    assert!(verify_matrix_norm_submultiplicative(&a, &b, NormKind::Linf).unwrap());
}

#[test]
fn test_submultiplicativity_identity() {
    let id = vec![vec![r(1), r(0)], vec![r(0), r(1)]];
    let m = vec![vec![r(3), r(-1)], vec![r(2), r(5)]];
    for kind in [NormKind::L1, NormKind::Linf] {
        assert!(verify_matrix_norm_submultiplicative(&id, &m, kind).unwrap());
    }
}

// ---------------------------------------------------------------------------
// Theorem: Dual norm duality
// ---------------------------------------------------------------------------

#[test]
fn test_dual_norm_duality_l1_basic() {
    let v = vec![r(3), r(-4), r(1)];
    assert!(verify_dual_norm_duality_l1(&v));
}

#[test]
fn test_dual_norm_duality_l1_zeros() {
    let v = vec![r(0), r(0), r(0)];
    assert!(verify_dual_norm_duality_l1(&v));
}

#[test]
fn test_dual_norm_duality_l1_single() {
    let v = vec![r(-7)];
    assert!(verify_dual_norm_duality_l1(&v));
}

#[test]
fn test_dual_norm_duality_l1_fractional() {
    let v = vec![frac(1, 3), frac(-5, 7)];
    assert!(verify_dual_norm_duality_l1(&v));
}

// ---------------------------------------------------------------------------
// Error display
// ---------------------------------------------------------------------------

#[test]
fn test_norm_error_display() {
    let e = NormError::InconsistentRowLength {
        row: 1,
        got: 3,
        expected: 2,
    };
    assert!(format!("{e}").contains("row 1"));

    let e = NormError::EmptyMatrix;
    assert!(format!("{e}").contains("empty"));

    let e = NormError::DimensionMismatch { left: 2, right: 3 };
    assert!(format!("{e}").contains("2"));
}
