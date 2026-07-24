// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for spectral norm verification properties (spectral_norm module).

use super::ibp::Interval;
use super::spectral_norm::*;

// -- Proof status constants --------------------------------------------------

#[test]
fn test_proof_status_constants_are_derived_pending() {
    use crate::spec::ProofStatus;
    assert_eq!(T32A_SPECTRAL_NORM_BOUND, ProofStatus::DerivedPending);
    assert_eq!(
        T32B_FROBENIUS_SPECTRAL_RELATION,
        ProofStatus::DerivedPending
    );
    assert_eq!(
        T32C_SPECTRAL_SUBMULTIPLICATIVITY,
        ProofStatus::DerivedPending
    );
}

// -- Power iteration: basic cases --------------------------------------------

#[test]
fn test_power_iteration_identity_2x2() {
    let matrix = vec![vec![1.0, 0.0], vec![0.0, 1.0]];
    let result = spectral_norm_power_iteration(&matrix, 50, 1e-10);
    assert!(
        (result.spectral_norm - 1.0).abs() < 1e-6,
        "identity spectral norm should be 1.0, got {}",
        result.spectral_norm
    );
}

#[test]
fn test_power_iteration_identity_3x3() {
    let matrix = vec![
        vec![1.0, 0.0, 0.0],
        vec![0.0, 1.0, 0.0],
        vec![0.0, 0.0, 1.0],
    ];
    let result = spectral_norm_power_iteration(&matrix, 50, 1e-10);
    assert!(
        (result.spectral_norm - 1.0).abs() < 1e-6,
        "3x3 identity spectral norm should be 1.0, got {}",
        result.spectral_norm
    );
}

#[test]
fn test_power_iteration_diagonal_max_entry() {
    let matrix = vec![
        vec![2.0, 0.0, 0.0],
        vec![0.0, 5.0, 0.0],
        vec![0.0, 0.0, 3.0],
    ];
    let result = spectral_norm_power_iteration(&matrix, 100, 1e-10);
    assert!(
        (result.spectral_norm - 5.0).abs() < 1e-6,
        "diag(2,5,3) spectral norm should be 5.0, got {}",
        result.spectral_norm
    );
}

#[test]
fn test_power_iteration_rank_one_matrix() {
    // rank-1: outer product of [1,2,3] with [4,5], sigma = sqrt(14)*sqrt(41)
    let u = [1.0, 2.0, 3.0];
    let v = [4.0, 5.0];
    let matrix: Vec<Vec<f64>> = u
        .iter()
        .map(|ui| v.iter().map(|vj| ui * vj).collect())
        .collect();
    let result = spectral_norm_power_iteration(&matrix, 100, 1e-12);
    let expected = (14.0_f64).sqrt() * (41.0_f64).sqrt();
    assert!(
        (result.spectral_norm - expected).abs() < 1e-4,
        "rank-1 spectral norm should be {expected:.4}, got {:.4}",
        result.spectral_norm
    );
}

#[test]
fn test_power_iteration_zero_matrix() {
    let matrix = vec![vec![0.0, 0.0], vec![0.0, 0.0]];
    let result = spectral_norm_power_iteration(&matrix, 50, 1e-10);
    assert!(
        result.spectral_norm < 1e-10,
        "zero matrix spectral norm should be ~0"
    );
    assert!(result.converged);
}

#[test]
fn test_power_iteration_empty_matrix() {
    let matrix: Vec<Vec<f64>> = vec![];
    let result = spectral_norm_power_iteration(&matrix, 50, 1e-10);
    assert!((result.spectral_norm).abs() < 1e-10);
    assert!(result.converged);
    assert_eq!(result.iterations_used, 0);
}

#[test]
fn test_power_iteration_1x1_matrix() {
    let matrix = vec![vec![7.5]];
    let result = spectral_norm_power_iteration(&matrix, 50, 1e-10);
    assert!(
        (result.spectral_norm - 7.5).abs() < 1e-6,
        "1x1 [[7.5]] spectral norm should be 7.5, got {}",
        result.spectral_norm
    );
}

#[test]
fn test_power_iteration_rectangular_3x2() {
    let matrix = vec![vec![1.0, 2.0], vec![3.0, 4.0], vec![5.0, 6.0]];
    let result = spectral_norm_power_iteration(&matrix, 100, 1e-12);
    assert!(
        (result.spectral_norm - 9.526).abs() < 0.01,
        "3x2 spectral norm should be ~9.526, got {:.3}",
        result.spectral_norm
    );
}

#[test]
fn test_power_iteration_rectangular_2x3() {
    // Transpose of the above: same singular values
    let matrix = vec![vec![1.0, 3.0, 5.0], vec![2.0, 4.0, 6.0]];
    let result = spectral_norm_power_iteration(&matrix, 100, 1e-12);
    assert!(
        (result.spectral_norm - 9.526).abs() < 0.01,
        "2x3 spectral norm should be ~9.526, got {:.3}",
        result.spectral_norm
    );
}

// -- Power iteration: convergence properties ---------------------------------

#[test]
fn test_power_iteration_convergence_flag() {
    let matrix = vec![vec![2.0, 0.0], vec![0.0, 3.0]];
    let result = spectral_norm_power_iteration(&matrix, 100, 1e-10);
    assert!(result.converged, "should converge for diagonal matrix");
    assert!(result.iterations_used < 100, "should converge early");
}

#[test]
fn test_power_iteration_convergence_improves_with_iterations() {
    let matrix = vec![vec![1.0, 2.0], vec![3.0, 4.0]];
    let result_5 = spectral_norm_power_iteration(&matrix, 5, 1e-15);
    let result_50 = spectral_norm_power_iteration(&matrix, 50, 1e-15);
    let exact = 29.866_f64.sqrt();
    assert!(
        (result_50.spectral_norm - exact).abs() <= (result_5.spectral_norm - exact).abs() + 1e-10,
        "50 iterations should be at least as accurate as 5"
    );
}

#[test]
fn test_power_iteration_zero_iterations() {
    let matrix = vec![vec![5.0, 0.0], vec![0.0, 3.0]];
    let result = spectral_norm_power_iteration(&matrix, 0, 1e-10);
    assert_eq!(result.iterations_used, 0);
}

// -- Bound verification ------------------------------------------------------

#[test]
fn test_verify_spectral_norm_bound_holds() {
    let matrix = vec![vec![2.0, 0.0], vec![0.0, 3.0]];
    assert!(verify_spectral_norm_bound(&matrix, 4.0, 50, 1e-10).is_ok());
}

#[test]
fn test_verify_spectral_norm_bound_tight() {
    let matrix = vec![vec![2.0, 0.0], vec![0.0, 3.0]];
    assert!(verify_spectral_norm_bound(&matrix, 3.0, 50, 1e-10).is_ok());
}

#[test]
fn test_verify_spectral_norm_bound_violated() {
    let matrix = vec![vec![2.0, 0.0], vec![0.0, 3.0]];
    assert!(verify_spectral_norm_bound(&matrix, 2.5, 50, 1e-10).is_err());
}

// -- Frobenius bound ---------------------------------------------------------

#[test]
fn test_frobenius_bound_identity() {
    let matrix = vec![vec![1.0, 0.0], vec![0.0, 1.0]];
    let frob = frobenius_to_spectral_bound(&matrix);
    assert!(
        (frob - 2.0_f64.sqrt()).abs() < 1e-10,
        "||I_2||_F should be sqrt(2), got {frob}"
    );
}

#[test]
fn test_frobenius_bound_diagonal() {
    let matrix = vec![vec![3.0, 0.0], vec![0.0, 4.0]];
    let frob = frobenius_to_spectral_bound(&matrix);
    assert!(
        (frob - 5.0).abs() < 1e-10,
        "||diag(3,4)||_F should be 5.0, got {frob}"
    );
}

#[test]
fn test_frobenius_always_ge_spectral() {
    let matrices: Vec<Vec<Vec<f64>>> = vec![
        vec![vec![1.0, 2.0], vec![3.0, 4.0]],
        vec![vec![1.0, 0.0, 0.0], vec![0.0, 5.0, 0.0]],
        vec![vec![1.0, 1.0], vec![1.0, 1.0]],
    ];
    for matrix in &matrices {
        let frob = frobenius_to_spectral_bound(matrix);
        let sigma = spectral_norm_power_iteration(matrix, 100, 1e-12).spectral_norm;
        assert!(
            frob >= sigma - 1e-6,
            "Frobenius {frob} should be >= spectral {sigma}"
        );
    }
}

#[test]
fn test_frobenius_tight_for_rank_one() {
    let u = [1.0, 0.0];
    let v = [0.0, 3.0];
    let matrix: Vec<Vec<f64>> = u
        .iter()
        .map(|ui| v.iter().map(|vj| ui * vj).collect())
        .collect();
    let frob = frobenius_to_spectral_bound(&matrix);
    let sigma = spectral_norm_power_iteration(&matrix, 100, 1e-12).spectral_norm;
    assert!(
        (frob - sigma).abs() < 1e-6,
        "Frobenius should be tight for rank-1"
    );
}

#[test]
fn test_frobenius_bound_empty() {
    let matrix: Vec<Vec<f64>> = vec![];
    assert!(frobenius_to_spectral_bound(&matrix).abs() < 1e-10);
}

// -- Rank-one update bound ---------------------------------------------------

#[test]
fn test_rank_one_update_zero_perturbation() {
    let bound = spectral_norm_rank_one_update(5.0, &[0.0, 0.0], &[0.0, 0.0]);
    assert!(
        (bound - 5.0).abs() < 1e-10,
        "zero perturbation keeps bound, got {bound}"
    );
}

#[test]
fn test_rank_one_update_unit_vectors() {
    // ||u|| = 1, ||v|| = 1, so bound = 3 + 1 = 4
    let bound = spectral_norm_rank_one_update(3.0, &[1.0, 0.0], &[0.0, 1.0]);
    assert!(
        (bound - 4.0).abs() < 1e-10,
        "rank-one update bound should be 4.0, got {bound}"
    );
}

#[test]
fn test_rank_one_update_correctness() {
    // W = diag(2,3), u=[1,0], v=[0,1] => W'=[[2,1],[0,3]]
    // Bound: sigma(W)+||u||*||v|| = 3+1 = 4, actual sigma(W') <= 4
    let w_prime = vec![vec![2.0, 1.0], vec![0.0, 3.0]];
    let actual = spectral_norm_power_iteration(&w_prime, 100, 1e-12).spectral_norm;
    let bound = spectral_norm_rank_one_update(3.0, &[1.0, 0.0], &[0.0, 1.0]);
    assert!(
        actual <= bound + 1e-6,
        "actual {actual} should be <= Weyl bound {bound}"
    );
}

#[test]
fn test_rank_one_update_large_perturbation() {
    // ||u||=5, ||v||=13 => bound = 1 + 65 = 66
    let bound = spectral_norm_rank_one_update(1.0, &[3.0, 4.0], &[5.0, 12.0]);
    assert!(
        (bound - 66.0).abs() < 1e-10,
        "bound should be 66, got {bound}"
    );
}

// -- Lipschitz via spectral (T32 core) ---------------------------------------

#[test]
fn test_verify_lipschitz_via_spectral_correct() {
    let matrix = vec![vec![3.0, 0.0], vec![0.0, 2.0]];
    assert!(verify_lipschitz_via_spectral(&matrix, 3.0, 50, 1e-3).is_ok());
}

#[test]
fn test_verify_lipschitz_via_spectral_incorrect() {
    let matrix = vec![vec![3.0, 0.0], vec![0.0, 2.0]];
    assert!(verify_lipschitz_via_spectral(&matrix, 5.0, 50, 1e-3).is_err());
}

#[test]
fn test_verify_lipschitz_via_spectral_identity() {
    let matrix = vec![vec![1.0, 0.0], vec![0.0, 1.0]];
    let result = verify_lipschitz_via_spectral(&matrix, 1.0, 50, 1e-6);
    assert!(result.is_ok());
    assert!((result.unwrap() - 1.0).abs() < 1e-6);
}

// -- Spectral gap ------------------------------------------------------------

#[test]
fn test_spectral_gap_well_separated() {
    // diag(10, 1): gap = 10/1 = 10
    let matrix = vec![vec![10.0, 0.0], vec![0.0, 1.0]];
    let gap = spectral_gap(&matrix, 100, 1e-10);
    assert!(gap.is_some());
    assert!(
        (gap.unwrap() - 10.0).abs() < 0.5,
        "spectral gap should be ~10, got {}",
        gap.unwrap()
    );
}

#[test]
fn test_spectral_gap_close_singular_values() {
    // diag(5, 4): gap = 5/4 = 1.25
    let matrix = vec![vec![5.0, 0.0], vec![0.0, 4.0]];
    let gap = spectral_gap(&matrix, 100, 1e-10);
    assert!(gap.is_some());
    assert!(
        (gap.unwrap() - 1.25).abs() < 0.1,
        "spectral gap should be ~1.25, got {}",
        gap.unwrap()
    );
}

#[test]
fn test_spectral_gap_rank_one_returns_none() {
    let matrix = vec![vec![1.0, 2.0], vec![2.0, 4.0]];
    assert!(
        spectral_gap(&matrix, 100, 1e-10).is_none(),
        "rank-1 has no sigma_2"
    );
}

#[test]
fn test_spectral_gap_empty_returns_none() {
    let matrix: Vec<Vec<f64>> = vec![];
    assert!(spectral_gap(&matrix, 50, 1e-10).is_none());
}

#[test]
fn test_spectral_gap_1x1_returns_none() {
    assert!(
        spectral_gap(&[vec![5.0]], 50, 1e-10).is_none(),
        "1x1 has no sigma_2"
    );
}

// -- Interval spectral norm --------------------------------------------------

#[test]
fn test_interval_spectral_norm_point_intervals() {
    let matrix = vec![
        vec![Interval::point(2.0), Interval::point(0.0)],
        vec![Interval::point(0.0), Interval::point(3.0)],
    ];
    let result = spectral_norm_interval(&matrix, 100, 1e-10);
    assert!(
        (result.lower - 3.0).abs() < 1e-6,
        "lower should be 3.0, got {}",
        result.lower
    );
    assert!(
        (result.upper - 3.0).abs() < 1e-6,
        "upper should be 3.0, got {}",
        result.upper
    );
}

#[test]
fn test_interval_spectral_norm_contains_point() {
    let matrix = vec![
        vec![Interval::new(1.0, 3.0), Interval::new(-1.0, 1.0)],
        vec![Interval::new(-1.0, 1.0), Interval::new(2.0, 4.0)],
    ];
    let interval_result = spectral_norm_interval(&matrix, 100, 1e-10);
    let point = vec![vec![2.0, 0.5], vec![-0.5, 3.0]];
    let point_sigma = spectral_norm_power_iteration(&point, 100, 1e-12).spectral_norm;
    assert!(
        point_sigma <= interval_result.upper + 1e-6,
        "point sigma {point_sigma} should be <= interval upper {}",
        interval_result.upper
    );
}

#[test]
fn test_interval_spectral_norm_empty() {
    let matrix: Vec<Vec<Interval>> = vec![];
    let result = spectral_norm_interval(&matrix, 50, 1e-10);
    assert!(result.lower.abs() < 1e-10);
    assert!(result.upper.abs() < 1e-10);
}

#[test]
fn test_interval_spectral_norm_upper_ge_lower() {
    let matrix = vec![
        vec![Interval::new(-2.0, 3.0), Interval::new(-1.0, 2.0)],
        vec![Interval::new(0.0, 1.0), Interval::new(-3.0, 4.0)],
    ];
    let result = spectral_norm_interval(&matrix, 100, 1e-10);
    assert!(result.upper >= result.lower - 1e-10, "upper >= lower");
}

// -- Submultiplicativity -----------------------------------------------------

#[test]
fn test_submultiplicativity_diagonal() {
    let a = vec![vec![2.0, 0.0], vec![0.0, 3.0]];
    let b = vec![vec![4.0, 0.0], vec![0.0, 5.0]];
    let result = verify_submultiplicativity(&a, &b, 100, 1e-10);
    assert!(
        result.is_ok(),
        "submultiplicativity should hold for diagonal: {:?}",
        result.err()
    );
    let (sa, sb, sab) = result.unwrap();
    assert!((sa - 3.0).abs() < 1e-6);
    assert!((sb - 5.0).abs() < 1e-6);
    assert!(sab <= sa * sb + 1e-6);
}

#[test]
fn test_submultiplicativity_general() {
    let a = vec![vec![1.0, 2.0], vec![3.0, 4.0]];
    let b = vec![vec![5.0, 6.0], vec![7.0, 8.0]];
    assert!(verify_submultiplicativity(&a, &b, 100, 1e-10).is_ok());
}

#[test]
fn test_submultiplicativity_dimension_mismatch() {
    let a = vec![vec![1.0, 2.0, 3.0]];
    let b = vec![vec![1.0], vec![2.0]]; // 2x1 but A is 1x3
    assert!(verify_submultiplicativity(&a, &b, 50, 1e-10).is_err());
}

#[test]
fn test_submultiplicativity_rectangular() {
    let a = vec![vec![1.0, 0.0, 2.0], vec![0.0, 3.0, 0.0]];
    let b = vec![vec![1.0, 0.0], vec![0.0, 1.0], vec![1.0, 1.0]];
    assert!(verify_submultiplicativity(&a, &b, 100, 1e-10).is_ok());
}

#[test]
fn test_submultiplicativity_empty() {
    let a: Vec<Vec<f64>> = vec![];
    let b: Vec<Vec<f64>> = vec![];
    assert!(verify_submultiplicativity(&a, &b, 50, 1e-10).is_ok());
}

// -- Integration: consistency with lipschitz_concrete ------------------------

#[test]
fn test_spectral_norm_matches_power_iteration_in_lipschitz_concrete() {
    use super::lipschitz_concrete::power_iteration as legacy_power_iteration;
    let matrix = vec![vec![1.0, 2.0], vec![3.0, 4.0]];
    let refs: Vec<&[f64]> = matrix.iter().map(|r| r.as_slice()).collect();
    let legacy_sigma = legacy_power_iteration(&refs, 100);
    let new_result = spectral_norm_power_iteration(&matrix, 100, 1e-12);
    assert!(
        (legacy_sigma - new_result.spectral_norm).abs() < 1e-6,
        "legacy {} vs new {}",
        legacy_sigma,
        new_result.spectral_norm
    );
}

#[test]
fn test_negative_entries_spectral_norm() {
    let matrix = vec![vec![-3.0, 0.0], vec![0.0, 2.0]];
    let result = spectral_norm_power_iteration(&matrix, 100, 1e-10);
    assert!(
        (result.spectral_norm - 3.0).abs() < 1e-6,
        "diag(-3,2) spectral norm should be 3.0, got {}",
        result.spectral_norm
    );
}

#[test]
fn test_spectral_norm_scaling_property() {
    // sigma_max(c*W) = |c| * sigma_max(W)
    let matrix = vec![vec![1.0, 2.0], vec![3.0, 4.0]];
    let sigma_w = spectral_norm_power_iteration(&matrix, 100, 1e-12).spectral_norm;
    let scaled: Vec<Vec<f64>> = matrix
        .iter()
        .map(|row| row.iter().map(|x| x * 3.0).collect())
        .collect();
    let sigma_3w = spectral_norm_power_iteration(&scaled, 100, 1e-12).spectral_norm;
    assert!(
        (sigma_3w - 3.0 * sigma_w).abs() < 1e-4,
        "sigma(3W)={sigma_3w} should equal 3*sigma(W)={}",
        3.0 * sigma_w
    );
}
