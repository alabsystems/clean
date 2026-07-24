// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for PAC-to-Proof certification.

use super::certification::*;

// ---------------------------------------------------------------------------
// LipschitzBound tests
// ---------------------------------------------------------------------------

#[test]
fn test_lipschitz_bound_valid() {
    let lip = LipschitzBound::new(2.5).expect("should accept positive constant");
    assert!((lip.constant() - 2.5).abs() < f64::EPSILON);
}

#[test]
fn test_lipschitz_bound_zero_rejected() {
    let err = LipschitzBound::new(0.0).unwrap_err();
    assert!(matches!(err, CertificationError::NonPositiveLipschitz(_)));
}

#[test]
fn test_lipschitz_bound_negative_rejected() {
    let err = LipschitzBound::new(-1.0).unwrap_err();
    assert!(matches!(err, CertificationError::NonPositiveLipschitz(_)));
}

#[test]
fn test_lipschitz_bound_nan_rejected() {
    let err = LipschitzBound::new(f64::NAN).unwrap_err();
    assert!(matches!(err, CertificationError::NonPositiveLipschitz(_)));
}

#[test]
fn test_lipschitz_bound_inf_rejected() {
    let err = LipschitzBound::new(f64::INFINITY).unwrap_err();
    assert!(matches!(err, CertificationError::NonPositiveLipschitz(_)));
}

// ---------------------------------------------------------------------------
// HessianBound tests
// ---------------------------------------------------------------------------

#[test]
fn test_hessian_bound_valid() {
    let hess = HessianBound::new(3.0).expect("should accept positive bound");
    assert!((hess.bound() - 3.0).abs() < f64::EPSILON);
}

#[test]
fn test_hessian_bound_zero_valid() {
    let hess = HessianBound::new(0.0).expect("should accept zero (linear network)");
    assert!((hess.bound()).abs() < f64::EPSILON);
}

#[test]
fn test_hessian_bound_negative_rejected() {
    let err = HessianBound::new(-0.5).unwrap_err();
    assert!(matches!(err, CertificationError::NegativeHessian(_)));
}

#[test]
fn test_hessian_bound_nan_rejected() {
    let err = HessianBound::new(f64::NAN).unwrap_err();
    assert!(matches!(err, CertificationError::NegativeHessian(_)));
}

// ---------------------------------------------------------------------------
// First-order certification tests
// ---------------------------------------------------------------------------

#[test]
fn test_first_order_basic_radius() {
    // f(x_adv) = 0.8, threshold = 0.5, L = 3.0
    // r = (0.8 - 0.5) / 3.0 = 0.1
    let region = certify_pgd_result(3.0, 0.8, 0.5).expect("should certify valid PGD result");

    assert!((region.radius() - 0.1).abs() < 1e-10);
    assert!((region.margin() - 0.3).abs() < 1e-10);
    assert_eq!(region.mode(), CertificationMode::FirstOrder);
    assert!(region.hessian().is_none());
    assert!(region.gradient_norm().is_none());
}

#[test]
fn test_first_order_large_margin() {
    // Large margin → large radius.
    // f(x_adv) = 10.0, threshold = 1.0, L = 2.0
    // r = (10.0 - 1.0) / 2.0 = 4.5
    let region = certify_pgd_result(2.0, 10.0, 1.0).expect("should certify large-margin result");

    assert!((region.radius() - 4.5).abs() < 1e-10);
}

#[test]
fn test_first_order_small_lipschitz() {
    // Small Lipschitz constant → large radius.
    // f(x_adv) = 0.6, threshold = 0.5, L = 0.01
    // r = 0.1 / 0.01 = 10.0
    let region = certify_pgd_result(0.01, 0.6, 0.5).expect("should certify with small Lipschitz");

    assert!((region.radius() - 10.0).abs() < 1e-10);
}

#[test]
fn test_first_order_output_below_threshold_rejected() {
    let err = certify_pgd_result(2.0, 0.3, 0.5).unwrap_err();
    assert!(matches!(
        err,
        CertificationError::OutputBelowThreshold { .. }
    ));
}

#[test]
fn test_first_order_output_equals_threshold_rejected() {
    let err = certify_pgd_result(2.0, 0.5, 0.5).unwrap_err();
    assert!(matches!(
        err,
        CertificationError::OutputBelowThreshold { .. }
    ));
}

// ---------------------------------------------------------------------------
// Second-order certification tests
// ---------------------------------------------------------------------------

#[test]
fn test_second_order_basic_radius() {
    // f(x_adv) = 1.0, threshold = 0.5, L = 5.0, H = 2.0, ||grad|| = 0.1
    // margin = 0.5
    // First-order: r1 = 0.5 / 5.0 = 0.1
    // Second-order: r2 = (-0.1 + sqrt(0.01 + 2*2*0.5)) / 2 = (-0.1 + sqrt(2.01)) / 2
    //   sqrt(2.01) ~= 1.4177, r2 ~= (-0.1 + 1.4177) / 2 ~= 0.6589
    // Best = max(0.1, 0.6589) = 0.6589
    let lip = LipschitzBound::new(5.0).unwrap();
    let hess = HessianBound::new(2.0).unwrap();
    let certifier = PacProofCertifier::second_order(lip, hess);
    let region = certifier
        .certify(1.0, 0.5, Some(0.1))
        .expect("should certify with second-order");

    // Second-order radius should be significantly larger than first-order
    // when gradient is small.
    let first_order_r = 0.5 / 5.0;
    assert!(region.radius() > first_order_r + 0.1);
    assert_eq!(region.mode(), CertificationMode::SecondOrder);
    assert!(region.hessian().is_some());
    assert!(region.gradient_norm().is_some());
}

#[test]
fn test_second_order_zero_gradient_max_radius() {
    // When gradient is exactly zero, the quadratic gives maximum radius:
    // r = sqrt(2 * margin / H) = sqrt(2 * 0.5 / 2.0) = sqrt(0.5) ~= 0.707
    let lip = LipschitzBound::new(5.0).unwrap();
    let hess = HessianBound::new(2.0).unwrap();
    let certifier = PacProofCertifier::second_order(lip, hess);
    let region = certifier
        .certify(1.0, 0.5, Some(0.0))
        .expect("should certify with zero gradient");

    let expected_r2 = (2.0 * 0.5 / 2.0_f64).sqrt(); // sqrt(0.5)
    let first_order_r = 0.5 / 5.0;

    // Second-order should dominate when gradient is zero and H is moderate.
    assert!(region.radius() > first_order_r);
    // The actual radius should be close to the second-order computation.
    assert!(
        (region.radius() - expected_r2).abs() < 1e-10
            || (region.radius() - first_order_r).abs() < 1e-10
    );
}

#[test]
fn test_second_order_falls_back_to_first_order_when_gradient_large() {
    // Large gradient makes second-order radius small; first-order wins.
    // L = 1.0, margin = 1.0, H = 0.1, ||grad|| = 10.0
    // First-order: r1 = 1.0 / 1.0 = 1.0
    // Second-order: r2 = (-10 + sqrt(100 + 0.2)) / 0.1
    //   sqrt(100.2) ~= 10.01, r2 ~= (-10 + 10.01) / 0.1 ~= 0.1
    // Best = max(1.0, 0.1) = 1.0, so first-order wins.
    let lip = LipschitzBound::new(1.0).unwrap();
    let hess = HessianBound::new(0.1).unwrap();
    let certifier = PacProofCertifier::second_order(lip, hess);
    let region = certifier
        .certify(2.0, 1.0, Some(10.0))
        .expect("should certify");

    assert!((region.radius() - 1.0).abs() < 1e-6);
    assert_eq!(region.mode(), CertificationMode::FirstOrder);
}

#[test]
fn test_second_order_negative_gradient_rejected() {
    let lip = LipschitzBound::new(2.0).unwrap();
    let hess = HessianBound::new(1.0).unwrap();
    let certifier = PacProofCertifier::second_order(lip, hess);
    let err = certifier.certify(1.0, 0.5, Some(-0.1)).unwrap_err();
    assert!(matches!(err, CertificationError::NegativeGradientNorm(_)));
}

#[test]
fn test_second_order_without_gradient_uses_first_order() {
    // If no gradient norm is provided, second-order certifier falls back.
    let lip = LipschitzBound::new(2.0).unwrap();
    let hess = HessianBound::new(1.0).unwrap();
    let certifier = PacProofCertifier::second_order(lip, hess);
    let region = certifier
        .certify(1.0, 0.5, None)
        .expect("should fall back to first-order");

    assert_eq!(region.mode(), CertificationMode::FirstOrder);
    assert!((region.radius() - 0.25).abs() < 1e-10); // 0.5 / 2.0
}

#[test]
fn test_second_order_zero_hessian_uses_first_order() {
    // H = 0 → certifier uses first order (no curvature information).
    let lip = LipschitzBound::new(2.0).unwrap();
    let hess = HessianBound::new(0.0).unwrap();
    let certifier = PacProofCertifier::second_order(lip, hess);
    let region = certifier
        .certify(1.0, 0.5, Some(0.1))
        .expect("should use first-order for H=0");

    assert_eq!(region.mode(), CertificationMode::FirstOrder);
}

// ---------------------------------------------------------------------------
// CertifiedRegion verification tests
// ---------------------------------------------------------------------------

#[test]
fn test_verify_first_order_region() {
    let region = certify_pgd_result(3.0, 0.8, 0.5).expect("should produce valid region");
    assert!(verify_certified_region(&region));
}

#[test]
fn test_verify_second_order_region() {
    let lip = LipschitzBound::new(5.0).unwrap();
    let hess = HessianBound::new(2.0).unwrap();
    let certifier = PacProofCertifier::second_order(lip, hess);
    let region = certifier.certify(1.0, 0.5, Some(0.1)).unwrap();
    assert!(verify_certified_region(&region));
}

#[test]
fn test_verify_region_invariants_hold_for_many_parameters() {
    // Test a range of Lipschitz constants, margins, and Hessian bounds.
    let lipschitz_values = [0.1, 1.0, 5.0, 100.0];
    let margins = [0.01, 0.1, 1.0, 10.0];

    for &l in &lipschitz_values {
        for &m in &margins {
            let output = 1.0 + m;
            let threshold = 1.0;
            let region = certify_pgd_result(l, output, threshold).expect("should certify");
            assert!(
                verify_certified_region(&region),
                "failed for L={l}, margin={m}"
            );
        }
    }
}

// ---------------------------------------------------------------------------
// PacProofCertifier reuse tests
// ---------------------------------------------------------------------------

#[test]
fn test_certifier_reuse_across_examples() {
    let lip = LipschitzBound::new(2.0).unwrap();
    let certifier = PacProofCertifier::first_order(lip);

    // Different adversarial examples with same Lipschitz bound.
    let r1 = certifier.certify(0.8, 0.5, None).unwrap();
    let r2 = certifier.certify(1.2, 0.5, None).unwrap();
    let r3 = certifier.certify(0.6, 0.5, None).unwrap();

    // Larger margin → larger radius.
    assert!(r2.radius() > r1.radius());
    assert!(r1.radius() > r3.radius());

    // All should verify.
    assert!(verify_certified_region(&r1));
    assert!(verify_certified_region(&r2));
    assert!(verify_certified_region(&r3));
}

// ---------------------------------------------------------------------------
// Edge cases
// ---------------------------------------------------------------------------

#[test]
fn test_very_small_margin() {
    // Tiny margin → tiny radius, but should still be valid.
    let region = certify_pgd_result(1.0, 0.5 + 1e-12, 0.5).expect("should handle tiny margin");
    assert!(region.radius() > 0.0);
    assert!(region.radius() < 1e-10);
    assert!(verify_certified_region(&region));
}

#[test]
fn test_very_large_lipschitz() {
    // Large Lipschitz → tiny radius.
    let region = certify_pgd_result(1e10, 1.0, 0.5).expect("should handle large Lipschitz");
    assert!(region.radius() > 0.0);
    assert!(region.radius() < 1e-8);
    assert!(verify_certified_region(&region));
}

#[test]
fn test_margin_and_accessors() {
    let region = certify_pgd_result(4.0, 1.0, 0.6).unwrap();
    assert!((region.margin() - 0.4).abs() < 1e-10);
    assert!((region.adversarial_output() - 1.0).abs() < 1e-10);
    assert!((region.threshold() - 0.6).abs() < 1e-10);
    assert!((region.lipschitz() - 4.0).abs() < 1e-10);
}
