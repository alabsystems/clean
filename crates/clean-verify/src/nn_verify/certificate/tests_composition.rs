// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Dedicated tests for certificate composition (`composition.rs`).

use super::composition::*;
use super::*;
use clean_elab::cert::external::{
    ConstraintKind, ExternalEntailmentCert, ExternalLinearConstraint, ExternalRational,
};
use std::collections::BTreeMap;

fn mk_c(var: &str, coeff: i64, kind: ConstraintKind, bound: i64) -> ExternalLinearConstraint {
    let mut coefficients = BTreeMap::new();
    coefficients.insert(var.to_string(), ExternalRational::from_int(coeff));
    ExternalLinearConstraint {
        kind,
        coefficients,
        constant: ExternalRational::from_int(bound),
    }
}

fn mk_c2(
    v1: &str,
    c1: i64,
    v2: &str,
    c2: i64,
    kind: ConstraintKind,
    b: i64,
) -> ExternalLinearConstraint {
    let mut coefficients = BTreeMap::new();
    coefficients.insert(v1.to_string(), ExternalRational::from_int(c1));
    coefficients.insert(v2.to_string(), ExternalRational::from_int(c2));
    ExternalLinearConstraint {
        kind,
        coefficients,
        constant: ExternalRational::from_int(b),
    }
}

fn mk_empty(kind: ConstraintKind, bound: i64) -> ExternalLinearConstraint {
    ExternalLinearConstraint {
        kind,
        coefficients: BTreeMap::new(),
        constant: ExternalRational::from_int(bound),
    }
}

fn mk_ent(
    p: Vec<ExternalLinearConstraint>,
    m: Vec<ExternalRational>,
    c: ExternalLinearConstraint,
) -> ExternalEntailmentCert {
    ExternalEntailmentCert {
        version: "1.0".to_string(),
        premises: p,
        multipliers: m,
        conclusion: c,
    }
}

// -- compose_entailment_certs: happy path --
#[test]
fn test_compose_simple_chain_x_le_5_to_8() {
    let a = build_simple_entailment("x", 1, 5, 6);
    let b = build_simple_entailment("x", 1, 6, 8);
    let c = compose_entailment_certs(&a, &b).expect("should compose");
    assert_eq!(
        c.certificate.conclusion.constant,
        ExternalRational::from_int(8)
    );
    assert_eq!(c.certificate.premises.len(), 1);
    assert_eq!(
        c.certificate.premises[0].constant,
        ExternalRational::from_int(5)
    );
}
#[test]
fn test_compose_chain_different_bounds() {
    let c = compose_entailment_certs(
        &build_simple_entailment("x", 1, 3, 10),
        &build_simple_entailment("x", 1, 10, 20),
    )
    .expect("should compose");
    assert_eq!(
        c.certificate.conclusion.constant,
        ExternalRational::from_int(20)
    );
    assert_eq!(
        c.certificate.premises[0].constant,
        ExternalRational::from_int(3)
    );
}
#[test]
fn test_compose_replaced_premise_index_is_zero() {
    let c = compose_entailment_certs(
        &build_simple_entailment("x", 1, 1, 5),
        &build_simple_entailment("x", 1, 5, 9),
    )
    .expect("should compose");
    assert_eq!(c.replaced_premise_index, 0);
}
#[test]
fn test_compose_spliced_premise_count_single() {
    let c = compose_entailment_certs(
        &build_simple_entailment("x", 1, 2, 4),
        &build_simple_entailment("x", 1, 4, 6),
    )
    .expect("should compose");
    assert_eq!(c.spliced_premise_count, 1);
}
#[test]
fn test_compose_conclusion_is_cert_b_conclusion() {
    let b = build_simple_entailment("x", 1, 10, 100);
    let c = compose_entailment_certs(&build_simple_entailment("x", 1, 0, 10), &b)
        .expect("should compose");
    assert_eq!(c.certificate.conclusion.constant, b.conclusion.constant);
    assert_eq!(c.certificate.conclusion.kind, b.conclusion.kind);
}
#[test]
fn test_compose_premises_are_cert_a_premises() {
    let a = build_simple_entailment("x", 1, 7, 15);
    let c = compose_entailment_certs(&a, &build_simple_entailment("x", 1, 15, 30))
        .expect("should compose");
    assert_eq!(c.certificate.premises.len(), a.premises.len());
    assert_eq!(c.certificate.premises[0].constant, a.premises[0].constant);
}

#[test]
fn test_compose_version_is_1_0() {
    let c = compose_entailment_certs(
        &build_simple_entailment("x", 1, 0, 1),
        &build_simple_entailment("x", 1, 1, 2),
    )
    .expect("should compose");
    assert_eq!(c.certificate.version, "1.0");
}

#[test]
fn test_compose_tight_bounds() {
    let c = compose_entailment_certs(
        &build_simple_entailment("x", 1, 5, 5),
        &build_simple_entailment("x", 1, 5, 10),
    )
    .expect("tight bound");
    assert_eq!(
        c.certificate.conclusion.constant,
        ExternalRational::from_int(10)
    );
}

#[test]
fn test_compose_wide_gap_bounds() {
    let c = compose_entailment_certs(
        &build_simple_entailment("x", 1, 0, 500),
        &build_simple_entailment("x", 1, 500, 1000),
    )
    .expect("wide gap");
    assert_eq!(
        c.certificate.conclusion.constant,
        ExternalRational::from_int(1000)
    );
    assert_eq!(
        c.certificate.premises[0].constant,
        ExternalRational::from_int(0)
    );
}

#[test]
fn test_compose_multipliers_length_matches_premises() {
    let c = compose_entailment_certs(
        &build_simple_entailment("x", 1, 1, 3),
        &build_simple_entailment("x", 1, 3, 5),
    )
    .expect("should compose");
    assert_eq!(
        c.certificate.multipliers.len(),
        c.certificate.premises.len()
    );
}

// -- compose_entailment_certs: error paths --
#[test]
fn test_compose_no_match_different_variable() {
    let err = compose_entailment_certs(
        &build_simple_entailment("x", 1, 5, 6),
        &build_simple_entailment("y", 1, 6, 8),
    )
    .expect_err("different vars");
    assert!(matches!(err, CompositionError::NoMatchingPremise));
}

#[test]
fn test_compose_no_match_different_constant() {
    let err = compose_entailment_certs(
        &build_simple_entailment("x", 1, 5, 6),
        &build_simple_entailment("x", 1, 7, 10),
    )
    .expect_err("different constant");
    assert!(matches!(err, CompositionError::NoMatchingPremise));
}

#[test]
fn test_compose_no_match_different_coefficient() {
    let err = compose_entailment_certs(
        &build_simple_entailment("x", 1, 5, 6),
        &build_simple_entailment("x", 2, 6, 12),
    )
    .expect_err("different coeff");
    assert!(matches!(err, CompositionError::NoMatchingPremise));
}

#[test]
fn test_compose_no_match_different_constraint_kind() {
    let a = mk_ent(
        vec![mk_c("x", 1, ConstraintKind::Le, 5)],
        vec![ExternalRational::ONE],
        mk_c("x", 1, ConstraintKind::Le, 6),
    );
    let b = mk_ent(
        vec![mk_c("x", -1, ConstraintKind::Ge, -6)],
        vec![ExternalRational::ONE],
        mk_c("x", -1, ConstraintKind::Ge, -10),
    );
    let err = compose_entailment_certs(&a, &b).expect_err("different kind");
    assert!(matches!(err, CompositionError::NoMatchingPremise));
}

#[test]
fn test_compose_no_match_extra_variable() {
    let a = build_simple_entailment("x", 1, 3, 6);
    let b = mk_ent(
        vec![mk_c2("x", 1, "y", 1, ConstraintKind::Le, 6)],
        vec![ExternalRational::ONE],
        mk_c2("x", 1, "y", 1, ConstraintKind::Le, 10),
    );
    let err = compose_entailment_certs(&a, &b).expect_err("extra variable");
    assert!(matches!(err, CompositionError::NoMatchingPremise));
}

#[test]
fn test_compose_no_match_reversed_direction() {
    let err = compose_entailment_certs(
        &build_simple_entailment("x", 1, 10, 20),
        &build_simple_entailment("x", 1, 5, 10),
    )
    .expect_err("reversed");
    assert!(matches!(err, CompositionError::NoMatchingPremise));
}

#[test]
fn test_compose_no_match_negative_vs_positive_coeff() {
    let err = compose_entailment_certs(
        &build_simple_entailment("x", 1, 5, 6),
        &build_simple_entailment("x", -1, 6, 10),
    )
    .expect_err("neg vs pos coeff");
    assert!(matches!(err, CompositionError::NoMatchingPremise));
}

#[test]
fn test_compose_no_match_empty_vs_nonempty_coefficients() {
    let a = mk_ent(
        vec![mk_empty(ConstraintKind::Le, 0)],
        vec![ExternalRational::ONE],
        mk_empty(ConstraintKind::Le, 5),
    );
    let err = compose_entailment_certs(&a, &build_simple_entailment("x", 1, 5, 10))
        .expect_err("empty vs nonempty");
    assert!(matches!(err, CompositionError::NoMatchingPremise));
}

#[test]
fn test_compose_error_display_no_matching_premise() {
    let msg = format!("{}", CompositionError::NoMatchingPremise);
    assert!(msg.contains("no matching premise"));
}

#[test]
fn test_compose_error_display_dimension_mismatch() {
    let msg = format!(
        "{}",
        CompositionError::DimensionMismatch("test".to_string())
    );
    assert!(msg.contains("dimension mismatch"));
    assert!(msg.contains("test"));
}

// -- Constraint matching (indirect) --
#[test]
fn test_match_exact_single_var_le() {
    assert!(compose_entailment_certs(
        &build_simple_entailment("x", 1, 0, 5),
        &build_simple_entailment("x", 1, 5, 10),
    )
    .is_ok());
}

#[test]
fn test_match_fails_different_kind_le_vs_ge() {
    let a = mk_ent(
        vec![mk_c("x", 1, ConstraintKind::Le, 3)],
        vec![ExternalRational::ONE],
        mk_c("x", 1, ConstraintKind::Le, 5),
    );
    let b = mk_ent(
        vec![mk_c("x", 1, ConstraintKind::Ge, 5)],
        vec![ExternalRational::ONE],
        mk_c("x", 1, ConstraintKind::Ge, 3),
    );
    assert!(compose_entailment_certs(&a, &b).is_err());
}

#[test]
fn test_match_fails_different_constant_value() {
    assert!(compose_entailment_certs(
        &build_simple_entailment("x", 1, 0, 5),
        &build_simple_entailment("x", 1, 6, 10),
    )
    .is_err());
}

#[test]
fn test_match_fails_different_coefficient_count() {
    let b = mk_ent(
        vec![mk_c2("x", 1, "y", 1, ConstraintKind::Le, 5)],
        vec![ExternalRational::ONE],
        mk_c2("x", 1, "y", 1, ConstraintKind::Le, 10),
    );
    assert!(compose_entailment_certs(&build_simple_entailment("x", 1, 0, 5), &b).is_err());
}

#[test]
fn test_match_fails_different_variable_name() {
    assert!(compose_entailment_certs(
        &build_simple_entailment("x", 1, 0, 5),
        &build_simple_entailment("y", 1, 5, 10),
    )
    .is_err());
}

#[test]
fn test_match_fails_different_coefficient_value() {
    assert!(compose_entailment_certs(
        &build_simple_entailment("x", 1, 0, 5),
        &build_simple_entailment("x", 3, 5, 15),
    )
    .is_err());
}

#[test]
fn test_match_empty_coefficients_both_sides() {
    let a = mk_ent(
        vec![mk_empty(ConstraintKind::Le, 0)],
        vec![ExternalRational::ONE],
        mk_empty(ConstraintKind::Le, 5),
    );
    let b = mk_ent(
        vec![mk_empty(ConstraintKind::Le, 5)],
        vec![ExternalRational::ONE],
        mk_empty(ConstraintKind::Le, 10),
    );
    assert!(compose_entailment_certs(&a, &b).is_ok());
}

#[test]
fn test_match_two_var_exact() {
    let a = mk_ent(
        vec![mk_c2("a", 2, "b", 3, ConstraintKind::Le, 10)],
        vec![ExternalRational::ONE],
        mk_c2("a", 2, "b", 3, ConstraintKind::Le, 20),
    );
    let b = mk_ent(
        vec![mk_c2("a", 2, "b", 3, ConstraintKind::Le, 20)],
        vec![ExternalRational::ONE],
        mk_c2("a", 2, "b", 3, ConstraintKind::Le, 30),
    );
    assert!(compose_entailment_certs(&a, &b).is_ok());
}

#[test]
fn test_match_two_var_one_coeff_differs() {
    let a = mk_ent(
        vec![mk_c2("a", 2, "b", 3, ConstraintKind::Le, 10)],
        vec![ExternalRational::ONE],
        mk_c2("a", 2, "b", 3, ConstraintKind::Le, 20),
    );
    let b = mk_ent(
        vec![mk_c2("a", 2, "b", 4, ConstraintKind::Le, 20)],
        vec![ExternalRational::ONE],
        mk_c2("a", 2, "b", 4, ConstraintKind::Le, 30),
    );
    assert!(compose_entailment_certs(&a, &b).is_err());
}

#[test]
fn test_match_multiple_coefficients_all_matching() {
    let a = mk_ent(
        vec![mk_c2("x", 1, "y", 2, ConstraintKind::Le, 5)],
        vec![ExternalRational::ONE],
        mk_c2("x", 1, "y", 2, ConstraintKind::Le, 10),
    );
    let b = mk_ent(
        vec![mk_c2("x", 1, "y", 2, ConstraintKind::Le, 10)],
        vec![ExternalRational::ONE],
        mk_c2("x", 1, "y", 2, ConstraintKind::Le, 20),
    );
    assert!(compose_entailment_certs(&a, &b).is_ok());
}

// -- ComposedCert metadata --
#[test]
fn test_metadata_replaced_index_zero() {
    let c = compose_entailment_certs(
        &build_simple_entailment("x", 1, 0, 5),
        &build_simple_entailment("x", 1, 5, 10),
    )
    .expect("compose");
    assert_eq!(c.replaced_premise_index, 0);
}

#[test]
fn test_metadata_spliced_count_equals_cert_a_premises() {
    let a = build_simple_entailment("x", 1, 0, 5);
    let c = compose_entailment_certs(&a, &build_simple_entailment("x", 1, 5, 10)).expect("compose");
    assert_eq!(c.spliced_premise_count, a.premises.len());
}

#[test]
fn test_metadata_certificate_passes_independent_verification() {
    let c = compose_entailment_certs(
        &build_simple_entailment("x", 1, 0, 5),
        &build_simple_entailment("x", 1, 5, 10),
    )
    .expect("compose");
    let result = clean_elab::cert::external::verify_entailment_certificate(&c.certificate);
    assert!(result.is_ok(), "composed cert should verify independently");
}

#[test]
fn test_metadata_debug_impl() {
    let c = compose_entailment_certs(
        &build_simple_entailment("x", 1, 0, 5),
        &build_simple_entailment("x", 1, 5, 10),
    )
    .expect("compose");
    let debug = format!("{c:?}");
    assert!(debug.contains("ComposedCert"));
    assert!(debug.contains("replaced_premise_index"));
}

#[test]
fn test_metadata_clone() {
    let c = compose_entailment_certs(
        &build_simple_entailment("x", 1, 0, 5),
        &build_simple_entailment("x", 1, 5, 10),
    )
    .expect("compose");
    let cl = c.clone();
    assert_eq!(cl.replaced_premise_index, c.replaced_premise_index);
    assert_eq!(cl.spliced_premise_count, c.spliced_premise_count);
}

// -- Edge cases --
#[test]
fn test_self_composition_same_structure() {
    let cert = build_simple_entailment("x", 1, 5, 5);
    let c = compose_entailment_certs(&cert, &cert).expect("self-compose");
    assert_eq!(
        c.certificate.conclusion.constant,
        ExternalRational::from_int(5)
    );
    assert_eq!(c.replaced_premise_index, 0);
}

#[test]
fn test_compose_large_bounds() {
    let c = compose_entailment_certs(
        &build_simple_entailment("x", 1, 0, 1_000_000),
        &build_simple_entailment("x", 1, 1_000_000, 2_000_000),
    )
    .expect("large bounds");
    assert_eq!(
        c.certificate.conclusion.constant,
        ExternalRational::from_int(2_000_000)
    );
}

#[test]
fn test_compose_zero_coefficient_empty_constraints() {
    let a = mk_ent(
        vec![mk_empty(ConstraintKind::Le, 0)],
        vec![ExternalRational::ONE],
        mk_empty(ConstraintKind::Le, 5),
    );
    let b = mk_ent(
        vec![mk_empty(ConstraintKind::Le, 5)],
        vec![ExternalRational::ONE],
        mk_empty(ConstraintKind::Le, 10),
    );
    let c = compose_entailment_certs(&a, &b).expect("zero coefficients");
    assert_eq!(
        c.certificate.conclusion.constant,
        ExternalRational::from_int(10)
    );
}

#[test]
fn test_compose_negative_coefficient() {
    let c = compose_entailment_certs(
        &build_simple_entailment("x", -1, -3, -1),
        &build_simple_entailment("x", -1, -1, 0),
    )
    .expect("negative coeff");
    assert_eq!(
        c.certificate.conclusion.constant,
        ExternalRational::from_int(0)
    );
}

#[test]
fn test_compose_negative_bounds() {
    let c = compose_entailment_certs(
        &build_simple_entailment("x", 1, -10, -5),
        &build_simple_entailment("x", 1, -5, 0),
    )
    .expect("negative bounds");
    assert_eq!(
        c.certificate.premises[0].constant,
        ExternalRational::from_int(-10)
    );
    assert_eq!(
        c.certificate.conclusion.constant,
        ExternalRational::from_int(0)
    );
}

#[test]
fn test_compose_three_step_chain() {
    let ab = compose_entailment_certs(
        &build_simple_entailment("x", 1, 2, 5),
        &build_simple_entailment("x", 1, 5, 10),
    )
    .expect("a+b");
    let abc = compose_entailment_certs(&ab.certificate, &build_simple_entailment("x", 1, 10, 20))
        .expect("ab+c");
    assert_eq!(
        abc.certificate.conclusion.constant,
        ExternalRational::from_int(20)
    );
    assert_eq!(
        abc.certificate.premises[0].constant,
        ExternalRational::from_int(2)
    );
}

#[test]
fn test_build_simple_entailment_helper_structure() {
    let cert = build_simple_entailment("y", 3, 10, 20);
    assert_eq!(cert.version, "1.0");
    assert_eq!(cert.premises.len(), 1);
    assert_eq!(cert.multipliers.len(), 1);
    assert_eq!(cert.multipliers[0], ExternalRational::ONE);
    assert_eq!(cert.premises[0].kind, ConstraintKind::Le);
    assert_eq!(cert.premises[0].constant, ExternalRational::from_int(10));
    assert_eq!(cert.conclusion.constant, ExternalRational::from_int(20));
    assert_eq!(
        *cert.conclusion.coefficients.get("y").expect("y"),
        ExternalRational::from_int(3)
    );
}

#[test]
fn test_compose_preserves_variable_name() {
    let c = compose_entailment_certs(
        &build_simple_entailment("temperature", 1, 0, 100),
        &build_simple_entailment("temperature", 1, 100, 200),
    )
    .expect("named var");
    assert!(c
        .certificate
        .conclusion
        .coefficients
        .contains_key("temperature"));
    assert!(c.certificate.premises[0]
        .coefficients
        .contains_key("temperature"));
}

#[test]
fn test_compose_multipliers_all_non_negative() {
    let c = compose_entailment_certs(
        &build_simple_entailment("x", 1, 0, 5),
        &build_simple_entailment("x", 1, 5, 10),
    )
    .expect("compose");
    for m in &c.certificate.multipliers {
        assert!(!m.is_negative(), "multiplier should be non-negative");
    }
}

#[test]
fn test_compose_error_non_exhaustive_match() {
    let err = CompositionError::NoMatchingPremise;
    match err {
        CompositionError::NoMatchingPremise => {}
        CompositionError::DimensionMismatch(_) => panic!("wrong variant"),
        CompositionError::VerificationFailed(_) => panic!("wrong variant"),
        CompositionError::ComposedVerificationFailed(_) => panic!("wrong variant"),
        _ => {} // non_exhaustive wildcard
    }
}
