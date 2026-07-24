// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for cert_expr_builder: Farkas certificate to clean Expr conversion.

use super::*;
use crate::nn_verify::certificate::farkas_bridge::{build_simple_box_cert, ExternalFarkasCert};

/// Build a simple 2-variable identity Farkas certificate.
fn simple_2var_cert() -> ExternalFarkasCert {
    build_simple_box_cert(2, &[-1.0, -2.0], &[1.0, 2.0], &[-1.0, -2.0], &[1.0, 2.0])
}

/// Build a multi-constraint certificate (3 dims, different bounds).
fn multi_constraint_cert() -> ExternalFarkasCert {
    build_simple_box_cert(
        3,
        &[-1.0, -1.0, -1.0],
        &[1.0, 1.0, 1.0],
        &[-2.0, -2.0, -2.0],
        &[2.0, 2.0, 2.0],
    )
}

/// Build a single-variable cert with specific bounds.
fn single_var_cert() -> ExternalFarkasCert {
    build_simple_box_cert(1, &[0.0], &[1.0], &[0.0], &[1.0])
}

#[test]
fn test_farkas_cert_to_expr_simple_2var() {
    let cert = simple_2var_cert();
    let result = farkas_cert_to_expr(&cert).expect("should build expr for 2-var cert");
    assert_eq!(result.input_dim, 2);
    assert_eq!(result.output_dim, 2);
    assert_eq!(result.num_input_constraints, 4); // 2 dims * 2 rows per dim
    assert_eq!(result.num_output_constraints, 4);
    assert!(
        result.prop_type.is_pi(),
        "prop_type should be a pi/forall type"
    );
}

#[test]
fn test_farkas_cert_to_expr_multi_constraint() {
    let cert = multi_constraint_cert();
    let result = farkas_cert_to_expr(&cert).expect("should build expr for multi-constraint cert");
    assert_eq!(result.input_dim, 3);
    assert_eq!(result.output_dim, 3);
    assert_eq!(result.num_input_constraints, 6);
    assert_eq!(result.num_output_constraints, 6);
    assert!(result.prop_type.is_pi());
    assert!(result.proof_term.is_lam(), "proof_term should be a lambda");
}

#[test]
fn test_farkas_cert_to_expr_single_var() {
    let cert = single_var_cert();
    let result = farkas_cert_to_expr(&cert).expect("should build expr for single-var cert");
    assert_eq!(result.input_dim, 1);
    assert_eq!(result.num_input_constraints, 2);
    assert_eq!(result.num_output_constraints, 2);
}

#[test]
fn test_farkas_cert_to_expr_zero_dim_errors() {
    let cert = ExternalFarkasCert {
        multipliers: vec![],
        input_matrix: vec![],
        input_bounds: vec![],
        output_matrix: vec![],
        output_bounds: vec![],
        input_dim: 0,
        output_dim: 0,
    };
    let result = farkas_cert_to_expr(&cert);
    assert!(result.is_err());
    match result {
        Err(CertExprError::EmptyCertificate { .. }) => {}
        other => panic!("expected EmptyCertificate, got {other:?}"),
    }
}

#[test]
fn test_f64_to_rational_integers() {
    assert_eq!(f64_to_rational(0.0), (0, 1));
    assert_eq!(f64_to_rational(1.0), (1, 1));
    assert_eq!(f64_to_rational(-1.0), (-1, 1));
    assert_eq!(f64_to_rational(42.0), (42, 1));
}

#[test]
fn test_f64_to_rational_simple_fractions() {
    let (num, den) = f64_to_rational(0.5);
    let approx = num as f64 / den as f64;
    assert!((approx - 0.5).abs() < 1e-9, "0.5 -> {num}/{den} = {approx}");

    let (num, den) = f64_to_rational(0.25);
    let approx = num as f64 / den as f64;
    assert!(
        (approx - 0.25).abs() < 1e-9,
        "0.25 -> {num}/{den} = {approx}"
    );
}

#[test]
fn test_f64_to_rational_negative() {
    let (num, den) = f64_to_rational(-0.5);
    let approx = num as f64 / den as f64;
    assert!(
        (approx - (-0.5)).abs() < 1e-9,
        "-0.5 -> {num}/{den} = {approx}"
    );
}

#[test]
fn test_mk_real_of_rat_produces_app() {
    let expr = mk_real_of_rat(1, 2);
    assert!(expr.is_app(), "Real.ofRat should produce an App node");
}

#[test]
fn test_conjoin_props_empty() {
    let result = conjoin_props(&[]);
    assert!(result.is_const(), "empty conjunction should be True");
}

#[test]
fn test_conjoin_props_single() {
    let p = Expr::const_str("P");
    let result = conjoin_props(&[p]);
    assert!(result.is_const());
}

#[test]
fn test_conjoin_props_pair() {
    let p = Expr::const_str("P");
    let q = Expr::const_str("Q");
    let result = conjoin_props(&[p, q]);
    assert!(result.is_app(), "AndType P Q should be an App node");
}

#[test]
fn test_build_list_real_empty() {
    let list = build_list_real(&[]);
    assert!(list.is_app(), "ListType.nil Real should be an App node");
}

#[test]
fn test_build_list_real_single() {
    let elem = mk_real_of_rat(1, 1);
    let list = build_list_real(&[elem]);
    assert!(list.is_app(), "ListType.cons should be an App node");
}

#[test]
fn test_full_pipeline_json_to_expr() {
    // Integration test: parse JSON -> Farkas chain -> Expr proof terms.
    let json = r#"{
        "network_id": "integration_test",
        "num_layers": 1,
        "layer_certs": [
            {
                "layer_index": 0,
                "layer_type": "linear",
                "multipliers": [1.0, 1.0, 1.0, 1.0],
                "input_bounds": [[-1.0, 1.0], [-1.0, 1.0]],
                "output_bounds": [[-1.0, 1.0], [-1.0, 1.0]]
            }
        ],
        "input_spec": { "center": [0.0, 0.0], "epsilon": 1.0 },
        "output_property": {
            "property_type": "robust_classification",
            "true_class": 0,
            "margin": 0.0
        }
    }"#;

    let (_cert, chain) = crate::nn_verify::cert_json_parser::parse_json_to_farkas_chain(json)
        .expect("should parse JSON");
    assert_eq!(chain.len(), 1);

    let expr_result = farkas_cert_to_expr(&chain[0]).expect("should build expr from Farkas cert");
    assert_eq!(expr_result.input_dim, 2);
    assert!(expr_result.prop_type.is_pi());
    assert!(expr_result.proof_term.is_lam());
}
