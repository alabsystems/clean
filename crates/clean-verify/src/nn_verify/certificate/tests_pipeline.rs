// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the verify-and-compose certificate pipeline.

use super::pipeline::*;

/// Build a JSON entailment cert: `var <= premise_bound => var <= conclusion_bound`.
fn make_cert_json(var: &str, premise_bound: i64, conclusion_bound: i64) -> String {
    format!(
        r#"{{
            "version": "1.0",
            "premises": [{{
                "type": "linear_constraint",
                "kind": "le",
                "coefficients": {{"{var}": "{coeff}"}},
                "constant": "{premise}"
            }}],
            "multipliers": ["1"],
            "conclusion": {{
                "type": "linear_constraint",
                "kind": "le",
                "coefficients": {{"{var}": "{coeff}"}},
                "constant": "{conclusion}"
            }}
        }}"#,
        var = var,
        coeff = 1,
        premise = premise_bound,
        conclusion = conclusion_bound,
    )
}

// -- 1. EmptyPipeline --

#[test]
fn test_empty_pipeline_returns_error() {
    let result = verify_and_compose_pipeline(&[]);
    assert!(matches!(result, Err(PipelineError::EmptyPipeline)));
}

#[test]
fn test_empty_pipeline_display_message() {
    let err = verify_and_compose_pipeline(&[]).unwrap_err();
    let msg = err.to_string();
    assert!(
        msg.contains("at least one certificate"),
        "expected display to mention 'at least one certificate', got: {msg}"
    );
}

#[test]
fn test_empty_pipeline_debug_format() {
    let err = verify_and_compose_pipeline(&[]).unwrap_err();
    let dbg = format!("{err:?}");
    assert!(
        dbg.contains("EmptyPipeline"),
        "expected Debug to contain 'EmptyPipeline', got: {dbg}"
    );
}

// -- 2. ParseError --

#[test]
fn test_parse_error_invalid_json_index_zero() {
    let result = verify_and_compose_pipeline(&["not valid json"]);
    match result {
        Err(PipelineError::ParseError { index: 0, .. }) => {}
        other => panic!("expected ParseError at index 0, got {other:?}"),
    }
}

#[test]
fn test_parse_error_valid_first_invalid_second() {
    let good = make_cert_json("x", 5, 6);
    let result = verify_and_compose_pipeline(&[&good, "bad json"]);
    match result {
        Err(PipelineError::ParseError { index: 1, .. }) => {}
        other => panic!("expected ParseError at index 1, got {other:?}"),
    }
}

#[test]
fn test_parse_error_empty_string() {
    let result = verify_and_compose_pipeline(&[""]);
    match result {
        Err(PipelineError::ParseError { index: 0, .. }) => {}
        other => panic!("expected ParseError at index 0, got {other:?}"),
    }
}

#[test]
fn test_parse_error_wrong_schema() {
    let bad_schema = r#"{"version":"1.0","wrong_field":true}"#;
    let result = verify_and_compose_pipeline(&[bad_schema]);
    match result {
        Err(PipelineError::ParseError { index: 0, .. }) => {}
        other => panic!("expected ParseError at index 0 for wrong schema, got {other:?}"),
    }
}

#[test]
fn test_parse_error_array_instead_of_object() {
    let result = verify_and_compose_pipeline(&["[1,2,3]"]);
    match result {
        Err(PipelineError::ParseError { index: 0, .. }) => {}
        other => panic!("expected ParseError at index 0, got {other:?}"),
    }
}

#[test]
fn test_parse_error_index_tracks_in_multi_cert() {
    let good = make_cert_json("x", 5, 6);
    let result = verify_and_compose_pipeline(&[&good, &good, "{}", &good]);
    match result {
        Err(PipelineError::ParseError { index: 2, .. }) => {}
        other => panic!("expected ParseError at index 2, got {other:?}"),
    }
}

#[test]
fn test_parse_error_display_contains_index() {
    let result = verify_and_compose_pipeline(&["zzz"]);
    let msg = result.unwrap_err().to_string();
    assert!(
        msg.contains("index 0"),
        "expected display to mention 'index 0', got: {msg}"
    );
}

// -- 3. VerificationFailed --

#[test]
fn test_verification_failed_invalid_entailment() {
    // x<=5 implies x<=3 is invalid (5 > 3)
    let bad = make_cert_json("x", 5, 3);
    let result = verify_and_compose_pipeline(&[&bad]);
    match result {
        Err(PipelineError::VerificationFailed { index: 0, .. }) => {}
        other => panic!("expected VerificationFailed at index 0, got {other:?}"),
    }
}

#[test]
fn test_verification_failed_valid_first_invalid_second() {
    let good = make_cert_json("x", 5, 6);
    let bad = make_cert_json("x", 10, 2);
    let result = verify_and_compose_pipeline(&[&good, &bad]);
    match result {
        Err(PipelineError::VerificationFailed { index: 1, .. }) => {}
        other => panic!("expected VerificationFailed at index 1, got {other:?}"),
    }
}

#[test]
fn test_verification_failed_third_of_three() {
    let a = make_cert_json("x", 1, 3);
    let b = make_cert_json("x", 3, 5);
    let bad = make_cert_json("x", 5, 1);
    let result = verify_and_compose_pipeline(&[&a, &b, &bad]);
    match result {
        Err(PipelineError::VerificationFailed { index: 2, .. }) => {}
        other => panic!("expected VerificationFailed at index 2, got {other:?}"),
    }
}

#[test]
fn test_verification_failed_index_tracks_correctly() {
    let a = make_cert_json("x", 1, 2);
    let b = make_cert_json("x", 2, 4);
    let c = make_cert_json("x", 4, 6);
    let bad = make_cert_json("x", 100, 50);
    let result = verify_and_compose_pipeline(&[&a, &b, &c, &bad]);
    match result {
        Err(PipelineError::VerificationFailed { index: 3, .. }) => {}
        other => panic!("expected VerificationFailed at index 3, got {other:?}"),
    }
}

#[test]
fn test_verification_failed_display_contains_index() {
    let bad = make_cert_json("x", 10, 2);
    let msg = verify_and_compose_pipeline(&[&bad])
        .unwrap_err()
        .to_string();
    assert!(
        msg.contains("index 0"),
        "expected display to mention 'index 0', got: {msg}"
    );
}

#[test]
fn test_verification_failed_equal_bounds_is_valid() {
    // x<=5 implies x<=5 is valid (premise bound = conclusion bound)
    let cert = make_cert_json("x", 5, 5);
    let result = verify_and_compose_pipeline(&[&cert]);
    assert!(result.is_ok(), "equal bounds should be valid: {result:?}");
}

// -- 4. Single cert (no composition) --

#[test]
fn test_single_cert_input_count() {
    let json = make_cert_json("x", 5, 6);
    let result = verify_and_compose_pipeline(&[&json]).unwrap();
    assert_eq!(result.input_count, 1);
}

#[test]
fn test_single_cert_composition_steps_zero() {
    let json = make_cert_json("x", 5, 6);
    let result = verify_and_compose_pipeline(&[&json]).unwrap();
    assert_eq!(result.composition_steps, 0);
}

#[test]
fn test_single_cert_preserves_conclusion() {
    let json = make_cert_json("x", 3, 10);
    let result = verify_and_compose_pipeline(&[&json]).unwrap();
    let conclusion_constant = result.certificate.conclusion.constant;
    assert_eq!(
        conclusion_constant,
        clean_elab::cert::external::ExternalRational::from_int(10)
    );
}

#[test]
fn test_single_cert_preserves_premise() {
    let json = make_cert_json("x", 3, 10);
    let result = verify_and_compose_pipeline(&[&json]).unwrap();
    assert_eq!(result.certificate.premises.len(), 1);
    let premise_constant = result.certificate.premises[0].constant;
    assert_eq!(
        premise_constant,
        clean_elab::cert::external::ExternalRational::from_int(3)
    );
}

#[test]
fn test_single_cert_different_variable() {
    let json = make_cert_json("temperature", 100, 200);
    let result = verify_and_compose_pipeline(&[&json]);
    assert!(
        result.is_ok(),
        "different variable name should work: {result:?}"
    );
    assert_eq!(result.unwrap().input_count, 1);
}

#[test]
fn test_single_cert_large_gap() {
    let json = make_cert_json("x", 0, 1000);
    let result = verify_and_compose_pipeline(&[&json]);
    assert!(result.is_ok(), "large gap should be valid: {result:?}");
}

// -- 5. Two-cert composition --

#[test]
fn test_two_cert_composition_basic() {
    let a = make_cert_json("x", 5, 6);
    let b = make_cert_json("x", 6, 8);
    let result = verify_and_compose_pipeline(&[&a, &b]).unwrap();
    // Composed: x<=5 => x<=8
    assert_eq!(
        result.certificate.conclusion.constant,
        clean_elab::cert::external::ExternalRational::from_int(8)
    );
}

#[test]
fn test_two_cert_input_count() {
    let a = make_cert_json("x", 5, 6);
    let b = make_cert_json("x", 6, 8);
    let result = verify_and_compose_pipeline(&[&a, &b]).unwrap();
    assert_eq!(result.input_count, 2);
}

#[test]
fn test_two_cert_composition_steps() {
    let a = make_cert_json("x", 5, 6);
    let b = make_cert_json("x", 6, 8);
    let result = verify_and_compose_pipeline(&[&a, &b]).unwrap();
    assert_eq!(result.composition_steps, 1);
}

#[test]
fn test_two_cert_preserves_first_premise() {
    let a = make_cert_json("x", 5, 6);
    let b = make_cert_json("x", 6, 8);
    let result = verify_and_compose_pipeline(&[&a, &b]).unwrap();
    assert_eq!(result.certificate.premises.len(), 1);
    assert_eq!(
        result.certificate.premises[0].constant,
        clean_elab::cert::external::ExternalRational::from_int(5)
    );
}

#[test]
fn test_two_cert_composition_failed_no_match() {
    // cert_a concludes x<=6, cert_b expects y<=3 as premise -> no match
    let a = make_cert_json("x", 5, 6);
    let b = make_cert_json("y", 3, 4);
    let result = verify_and_compose_pipeline(&[&a, &b]);
    match result {
        Err(PipelineError::CompositionFailed {
            left: 0, right: 1, ..
        }) => {}
        other => panic!("expected CompositionFailed(0,1), got {other:?}"),
    }
}

#[test]
fn test_two_cert_composition_failed_bound_mismatch() {
    // cert_a concludes x<=6, cert_b expects x<=7 as premise -> mismatch
    let a = make_cert_json("x", 5, 6);
    let b = make_cert_json("x", 7, 9);
    let result = verify_and_compose_pipeline(&[&a, &b]);
    match result {
        Err(PipelineError::CompositionFailed {
            left: 0, right: 1, ..
        }) => {}
        other => panic!("expected CompositionFailed(0,1), got {other:?}"),
    }
}

#[test]
fn test_two_cert_composition_tight_bounds() {
    // x<=10 => x<=10 then x<=10 => x<=10 (equal bounds, valid entailment)
    let a = make_cert_json("x", 10, 10);
    let b = make_cert_json("x", 10, 10);
    let result = verify_and_compose_pipeline(&[&a, &b]);
    assert!(
        result.is_ok(),
        "tight equal-bound chain should compose: {result:?}"
    );
}

#[test]
fn test_two_cert_composition_failed_display_contains_indices() {
    let a = make_cert_json("x", 5, 6);
    let b = make_cert_json("y", 3, 4);
    let msg = verify_and_compose_pipeline(&[&a, &b])
        .unwrap_err()
        .to_string();
    assert!(msg.contains("0"), "display should mention index 0: {msg}");
    assert!(msg.contains("1"), "display should mention index 1: {msg}");
}

// -- 6. Multi-cert pipeline --

#[test]
fn test_three_cert_chain() {
    let a = make_cert_json("x", 3, 5);
    let b = make_cert_json("x", 5, 7);
    let c = make_cert_json("x", 7, 10);
    let result = verify_and_compose_pipeline(&[&a, &b, &c]).unwrap();
    assert_eq!(
        result.certificate.conclusion.constant,
        clean_elab::cert::external::ExternalRational::from_int(10)
    );
}

#[test]
fn test_three_cert_input_count() {
    let a = make_cert_json("x", 3, 5);
    let b = make_cert_json("x", 5, 7);
    let c = make_cert_json("x", 7, 10);
    let result = verify_and_compose_pipeline(&[&a, &b, &c]).unwrap();
    assert_eq!(result.input_count, 3);
}

#[test]
fn test_three_cert_composition_steps() {
    let a = make_cert_json("x", 3, 5);
    let b = make_cert_json("x", 5, 7);
    let c = make_cert_json("x", 7, 10);
    let result = verify_and_compose_pipeline(&[&a, &b, &c]).unwrap();
    assert_eq!(result.composition_steps, 2);
}

#[test]
fn test_four_cert_chain() {
    let a = make_cert_json("x", 1, 2);
    let b = make_cert_json("x", 2, 4);
    let c = make_cert_json("x", 4, 6);
    let d = make_cert_json("x", 6, 9);
    let result = verify_and_compose_pipeline(&[&a, &b, &c, &d]).unwrap();
    assert_eq!(result.input_count, 4);
    assert_eq!(result.composition_steps, 3);
    assert_eq!(
        result.certificate.conclusion.constant,
        clean_elab::cert::external::ExternalRational::from_int(9)
    );
}

#[test]
fn test_composition_steps_equals_input_count_minus_one() {
    let a = make_cert_json("x", 0, 1);
    let b = make_cert_json("x", 1, 2);
    let c = make_cert_json("x", 2, 3);
    let d = make_cert_json("x", 3, 4);
    let e = make_cert_json("x", 4, 5);
    let result = verify_and_compose_pipeline(&[&a, &b, &c, &d, &e]).unwrap();
    assert_eq!(result.composition_steps, result.input_count - 1);
    assert_eq!(result.input_count, 5);
}

#[test]
fn test_multi_cert_preserves_first_premise() {
    let a = make_cert_json("x", 3, 5);
    let b = make_cert_json("x", 5, 7);
    let c = make_cert_json("x", 7, 10);
    let result = verify_and_compose_pipeline(&[&a, &b, &c]).unwrap();
    assert_eq!(
        result.certificate.premises[0].constant,
        clean_elab::cert::external::ExternalRational::from_int(3)
    );
}

// -- 7. PipelineError Display --

#[test]
fn test_pipeline_error_display_parse_error() {
    let err = verify_and_compose_pipeline(&["{"]).unwrap_err();
    let msg = err.to_string();
    assert!(
        msg.contains("parse error"),
        "expected 'parse error' in: {msg}"
    );
    assert!(msg.contains("index 0"), "expected 'index 0' in: {msg}");
}

#[test]
fn test_pipeline_error_display_verification_failed() {
    let bad = make_cert_json("x", 10, 1);
    let err = verify_and_compose_pipeline(&[&bad]).unwrap_err();
    let msg = err.to_string();
    assert!(
        msg.contains("verification failed"),
        "expected 'verification failed' in: {msg}"
    );
    assert!(msg.contains("index 0"), "expected 'index 0' in: {msg}");
}

#[test]
fn test_pipeline_error_display_composition_failed() {
    let a = make_cert_json("x", 5, 6);
    let b = make_cert_json("y", 3, 4);
    let err = verify_and_compose_pipeline(&[&a, &b]).unwrap_err();
    let msg = err.to_string();
    assert!(
        msg.contains("composition failed"),
        "expected 'composition failed' in: {msg}"
    );
}

// -- 8. Edge cases --

#[test]
fn test_edge_case_large_bounds() {
    let json = make_cert_json("x", 1_000_000, 2_000_000);
    let result = verify_and_compose_pipeline(&[&json]);
    assert!(result.is_ok(), "large bounds should work: {result:?}");
}

#[test]
fn test_edge_case_negative_bounds() {
    let json = make_cert_json("x", -10, -5);
    let result = verify_and_compose_pipeline(&[&json]);
    assert!(result.is_ok(), "negative bounds should work: {result:?}");
}

#[test]
fn test_edge_case_zero_to_positive() {
    let json = make_cert_json("x", 0, 1);
    let result = verify_and_compose_pipeline(&[&json]);
    assert!(result.is_ok(), "zero to positive should work: {result:?}");
}

#[test]
fn test_edge_case_negative_to_zero() {
    let json = make_cert_json("x", -5, 0);
    let result = verify_and_compose_pipeline(&[&json]);
    assert!(result.is_ok(), "negative to zero should work: {result:?}");
}

#[test]
fn test_edge_case_single_step_unit_increment() {
    // x<=0 => x<=1 — the smallest possible non-trivial entailment
    let json = make_cert_json("x", 0, 1);
    let result = verify_and_compose_pipeline(&[&json]).unwrap();
    assert_eq!(result.input_count, 1);
    assert_eq!(result.composition_steps, 0);
}

#[test]
fn test_edge_case_chain_with_negative_bounds() {
    let a = make_cert_json("x", -10, -5);
    let b = make_cert_json("x", -5, 0);
    let c = make_cert_json("x", 0, 3);
    let result = verify_and_compose_pipeline(&[&a, &b, &c]).unwrap();
    assert_eq!(
        result.certificate.conclusion.constant,
        clean_elab::cert::external::ExternalRational::from_int(3)
    );
    assert_eq!(
        result.certificate.premises[0].constant,
        clean_elab::cert::external::ExternalRational::from_int(-10)
    );
}
