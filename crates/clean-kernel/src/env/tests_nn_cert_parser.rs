// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for gamma-crown certificate parser (`nn_verify_cert_parser`).
//!
//! Part of #3255.

use super::nn_verify_cert_parser::*;
use crate::env::Environment;
use crate::expr::ExprKind;
use crate::name::Name;
use crate::tc::TypeChecker;

fn minimal_cert_json() -> &'static str {
    r#"{
        "network_name": "test_net",
        "layers": [
            {
                "layer_id": 0,
                "input_bounds": { "lower": [0.0, -1.0], "upper": [1.0, 1.0] },
                "output_bounds": { "lower": [-0.5, -0.5, -0.5], "upper": [0.5, 0.5, 0.5] },
                "proof_type": "ibp"
            },
            {
                "layer_id": 1,
                "input_bounds": { "lower": [-0.5, -0.5, -0.5], "upper": [0.5, 0.5, 0.5] },
                "output_bounds": { "lower": [-1.0, -1.0], "upper": [1.0, 1.0] },
                "proof_type": "ibp"
            }
        ]
    }"#
}

fn single_layer_cert_json() -> &'static str {
    r#"{
        "network_name": "single",
        "layers": [{
            "layer_id": 0,
            "input_bounds": { "lower": [0.0, 0.0], "upper": [1.0, 1.0] },
            "output_bounds": { "lower": [0.0, 0.0], "upper": [1.0, 1.0] },
            "proof_type": "ibp"
        }]
    }"#
}

fn make_env() -> Environment {
    let mut env = Environment::new();
    env.init_nn_verify_types().expect("init_nn_verify_types");
    env.init_nn_verify_proofs().expect("init_nn_verify_proofs");
    env
}

// --- Parsing tests ---

#[test]
fn test_parse_minimal_certificate() {
    let cert = Certificate::parse(minimal_cert_json()).expect("should parse");
    assert_eq!(cert.network_name, "test_net");
    assert_eq!(cert.layers.len(), 2);
    assert_eq!(cert.layers[0].layer_id, 0);
    assert_eq!(cert.layers[1].layer_id, 1);
    assert_eq!(cert.layers[0].proof_type, ProofType::Ibp);
}

#[test]
fn test_parse_single_layer() {
    let cert = Certificate::parse(single_layer_cert_json()).expect("should parse");
    assert_eq!(cert.layers.len(), 1);
}

#[test]
fn test_parse_empty_layers_rejected() {
    let json = r#"{"network_name": "bad", "layers": []}"#;
    let err = Certificate::parse(json).expect_err("empty layers should fail");
    assert!(matches!(err, CertParseError::EmptyLayers));
}

#[test]
fn test_parse_dim_mismatch_rejected() {
    let json = r#"{"layers": [{"layer_id": 0,
        "input_bounds": {"lower": [0.0], "upper": [1.0, 2.0]},
        "output_bounds": {"lower": [0.0], "upper": [1.0]}}]}"#;
    let err = Certificate::parse(json).expect_err("dim mismatch should fail");
    assert!(matches!(err, CertParseError::DimMismatch { .. }));
}

#[test]
fn test_parse_bound_violation_rejected() {
    let json = r#"{"layers": [{"layer_id": 0,
        "input_bounds": {"lower": [5.0], "upper": [1.0]},
        "output_bounds": {"lower": [0.0], "upper": [1.0]}}]}"#;
    let err = Certificate::parse(json).expect_err("bound violation should fail");
    assert!(matches!(err, CertParseError::BoundViolation { .. }));
}

#[test]
fn test_parse_chain_dim_mismatch_rejected() {
    let json = r#"{"layers": [
        {"layer_id": 0,
         "input_bounds": {"lower": [0.0, 0.0], "upper": [1.0, 1.0]},
         "output_bounds": {"lower": [0.0, 0.0, 0.0], "upper": [1.0, 1.0, 1.0]}},
        {"layer_id": 1,
         "input_bounds": {"lower": [0.0, 0.0], "upper": [1.0, 1.0]},
         "output_bounds": {"lower": [0.0], "upper": [1.0]}}
    ]}"#;
    let err = Certificate::parse(json).expect_err("chain dim mismatch should fail");
    assert!(matches!(err, CertParseError::ChainDimMismatch { .. }));
}

#[test]
fn test_parse_farkas_proof_type() {
    let json = r#"{"layers": [{"layer_id": 0,
        "input_bounds": {"lower": [0.0], "upper": [1.0]},
        "output_bounds": {"lower": [0.0], "upper": [1.0]},
        "proof_type": "farkas",
        "farkas": {"coefficients": [[0.5, 0.5], [0.3, 0.7]]}}]}"#;
    let cert = Certificate::parse(json).expect("should parse farkas");
    assert_eq!(cert.layers[0].proof_type, ProofType::Farkas);
    assert!(cert.layers[0].farkas.is_some());
}

#[test]
fn test_parse_default_proof_type() {
    let json = r#"{"layers": [{"layer_id": 0,
        "input_bounds": {"lower": [0.0], "upper": [1.0]},
        "output_bounds": {"lower": [0.0], "upper": [1.0]}}]}"#;
    let cert = Certificate::parse(json).expect("should parse without proof_type");
    assert_eq!(cert.layers[0].proof_type, ProofType::Ibp);
}

// --- Expr construction tests ---

#[test]
fn test_single_layer_expr_construction() {
    let mut env = make_env();
    let result = env
        .parse_nn_certificate(single_layer_cert_json())
        .expect("should construct");
    assert_eq!(result.layers.len(), 1);
    assert_eq!(result.layers[0].input_dim, 2);
    assert_eq!(result.layers[0].output_dim, 2);
    assert!(result.chain_proof_type.is_none());
}

#[test]
fn test_two_layer_expr_construction() {
    let mut env = make_env();
    let result = env
        .parse_nn_certificate(minimal_cert_json())
        .expect("should construct");
    assert_eq!(result.layers.len(), 2);
    assert!(result.chain_proof_type.is_some());
}

#[test]
fn test_registered_axioms_exist() {
    let mut env = make_env();
    env.parse_nn_certificate(single_layer_cert_json())
        .expect("should construct");
    assert!(env
        .get_const(&Name::from_string("cert_single_in_L0_lower"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("cert_single_in_L0_upper"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("cert_single_in_L0_valid"))
        .is_some());
}

#[test]
fn test_registered_axioms_type_check() {
    let mut env = make_env();
    env.parse_nn_certificate(single_layer_cert_json())
        .expect("should construct");
    let tc = TypeChecker::with_mode(&env, env.mode());

    let lower = crate::expr::Expr::const_(Name::from_string("cert_single_in_L0_lower"), vec![]);
    let lower_ty = tc.infer_type(&lower).expect("lower should type-check");
    match lower_ty.kind() {
        ExprKind::App(_, _) => {} // NNVec applied to Nat lit
        other => panic!("Expected App for NNVec type, got {other:?}"),
    }

    let upper = crate::expr::Expr::const_(Name::from_string("cert_single_in_L0_upper"), vec![]);
    let upper_ty = tc.infer_type(&upper).expect("upper should type-check");
    match upper_ty.kind() {
        ExprKind::App(_, _) => {}
        other => panic!("Expected App for NNVec type, got {other:?}"),
    }
}

#[test]
fn test_two_layer_subset_axiom_registered() {
    let mut env = make_env();
    env.parse_nn_certificate(minimal_cert_json())
        .expect("should construct");
    assert!(env
        .get_const(&Name::from_string("cert_test_net_subset_L0_L1"))
        .is_some());
}

#[test]
fn test_idempotent_parsing() {
    let mut env = make_env();
    env.parse_nn_certificate(single_layer_cert_json())
        .expect("first parse");
    env.parse_nn_certificate(single_layer_cert_json())
        .expect("second parse (idempotent)");
}

#[test]
fn test_rat_from_f64_positive() {
    let c = CertConsts::new();
    let expr = c.rat_from_f64(3.0);
    match expr.kind() {
        ExprKind::App(_, denom) => match denom.kind() {
            ExprKind::Lit(_) => {}
            other => panic!("Expected Lit for denom, got {other:?}"),
        },
        other => panic!("Expected App for Rat.mk, got {other:?}"),
    }
}

#[test]
fn test_rat_from_f64_negative() {
    let c = CertConsts::new();
    let expr = c.rat_from_f64(-2.0);
    match expr.kind() {
        ExprKind::App(_, _) => {}
        other => panic!("Expected App for Rat.mk, got {other:?}"),
    }
}

#[test]
fn test_rat_from_f64_zero() {
    let c = CertConsts::new();
    let expr = c.rat_from_f64(0.0);
    match expr.kind() {
        ExprKind::App(_, _) => {}
        other => panic!("Expected App for Rat.mk, got {other:?}"),
    }
}

// --- Farkas parsing tests ---

fn farkas_cert_json() -> &'static str {
    r#"{
        "network_name": "farkas_net",
        "layers": [{
            "layer_id": 0,
            "input_bounds": { "lower": [0.0], "upper": [1.0] },
            "output_bounds": { "lower": [-0.5], "upper": [0.5] },
            "proof_type": "farkas",
            "farkas": {
                "coefficients": [[0.5, 0.5], [0.3, 0.7]]
            }
        }]
    }"#
}

#[test]
fn test_parse_farkas_with_witness() {
    let cert = Certificate::parse(farkas_cert_json()).expect("should parse farkas cert");
    assert_eq!(cert.layers[0].proof_type, ProofType::Farkas);
    let farkas = cert.layers[0]
        .farkas
        .as_ref()
        .expect("should have farkas data");
    assert_eq!(farkas.coefficients.len(), 2); // 2 * output_dim(1)
    assert_eq!(farkas.coefficients[0].len(), 2); // 2 * input_dim(1)
}

#[test]
fn test_farkas_missing_witness_rejected() {
    let json = r#"{"layers": [{"layer_id": 0,
        "input_bounds": {"lower": [0.0], "upper": [1.0]},
        "output_bounds": {"lower": [0.0], "upper": [1.0]},
        "proof_type": "farkas"}]}"#;
    let err = Certificate::parse(json).expect_err("missing farkas witness should fail");
    assert!(matches!(err, CertParseError::FarkasMissing { .. }));
}

#[test]
fn test_farkas_wrong_row_count_rejected() {
    let json = r#"{"layers": [{"layer_id": 0,
        "input_bounds": {"lower": [0.0], "upper": [1.0]},
        "output_bounds": {"lower": [0.0], "upper": [1.0]},
        "proof_type": "farkas",
        "farkas": {"coefficients": [[0.5, 0.5]]}}]}"#;
    // output_dim=1, so expected_rows=2, but we gave 1
    let err = Certificate::parse(json).expect_err("wrong row count should fail");
    assert!(matches!(err, CertParseError::FarkasRowCount { .. }));
}

#[test]
fn test_farkas_wrong_col_count_rejected() {
    let json = r#"{"layers": [{"layer_id": 0,
        "input_bounds": {"lower": [0.0], "upper": [1.0]},
        "output_bounds": {"lower": [0.0], "upper": [1.0]},
        "proof_type": "farkas",
        "farkas": {"coefficients": [[0.5, 0.5, 0.0], [0.3, 0.7, 0.0]]}}]}"#;
    // input_dim=1, so expected_cols=2, but we gave 3
    let err = Certificate::parse(json).expect_err("wrong col count should fail");
    assert!(matches!(err, CertParseError::FarkasColCount { .. }));
}

#[test]
fn test_farkas_negative_coefficient_rejected() {
    let json = r#"{"layers": [{"layer_id": 0,
        "input_bounds": {"lower": [0.0], "upper": [1.0]},
        "output_bounds": {"lower": [0.0], "upper": [1.0]},
        "proof_type": "farkas",
        "farkas": {"coefficients": [[0.5, -0.1], [0.3, 0.7]]}}]}"#;
    let err = Certificate::parse(json).expect_err("negative coefficient should fail");
    assert!(matches!(err, CertParseError::FarkasNegative { .. }));
}

#[test]
fn test_farkas_expr_construction() {
    let mut env = make_env();
    let result = env
        .parse_nn_certificate(farkas_cert_json())
        .expect("should construct");
    assert_eq!(result.layers.len(), 1);
    assert!(result.layers[0].farkas_coeffs_expr.is_some());
    // Check that the Farkas coefficient matrix axiom was registered
    assert!(env
        .get_const(&Name::from_string("cert_farkas_net_L0_farkas_coeffs"))
        .is_some());
    // Check individual coefficient definitions
    assert!(env
        .get_const(&Name::from_string("cert_farkas_net_L0_farkas_c0_0"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("cert_farkas_net_L0_farkas_c1_1"))
        .is_some());
}

#[test]
fn test_farkas_coefficients_type_check() {
    let mut env = make_env();
    env.parse_nn_certificate(farkas_cert_json())
        .expect("should construct");
    let tc = TypeChecker::with_mode(&env, env.mode());

    // The matrix axiom should type-check to NNMat 2 2
    let mat = crate::expr::Expr::const_(
        Name::from_string("cert_farkas_net_L0_farkas_coeffs"),
        vec![],
    );
    let mat_ty = tc
        .infer_type(&mat)
        .expect("farkas_coeffs should type-check");
    match mat_ty.kind() {
        ExprKind::App(_, _) => {} // NNMat applied to args
        other => panic!("Expected App for NNMat type, got {other:?}"),
    }

    // Individual coefficient should type-check to Rat
    let c00 =
        crate::expr::Expr::const_(Name::from_string("cert_farkas_net_L0_farkas_c0_0"), vec![]);
    let c00_ty = tc.infer_type(&c00).expect("coeff c0_0 should type-check");
    let rat_name = Name::from_string("Rat");
    match c00_ty.kind() {
        ExprKind::Const(n, _) if *n == rat_name => {}
        other => panic!("Expected Rat for coefficient type, got {other:?}"),
    }
}

#[test]
fn test_ibp_layer_has_no_farkas_expr() {
    let mut env = make_env();
    let result = env
        .parse_nn_certificate(single_layer_cert_json())
        .expect("should construct");
    assert!(result.layers[0].farkas_coeffs_expr.is_none());
}

// --- Error display tests ---

#[test]
fn test_error_display_formats() {
    let e = CertParseError::EmptyLayers;
    assert_eq!(format!("{e}"), "certificate has no layers");

    let e = CertParseError::DimMismatch {
        layer_id: 0,
        lower_len: 2,
        upper_len: 3,
    };
    assert!(format!("{e}").contains("dimension mismatch"));

    let e = CertParseError::BoundViolation {
        layer_id: 1,
        index: 3,
        lower: 5.0,
        upper: 1.0,
    };
    assert!(format!("{e}").contains("bound violation"));

    let e = CertParseError::FarkasMissing { layer_id: 0 };
    assert!(format!("{e}").contains("Farkas witness missing"));

    let e = CertParseError::FarkasNegative {
        layer_id: 0,
        row: 1,
        col: 2,
        value: -0.5,
    };
    assert!(format!("{e}").contains("negative"));
}

// ---------------------------------------------------------------------------
// Exact-rational Farkas-multiplier COMBINATION tests (closes the f64 +
// skipped-check gap; ports clean-extcert-verify logic into the kernel parser).
// ---------------------------------------------------------------------------

use crate::env::types::ConstantKind;

fn entail_env() -> Environment {
    let mut env = Environment::new();
    env.init_nn_verify_types().expect("init_nn_verify_types");
    env.init_eq().expect("init_eq");
    env
}

/// A SOUND entailment certificate: from `x <= 2` and `y <= 3`, multipliers
/// [1, 1] combine to `x + y <= 5`; the claimed conclusion is exactly `x+y<=5`.
fn sound_entailment_json() -> &'static str {
    r#"{
        "version": "1.0",
        "premises": [
            { "kind": "le", "coefficients": { "x": "1" }, "constant": "2" },
            { "kind": "le", "coefficients": { "y": "1" }, "constant": "3" }
        ],
        "multipliers": ["1", "1"],
        "conclusion": { "kind": "le", "coefficients": { "x": "1", "y": "1" }, "constant": "5" }
    }"#
}

/// A SOUND certificate exercising EXACT rationals: from `x <= 1/3`,
/// multiplier [3] combines to `3x <= 1`.
fn sound_rational_json() -> &'static str {
    r#"{
        "version": "1.0",
        "premises": [
            { "kind": "le", "coefficients": { "x": "1" }, "constant": "1/3" }
        ],
        "multipliers": ["3"],
        "conclusion": { "kind": "le", "coefficients": { "x": "3" }, "constant": "1" }
    }"#
}

/// UNSOUND: bound too tight. Combination yields `x + y <= 5` but the cert
/// claims `x + y <= 4`; 5 does not imply 4, so it MUST be rejected.
fn unsound_bound_json() -> &'static str {
    r#"{
        "version": "1.0",
        "premises": [
            { "kind": "le", "coefficients": { "x": "1" }, "constant": "2" },
            { "kind": "le", "coefficients": { "y": "1" }, "constant": "3" }
        ],
        "multipliers": ["1", "1"],
        "conclusion": { "kind": "le", "coefficients": { "x": "1", "y": "1" }, "constant": "4" }
    }"#
}

/// UNSOUND: coefficient mismatch. Combination yields `x + y <= 5` but the cert
/// claims a conclusion over `x` only.
fn unsound_coeff_json() -> &'static str {
    r#"{
        "version": "1.0",
        "premises": [
            { "kind": "le", "coefficients": { "x": "1" }, "constant": "2" },
            { "kind": "le", "coefficients": { "y": "1" }, "constant": "3" }
        ],
        "multipliers": ["1", "1"],
        "conclusion": { "kind": "le", "coefficients": { "x": "1" }, "constant": "5" }
    }"#
}

/// UNSOUND: a negative multiplier is not a valid Farkas combination.
fn unsound_negative_mult_json() -> &'static str {
    r#"{
        "version": "1.0",
        "premises": [
            { "kind": "le", "coefficients": { "x": "1" }, "constant": "2" }
        ],
        "multipliers": ["-1"],
        "conclusion": { "kind": "le", "coefficients": { "x": "-1" }, "constant": "-2" }
    }"#
}

#[test]
fn test_valid_entailment_accepted_and_witness_type_checks() {
    let mut env = entail_env();
    let name = env
        .verify_entailment_certificate_kernel(sound_entailment_json(), "sound")
        .expect("sound entailment certificate must be ACCEPTED");

    // The derived witness is a real Declaration::Theorem (DERIVED, not Axiom).
    let info = env
        .get_const(&name)
        .expect("witness theorem should be registered");
    assert_eq!(
        info.kind,
        ConstantKind::Theorem,
        "combination witness must be a Theorem, not an Axiom"
    );

    // It is sorry-free.
    assert!(
        !info.sorry_summary().has_sorry,
        "combination witness proof must not use sorry"
    );

    // Its proof term type-checks against its declared type via the kernel's
    // own TypeChecker::infer_type, and the inferred type is def-eq to declared.
    let tc = TypeChecker::with_mode(&env, env.mode());
    let proof = info.value.as_ref().expect("Theorem should have a value");
    let inferred = tc
        .infer_type(proof)
        .expect("combination witness proof must type-check");
    assert!(
        tc.is_def_eq(&inferred, &info.type_),
        "inferred type must match declared theorem type"
    );
}

#[test]
fn test_valid_rational_entailment_accepted() {
    let mut env = entail_env();
    let name = env
        .verify_entailment_certificate_kernel(sound_rational_json(), "rat")
        .expect("sound rational entailment must be ACCEPTED");
    let info = env.get_const(&name).expect("registered");
    assert_eq!(info.kind, ConstantKind::Theorem);
    assert!(!info.sorry_summary().has_sorry);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let proof = info.value.as_ref().unwrap();
    let inferred = tc.infer_type(proof).expect("proof type-checks");
    assert!(tc.is_def_eq(&inferred, &info.type_));
}

#[test]
fn test_unsound_bound_rejected() {
    let mut env = entail_env();
    let err = env
        .verify_entailment_certificate_kernel(unsound_bound_json(), "bad_bound")
        .expect_err("a too-tight bound must be REJECTED, never axiomatized");
    assert!(
        matches!(err, CertParseError::EntailmentFailed { .. }),
        "expected EntailmentFailed, got {err:?}"
    );
    // Nothing registered.
    assert!(
        env.get_const(&Name::from_string("cert_bad_bound_combination_sound"))
            .is_none(),
        "no witness should be registered for an unsound certificate"
    );
}

#[test]
fn test_unsound_coefficients_rejected() {
    let mut env = entail_env();
    let err = env
        .verify_entailment_certificate_kernel(unsound_coeff_json(), "bad_coeff")
        .expect_err("coefficient mismatch must be REJECTED");
    assert!(matches!(err, CertParseError::EntailmentFailed { .. }));
}

#[test]
fn test_unsound_negative_multiplier_rejected() {
    let mut env = entail_env();
    let err = env
        .verify_entailment_certificate_kernel(unsound_negative_mult_json(), "neg_mult")
        .expect_err("negative multiplier must be REJECTED");
    assert!(matches!(err, CertParseError::EntailmentFailed { .. }));
}

#[test]
fn test_exact_rational_parsing_no_truncation() {
    // 1/3 must NOT be truncated to 0 (the old rat_from_f64 bug). Use a cert
    // that only verifies if 1/3 is treated exactly: x <= 1/3 scaled by 3 == 1.
    let mut env = entail_env();
    env.verify_entailment_certificate_kernel(sound_rational_json(), "exact")
        .expect("exact 1/3 handling required");
    // And a variant claiming `3x <= 0` (what truncation-to-0 would 'prove')
    // must be REJECTED, confirming we did NOT truncate.
    let truncation_trap = r#"{
        "version": "1.0",
        "premises": [
            { "kind": "le", "coefficients": { "x": "1" }, "constant": "1/3" }
        ],
        "multipliers": ["3"],
        "conclusion": { "kind": "le", "coefficients": { "x": "3" }, "constant": "0" }
    }"#;
    let err = env
        .verify_entailment_certificate_kernel(truncation_trap, "trap")
        .expect_err("3 * (1/3) = 1, not <= 0; must be rejected");
    assert!(matches!(err, CertParseError::EntailmentFailed { .. }));
}

// ---------------------------------------------------------------------------
// Combination step backed by the CONSTRUCTIVE `NNVerify.farkas_combine_list`
// theorem (n-row Farkas via List.rec, sorry-free) — the witness is genuinely
// DERIVED from the kernel-checked combination, not a bare Axiom.
// ---------------------------------------------------------------------------

/// Recursively check whether `e` mentions the constant `target` anywhere.
fn mentions_const(e: &crate::expr::Expr, target: &str) -> bool {
    let target_name = Name::from_string(target);
    let mut found = false;
    let mut stack = vec![e.clone()];
    while let Some(cur) = stack.pop() {
        match cur.kind() {
            ExprKind::Const(n, _) if *n == target_name => {
                found = true;
                break;
            }
            ExprKind::App(f, a) => {
                stack.push((**f).clone());
                stack.push((**a).clone());
            }
            ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
                stack.push((**ty).clone());
                stack.push((**body).clone());
            }
            ExprKind::Let(_, ty, val, body, _) => {
                stack.push((**ty).clone());
                stack.push((**val).clone());
                stack.push((**body).clone());
            }
            _ => {}
        }
    }
    found
}

/// A SOUND multi-row entailment: from `x <= 2`, `y <= 3`, `z <= 5` with
/// multipliers [2, 1, 3], the combined upper bound is 2*2 + 1*3 + 3*5 = 22,
/// matching the claimed `2x + y + 3z <= 22`.
fn sound_three_row_json() -> &'static str {
    r#"{
        "version": "1.0",
        "premises": [
            { "kind": "le", "coefficients": { "x": "1" }, "constant": "2" },
            { "kind": "le", "coefficients": { "y": "1" }, "constant": "3" },
            { "kind": "le", "coefficients": { "z": "1" }, "constant": "5" }
        ],
        "multipliers": ["2", "1", "3"],
        "conclusion": { "kind": "le", "coefficients": { "x": "2", "y": "1", "z": "3" }, "constant": "22" }
    }"#
}

#[test]
fn test_combination_witness_is_farkas_combine_list_backed() {
    let mut env = entail_env();
    let (name, list_backed) = env
        .verify_entailment_certificate_kernel_ex(sound_three_row_json(), "flist")
        .expect("sound multi-row entailment must be ACCEPTED");

    // The witness took the constructive kernel-list path.
    assert!(
        list_backed,
        "single-row premises must yield a farkas_combine_list-backed witness, \
         not the Eq.refl fallback"
    );

    let info = env.get_const(&name).expect("witness theorem registered");

    // It is a real Theorem (DERIVED), not an Axiom.
    assert_eq!(
        info.kind,
        ConstantKind::Theorem,
        "combination witness must be a Theorem, not an Axiom"
    );

    // Sorry-free.
    assert!(
        !info.sorry_summary().has_sorry,
        "combination witness proof must be sorry-free"
    );

    // The proof term genuinely references the constructive theorem
    // `NNVerify.farkas_combine_list` (the kernel-checked n-row combination),
    // i.e. the witness is BACKED BY it rather than a bare axiom.
    let proof = info.value.as_ref().expect("Theorem should have a value");
    assert!(
        mentions_const(proof, "NNVerify.farkas_combine_list"),
        "witness proof must be backed by NNVerify.farkas_combine_list"
    );

    // And the statement's conclusion folds through farkasLower/farkasUpper —
    // the multiplier-combination summation is reproduced by the kernel reducer.
    assert!(
        mentions_const(&info.type_, "NNVerify.farkasUpper")
            && mentions_const(&info.type_, "NNVerify.farkasLower"),
        "witness type must be the farkasLower ≤ farkasUpper combination"
    );

    // The proof term type-checks against its declared type under the kernel's
    // own TypeChecker — the combination is genuinely kernel-derived.
    let tc = TypeChecker::with_mode(&env, env.mode());
    let inferred = tc
        .infer_type(proof)
        .expect("combination witness proof must type-check");
    assert!(
        tc.is_def_eq(&inferred, &info.type_),
        "inferred type must match declared theorem type"
    );

    // The `farkas_combine_list` const it references is itself a sorry-free
    // Theorem in this environment.
    let fcl = env
        .get_const(&Name::from_string("NNVerify.farkas_combine_list"))
        .expect("farkas_combine_list must be registered");
    assert_eq!(fcl.kind, ConstantKind::Theorem);
    assert!(!fcl.sorry_summary().has_sorry);
}

#[test]
fn test_sound_two_row_is_farkas_list_backed_and_typechecks() {
    // The pre-existing `sound_entailment_json` (x<=2, y<=3, mults [1,1] ⇒
    // x+y<=5) is all single-row, so it too must now be list-backed.
    let mut env = entail_env();
    let (name, list_backed) = env
        .verify_entailment_certificate_kernel_ex(sound_entailment_json(), "two_row")
        .expect("sound two-row entailment must be ACCEPTED");
    assert!(
        list_backed,
        "two single-row premises ⇒ farkas_combine_list path"
    );
    let info = env.get_const(&name).expect("registered");
    assert_eq!(info.kind, ConstantKind::Theorem);
    assert!(!info.sorry_summary().has_sorry);
    let proof = info.value.as_ref().unwrap();
    assert!(mentions_const(proof, "NNVerify.farkas_combine_list"));
    let tc = TypeChecker::with_mode(&env, env.mode());
    let inferred = tc.infer_type(proof).expect("proof type-checks");
    assert!(tc.is_def_eq(&inferred, &info.type_));
}

#[test]
fn test_unsound_cert_rejected_no_farkas_list_witness() {
    // An unsound (too-tight bound) cert must be REJECTED before any
    // farkas_combine_list witness is built — no axiom, no theorem.
    let mut env = entail_env();
    let err = env
        .verify_entailment_certificate_kernel_ex(unsound_bound_json(), "flist_bad")
        .expect_err("too-tight bound must be REJECTED, never witnessed");
    assert!(
        matches!(err, CertParseError::EntailmentFailed { .. }),
        "expected EntailmentFailed, got {err:?}"
    );
    assert!(
        env.get_const(&Name::from_string("cert_flist_bad_combination_sound"))
            .is_none(),
        "no farkas_combine_list witness for an unsound certificate"
    );
}

// ---------------------------------------------------------------------------
// Arbitrary-precision (bignum) widening: BIG-but-VALID certificates whose
// reduced numerators/denominators exceed i128 must now be ACCEPTED and lowered
// EXACTLY (no truncation, correct sign), while every fail-closed reject
// (zero denominator, malformed input) must STILL reject.
// ---------------------------------------------------------------------------

/// Decode a kernel `Nat` literal `Expr` (built by `Expr::bignat_lit`) back to a
/// `num_bigint::BigUint`. Inverse of `biguint_to_bignat`: `BigNat::limbs()` is
/// little-endian, exactly what `BigUint::new(Vec<u32>)` does NOT expect, so we
/// rebuild from the u64 limbs directly. Used to ASSERT the lowering is exact.
fn decode_nat_lit(e: &crate::expr::Expr) -> num_bigint::BigUint {
    use crate::expr::{ExprKind, Literal};
    use num_bigint::BigUint;
    match e.kind() {
        ExprKind::Lit(Literal::Nat(bn)) => {
            // BigNat::limbs() is little-endian u64. Reconstruct as Σ limb_i·2^(64i).
            let mut acc = BigUint::from(0u8);
            let base = BigUint::from(1u128 << 64);
            for &limb in bn.limbs().iter().rev() {
                acc = acc * &base + BigUint::from(limb);
            }
            acc
        }
        other => panic!("expected a Nat literal, got {other:?}"),
    }
}

/// Walk a lowered `Rat.mk (Int.ofNat|Int.negSucc m) den` term and reconstruct
/// the EXACT `(num, den)` it denotes, so a test can assert it equals the input
/// rational bit-for-bit (the cardinal soundness rule for the trusted lowering).
fn decode_rat_mk(e: &crate::expr::Expr) -> (num_bigint::BigInt, num_bigint::BigInt) {
    use crate::expr::ExprKind;
    use num_bigint::{BigInt, BigUint, Sign};
    // e = ((Rat.mk int_expr) den_lit)
    let (mk_int, den_lit) = match e.kind() {
        ExprKind::App(f, a) => ((**f).clone(), (**a).clone()),
        other => panic!("expected Rat.mk application, got {other:?}"),
    };
    let den_mag = decode_nat_lit(&den_lit);
    let den = BigInt::from_biguint(Sign::Plus, den_mag);
    // mk_int = (Rat.mk int_expr); int_expr = (Int.ofNat m) | (Int.negSucc m)
    let int_expr = match mk_int.kind() {
        ExprKind::App(_rat_mk, int_e) => (**int_e).clone(),
        other => panic!("expected (Rat.mk int_expr), got {other:?}"),
    };
    let (ctor, mag_lit) = match int_expr.kind() {
        ExprKind::App(ctor, m) => ((**ctor).clone(), (**m).clone()),
        other => panic!("expected Int.ofNat/negSucc application, got {other:?}"),
    };
    let ctor_name = match ctor.kind() {
        ExprKind::Const(n, _) => n.clone(),
        other => panic!("expected Int constructor const, got {other:?}"),
    };
    let mag = decode_nat_lit(&mag_lit);
    let num = if ctor_name == Name::from_string("Int.ofNat") {
        BigInt::from_biguint(Sign::Plus, mag)
    } else if ctor_name == Name::from_string("Int.negSucc") {
        // negSucc m denotes -(m+1).
        let neg = mag + BigUint::from(1u8);
        BigInt::from_biguint(Sign::Minus, neg)
    } else {
        panic!("unexpected Int constructor {ctor_name:?}");
    };
    (num, den)
}

#[test]
fn test_rat_from_exact_lowers_bignum_exactly() {
    use num_bigint::BigInt;
    use num_traits::Num;

    let c = CertConsts::new();

    // 2^200 — far beyond i128::MAX (~1.7e38); the old `nat_lit(... as u64)`
    // would have truncated mod 2^64. Reduced fraction (3·2^200)/3 == 2^200/1.
    let pow200 = BigInt::from(2).pow(200);

    // Positive bignum integer: num = 2^200, den = 1.
    let lit = c.rat_from_exact(&pow200, &BigInt::from(1));
    let (n, d) = decode_rat_mk(&lit);
    assert_eq!(n, pow200, "positive bignum numerator must lower EXACTLY");
    assert_eq!(d, BigInt::from(1), "denominator must lower EXACTLY");

    // Negative bignum integer: num = -2^200 (exercises the negSucc(|num|-1)
    // path widened to BigNat — the old `(abs-1) as u64` would wrap).
    let neg = -pow200.clone();
    let lit = c.rat_from_exact(&neg, &BigInt::from(1));
    let (n, d) = decode_rat_mk(&lit);
    assert_eq!(
        n, neg,
        "negative bignum numerator must lower EXACTLY (negSucc)"
    );
    assert_eq!(d, BigInt::from(1));

    // Big fraction with big denominator: (2^200 + 1) / (2^130 - 7), kept reduced.
    let big_num = &pow200 + BigInt::from(1);
    let big_den = BigInt::from(2).pow(130) - BigInt::from(7);
    // Reduce as BigRational would (gcd) to mirror what ExactRat stores.
    let r = num_rational::BigRational::new(big_num.clone(), big_den.clone());
    let lit = c.rat_from_exact(r.numer(), r.denom());
    let (n, d) = decode_rat_mk(&lit);
    assert_eq!(&n, r.numer(), "reduced big numerator lowers EXACTLY");
    assert_eq!(&d, r.denom(), "reduced big denominator lowers EXACTLY");

    // A value whose magnitude is an exact multiple of 2^64 (limb boundary): a
    // regression guard for trailing-zero-limb handling in from_limbs.
    let limb_boundary = BigInt::from_str_radix("18446744073709551616", 10).unwrap(); // 2^64
    let lit = c.rat_from_exact(&limb_boundary, &BigInt::from(1));
    let (n, _d) = decode_rat_mk(&lit);
    assert_eq!(n, limb_boundary, "2^64 (limb boundary) lowers EXACTLY");
}

/// A SOUND entailment whose constants exceed i128: `x <= 2^200`, multiplier 3
/// ⇒ `3x <= 3·2^200`. The old i128 path REJECTED this (parse / `checked_mul`
/// overflow); it must now be ACCEPTED and its witness must type-check.
fn sound_bignum_json() -> String {
    let pow200 = num_bigint::BigInt::from(2).pow(200);
    let three_pow200 = &pow200 * num_bigint::BigInt::from(3);
    format!(
        r#"{{
            "version": "1.0",
            "premises": [
                {{ "kind": "le", "coefficients": {{ "x": "1" }}, "constant": "{pow200}" }}
            ],
            "multipliers": ["3"],
            "conclusion": {{ "kind": "le", "coefficients": {{ "x": "3" }}, "constant": "{three_pow200}" }}
        }}"#
    )
}

#[test]
fn test_bignum_entailment_accepted_and_witness_type_checks() {
    let mut env = entail_env();
    let json = sound_bignum_json();
    let (name, list_backed) = env
        .verify_entailment_certificate_kernel_ex(&json, "bignum")
        .expect("BIG-but-VALID bignum entailment must now be ACCEPTED");
    assert!(
        list_backed,
        "single-row bignum premise ⇒ farkas_combine_list-backed witness"
    );
    let info = env.get_const(&name).expect("witness theorem registered");
    assert_eq!(info.kind, ConstantKind::Theorem);
    assert!(
        !info.sorry_summary().has_sorry,
        "bignum combination witness must be sorry-free"
    );
    // The lowered `Rat.mk (Int.ofNat <2^200-scale bignum>) ...` term type-checks
    // through the kernel's own TypeChecker — the bignum literal is a valid
    // kernel Nat literal, not a truncated one.
    let proof = info.value.as_ref().expect("Theorem has a value");
    let tc = TypeChecker::with_mode(&env, env.mode());
    let inferred = tc
        .infer_type(proof)
        .expect("bignum witness proof must type-check");
    assert!(
        tc.is_def_eq(&inferred, &info.type_),
        "inferred type must match declared theorem type"
    );
}

#[test]
fn test_bignum_too_tight_bound_still_rejected() {
    // Same bignum coefficients, but the claimed bound is ONE LESS than the
    // exact combination (3·2^200 − 1). The exact-rational gate must REJECT it
    // — widening to bignum must not weaken the soundness check.
    let pow200 = num_bigint::BigInt::from(2).pow(200);
    let too_tight = &pow200 * num_bigint::BigInt::from(3) - num_bigint::BigInt::from(1);
    let json = format!(
        r#"{{
            "version": "1.0",
            "premises": [
                {{ "kind": "le", "coefficients": {{ "x": "1" }}, "constant": "{pow200}" }}
            ],
            "multipliers": ["3"],
            "conclusion": {{ "kind": "le", "coefficients": {{ "x": "3" }}, "constant": "{too_tight}" }}
        }}"#
    );
    let mut env = entail_env();
    let err = env
        .verify_entailment_certificate_kernel(&json, "bignum_tight")
        .expect_err("a too-tight bignum bound must still be REJECTED");
    assert!(
        matches!(err, CertParseError::EntailmentFailed { .. }),
        "expected EntailmentFailed, got {err:?}"
    );
    assert!(
        env.get_const(&Name::from_string("cert_bignum_tight_combination_sound"))
            .is_none(),
        "nothing registered for an unsound bignum cert"
    );
}

#[test]
fn test_zero_denominator_still_rejected() {
    // A malformed cert with a zero denominator must stay a clean fail-closed
    // reject (NOT a panic from BigRational::new, NOT an accept).
    let json = r#"{
        "version": "1.0",
        "premises": [
            { "kind": "le", "coefficients": { "x": "1" }, "constant": "1/0" }
        ],
        "multipliers": ["1"],
        "conclusion": { "kind": "le", "coefficients": { "x": "1" }, "constant": "0" }
    }"#;
    let mut env = entail_env();
    let err = env
        .verify_entailment_certificate_kernel(json, "zero_den")
        .expect_err("zero denominator must be REJECTED, never panic");
    assert!(
        matches!(err, CertParseError::RationalArith { .. }),
        "expected RationalArith (zero denominator), got {err:?}"
    );
}

#[test]
fn test_malformed_rationals_still_rejected() {
    // Scientific notation, trailing dot, double-dot, and >2 slash parts must
    // ALL remain rejects after the bignum widening — only too-BIG-but-VALID
    // values became acceptances.
    for (bad, label) in [
        ("1e10", "scientific"),
        ("1.", "trailing-dot"),
        ("1.2.3", "double-dot"),
        ("1/2/3", "three-parts"),
        ("", "empty"),
        ("abc", "non-digit"),
    ] {
        let json = format!(
            r#"{{
                "version": "1.0",
                "premises": [
                    {{ "kind": "le", "coefficients": {{ "x": "1" }}, "constant": "{bad}" }}
                ],
                "multipliers": ["1"],
                "conclusion": {{ "kind": "le", "coefficients": {{ "x": "1" }}, "constant": "0" }}
            }}"#
        );
        let mut env = entail_env();
        let err = env
            .verify_entailment_certificate_kernel(&json, "malformed")
            .expect_err(&format!("malformed rational ({label}) must be REJECTED"));
        assert!(
            matches!(err, CertParseError::RationalArith { .. }),
            "expected RationalArith for {label}, got {err:?}"
        );
    }
}
