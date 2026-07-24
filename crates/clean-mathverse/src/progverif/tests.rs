// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Integration tests for the progverif shared abstractions.
//!
//! Covers: certificate replay strategies, SMT VC bundles, sort/term parsing,
//! certificate serialization, all 9 importers, cross-importer consistency,
//! and edge cases in the shared infrastructure.

use crate::progverif::cert_replay::{
    AletheLfReplayStrategy, CertReplayError, CertReplayResult, CertReplayStrategy, Certificate,
    CertificateFormat, DratReplayStrategy, NullReplayStrategy,
};
use crate::progverif::smt_bridge::{
    parse_smtlib2_sort, parse_smtlib2_term, translate_smt_sort_to_clean, Quantifier, SmtAssertion,
    SmtBridgeError, SmtLiteral, SmtSort, SmtTerm, SmtVcBundle,
};
use crate::types::{AxiomProfile, SourceSystem, TrustLevel};

// ===========================================================================
// CertReplayStrategy trait tests
// ===========================================================================

#[test]
fn test_null_replay_strategy_trait_object() {
    let strategy: Box<dyn CertReplayStrategy> = Box::new(NullReplayStrategy);
    let cert = Certificate::new(CertificateFormat::SmtLib2, b"(proof)".to_vec(), "z3");
    let result = strategy
        .replay(&cert)
        .expect("null strategy always succeeds");
    assert!(result.verified);
    assert_eq!(result.trust_level, TrustLevel::TrustedOracle);
    assert!(result.axiom_profile.contains(AxiomProfile::SMT_ORACLE));
}

#[test]
fn test_null_replay_strategy_works_with_empty_certificate() {
    let strategy = NullReplayStrategy;
    let cert = Certificate::new(CertificateFormat::Lrat, vec![], "empty");
    let result = strategy
        .replay(&cert)
        .expect("null strategy accepts empty certs");
    assert!(result.verified);
}

#[test]
fn test_null_replay_strategy_works_with_custom_format() {
    let strategy = NullReplayStrategy;
    let cert = Certificate::new(
        CertificateFormat::Custom("boogie-cert".into()),
        b"custom data".to_vec(),
        "boogie",
    );
    let result = strategy
        .replay(&cert)
        .expect("null strategy accepts custom formats");
    assert!(result.verified);
    assert_eq!(result.trust_level, TrustLevel::TrustedOracle);
}

#[test]
fn test_null_replay_strategy_name_and_formats() {
    let strategy = NullReplayStrategy;
    assert_eq!(strategy.name(), "null");
    assert!(strategy.supported_formats().is_empty());
}

// ---------------------------------------------------------------------------
// AletheLfReplayStrategy integration tests
// ---------------------------------------------------------------------------

#[test]
fn test_alethe_lf_replay_valid_cert_returns_certificate_replayed() {
    let strategy = AletheLfReplayStrategy::new();
    let cert = Certificate::new(
        CertificateFormat::AletheLF,
        b"(assume h1 (not P))\n(step t1 (cl P Q) :rule resolution)".to_vec(),
        "cvc5",
    );
    let result = strategy.replay(&cert).expect("valid Alethe-LF cert");
    assert!(result.verified);
    assert_eq!(result.trust_level, TrustLevel::CertificateReplayed);
    assert!(result.axiom_profile.contains(AxiomProfile::SAT_CERT));
}

#[test]
fn test_alethe_lf_replay_wrong_format_returns_error() {
    let strategy = AletheLfReplayStrategy::new();
    let cert = Certificate::new(CertificateFormat::Drat, b"data".to_vec(), "cadical");
    let err = strategy.replay(&cert).unwrap_err();
    assert!(matches!(err, CertReplayError::UnsupportedFormat { .. }));
}

#[test]
fn test_alethe_lf_replay_empty_cert_returns_error() {
    let strategy = AletheLfReplayStrategy::new();
    let cert = Certificate::new(CertificateFormat::AletheLF, vec![], "cvc5");
    let err = strategy.replay(&cert).unwrap_err();
    assert!(matches!(err, CertReplayError::InvalidCert { .. }));
}

#[test]
fn test_alethe_lf_replay_no_proof_steps_returns_error() {
    let strategy = AletheLfReplayStrategy::new();
    let cert = Certificate::new(
        CertificateFormat::AletheLF,
        b"(define-fun f () Bool true)".to_vec(),
        "cvc5",
    );
    let err = strategy.replay(&cert).unwrap_err();
    assert!(matches!(err, CertReplayError::InvalidCert { .. }));
}

#[test]
fn test_alethe_lf_replay_invalid_utf8_returns_error() {
    let strategy = AletheLfReplayStrategy::new();
    let cert = Certificate::new(CertificateFormat::AletheLF, vec![0xFF, 0xFE], "cvc5");
    let err = strategy.replay(&cert).unwrap_err();
    assert!(matches!(err, CertReplayError::InvalidCert { .. }));
}

#[test]
fn test_alethe_lf_as_trait_object() {
    let strategy: Box<dyn CertReplayStrategy> = Box::new(AletheLfReplayStrategy::new());
    let cert = Certificate::new(
        CertificateFormat::AletheLF,
        b"(assume a1 P)\n(step t1 (cl P) :rule assumption)".to_vec(),
        "cvc5",
    );
    let result = strategy.replay(&cert).expect("trait object replay");
    assert!(result.verified);
}

// ---------------------------------------------------------------------------
// DratReplayStrategy integration tests
// ---------------------------------------------------------------------------

#[test]
fn test_drat_replay_text_cert_returns_certificate_replayed() {
    let strategy = DratReplayStrategy::new();
    let cert = Certificate::new(
        CertificateFormat::Drat,
        b"1 2 0\n-1 3 0\nd 1 2 0\n4 0\n".to_vec(),
        "cadical",
    );
    let result = strategy.replay(&cert).expect("valid text DRAT cert");
    assert!(result.verified);
    assert_eq!(result.trust_level, TrustLevel::CertificateReplayed);
    assert!(result.axiom_profile.contains(AxiomProfile::SAT_CERT));
}

#[test]
fn test_drat_replay_binary_cert_accepted() {
    let strategy = DratReplayStrategy::new();
    let binary_cert = vec![b'a', 0x02, 0x04, 0x00, b'd', 0x02, 0x00, b'a', 0x06, 0x00];
    let cert = Certificate::new(CertificateFormat::Drat, binary_cert, "cadical");
    let result = strategy.replay(&cert).expect("binary DRAT cert");
    assert!(result.verified);
    assert!(result.diagnostics.iter().any(|d| d.contains("binary")));
}

#[test]
fn test_lrat_replay_text_cert_accepted() {
    let strategy = DratReplayStrategy::new();
    let cert = Certificate::new(
        CertificateFormat::Lrat,
        b"5 1 2 0 1 2 0\n6 -1 3 0 3 4 0\nd 1 2 0\n7 0 5 6 0\n".to_vec(),
        "cake_lpr",
    );
    let result = strategy.replay(&cert).expect("LRAT cert");
    assert!(result.verified);
    assert!(result.diagnostics.iter().any(|d| d.contains("LRAT")));
}

#[test]
fn test_drat_replay_wrong_format_returns_error() {
    let strategy = DratReplayStrategy::new();
    let cert = Certificate::new(CertificateFormat::AletheLF, b"(step t1)".to_vec(), "cvc5");
    let err = strategy.replay(&cert).unwrap_err();
    assert!(matches!(err, CertReplayError::UnsupportedFormat { .. }));
}

#[test]
fn test_drat_replay_empty_cert_returns_error() {
    let strategy = DratReplayStrategy::new();
    let cert = Certificate::new(CertificateFormat::Drat, vec![], "cadical");
    let err = strategy.replay(&cert).unwrap_err();
    assert!(matches!(err, CertReplayError::InvalidCert { .. }));
}

#[test]
fn test_drat_replay_min_size_threshold_rejects_small_cert() {
    let strategy = DratReplayStrategy::new().with_min_cert_size(100);
    let cert = Certificate::new(CertificateFormat::Drat, b"1 0\n".to_vec(), "cadical");
    let err = strategy.replay(&cert).unwrap_err();
    assert!(matches!(err, CertReplayError::InvalidCert { .. }));
}

#[test]
fn test_drat_as_trait_object() {
    let strategy: Box<dyn CertReplayStrategy> = Box::new(DratReplayStrategy::new());
    let cert = Certificate::new(CertificateFormat::Drat, b"1 2 0\n".to_vec(), "cadical");
    let result = strategy.replay(&cert).expect("trait object replay");
    assert!(result.verified);
}

// ===========================================================================
// SmtVcBundle creation and manipulation
// ===========================================================================

#[test]
fn test_smt_vc_bundle_with_certificate() {
    let cert = Certificate::new(
        CertificateFormat::AletheLF,
        b"(step t1 (cl (not P) Q) :rule resolution)".to_vec(),
        "cvc5",
    )
    .with_metadata("logic", "QF_UF")
    .with_metadata("solver-version", "1.1.0");

    let bundle = SmtVcBundle::new("QF_UF")
        .with_sort(SmtSort::uninterpreted("Elem"))
        .with_assertion(SmtAssertion {
            name: Some("pre".into()),
            term: SmtTerm::app("P", vec![SmtTerm::var("x")]),
            source_line: Some(10),
        })
        .with_assertion(SmtAssertion {
            name: Some("post".into()),
            term: SmtTerm::app("Q", vec![SmtTerm::var("x")]),
            source_line: Some(20),
        })
        .with_certificate(cert);

    assert_eq!(bundle.logic, "QF_UF");
    assert_eq!(bundle.assertion_count(), 2);
    let cert_ref = bundle
        .certificate
        .as_ref()
        .expect("certificate should be attached");
    assert_eq!(cert_ref.source_tool, "cvc5");
    assert_eq!(cert_ref.format, CertificateFormat::AletheLF);
    assert_eq!(
        cert_ref.metadata.get("logic").map(String::as_str),
        Some("QF_UF")
    );
}

#[test]
fn test_smt_vc_bundle_empty() {
    let bundle = SmtVcBundle::new("ALL");
    assert_eq!(bundle.logic, "ALL");
    assert!(bundle.sorts.is_empty());
    assert_eq!(bundle.assertion_count(), 0);
    assert!(bundle.certificate.is_none());
}

#[test]
fn test_smt_vc_bundle_multiple_sorts() {
    let bundle = SmtVcBundle::new("AUFLIA")
        .with_sort(SmtSort::Int)
        .with_sort(SmtSort::Bool)
        .with_sort(SmtSort::array(SmtSort::Int, SmtSort::Int))
        .with_sort(SmtSort::uninterpreted("State"))
        .with_sort(SmtSort::BitVec(64));
    assert_eq!(bundle.sorts.len(), 5);
}

#[test]
fn test_smt_vc_bundle_unnamed_assertions() {
    let bundle = SmtVcBundle::new("QF_LIA")
        .with_assertion(SmtAssertion {
            name: None,
            term: SmtTerm::bool_(true),
            source_line: None,
        })
        .with_assertion(SmtAssertion {
            name: None,
            term: SmtTerm::int(42),
            source_line: None,
        });
    assert_eq!(bundle.assertion_count(), 2);
    assert!(bundle.assertions[0].name.is_none());
    assert!(bundle.assertions[0].source_line.is_none());
}

#[test]
fn test_smt_vc_bundle_large_batch() {
    let mut bundle = SmtVcBundle::new("QF_LIA");
    for i in 0..1000 {
        bundle = bundle.with_assertion(SmtAssertion {
            name: Some(format!("vc_{i}")),
            term: SmtTerm::app(">=", vec![SmtTerm::var("x"), SmtTerm::int(i)]),
            source_line: Some(i as u32),
        });
    }
    assert_eq!(bundle.assertion_count(), 1000);
}

// ===========================================================================
// Sort translation integration
// ===========================================================================

#[test]
fn test_sort_translation_nested_array() {
    let sort = SmtSort::array(SmtSort::Int, SmtSort::array(SmtSort::Int, SmtSort::Bool));
    let expr =
        translate_smt_sort_to_clean(&sort).expect("nested array sort translation should succeed");
    match expr.kind() {
        clean_kernel::ExprKind::Pi(_, from, _to) => match from.kind() {
            clean_kernel::ExprKind::Const(name, _) => {
                assert_eq!(name.to_string(), "Int");
            }
            other => panic!("expected Const(Int) as outer domain, got {other:?}"),
        },
        other => panic!("expected Pi for nested array, got {other:?}"),
    }
}

#[test]
fn test_sort_translation_bitvec_widths() {
    for width in [1u32, 8, 16, 32, 64, 128, 256] {
        let expr = translate_smt_sort_to_clean(&SmtSort::BitVec(width))
            .unwrap_or_else(|_| panic!("BitVec({width}) translation should succeed"));
        match expr.kind() {
            clean_kernel::ExprKind::App(func, arg) => {
                match func.kind() {
                    clean_kernel::ExprKind::Const(name, _) => {
                        assert_eq!(name.to_string(), "BitVec");
                    }
                    other => panic!("expected Const(BitVec) func, got {other:?}"),
                }
                match arg.kind() {
                    clean_kernel::ExprKind::Lit(clean_kernel::Literal::Nat(n)) => {
                        assert_eq!(
                            n.to_u64(),
                            Some(u64::from(width)),
                            "BitVec width mismatch for {width}"
                        );
                    }
                    other => panic!("expected Nat literal arg, got {other:?}"),
                }
            }
            other => panic!("expected App for BitVec({width}), got {other:?}"),
        }
    }
}

#[test]
fn test_sort_translation_bool_to_prop() {
    let expr =
        translate_smt_sort_to_clean(&SmtSort::Bool).expect("Bool translation should succeed");
    assert!(
        matches!(expr.kind(), clean_kernel::ExprKind::Sort(level) if *level == clean_kernel::Level::zero()),
        "Bool should translate to Prop (Sort 0), got {:?}",
        expr.kind()
    );
}

#[test]
fn test_sort_translation_uninterpreted() {
    let expr = translate_smt_sort_to_clean(&SmtSort::uninterpreted("MySort"))
        .expect("Uninterpreted translation should succeed");
    match expr.kind() {
        clean_kernel::ExprKind::Const(name, _) => {
            assert_eq!(name.to_string(), "MySort");
        }
        other => panic!("expected Const(MySort), got {other:?}"),
    }
}

#[test]
fn test_sort_translation_int_to_const() {
    let expr = translate_smt_sort_to_clean(&SmtSort::Int).expect("Int translation should succeed");
    match expr.kind() {
        clean_kernel::ExprKind::Const(name, _) => {
            assert_eq!(name.to_string(), "Int");
        }
        other => panic!("expected Const(Int), got {other:?}"),
    }
}

#[test]
fn test_sort_translation_real_to_const() {
    let expr =
        translate_smt_sort_to_clean(&SmtSort::Real).expect("Real translation should succeed");
    match expr.kind() {
        clean_kernel::ExprKind::Const(name, _) => {
            assert_eq!(name.to_string(), "Real");
        }
        other => panic!("expected Const(Real), got {other:?}"),
    }
}

#[test]
fn test_sort_translation_simple_array() {
    let sort = SmtSort::array(SmtSort::Int, SmtSort::Bool);
    let expr =
        translate_smt_sort_to_clean(&sort).expect("Array(Int,Bool) translation should succeed");
    match expr.kind() {
        clean_kernel::ExprKind::Pi(_, from, to) => {
            match from.kind() {
                clean_kernel::ExprKind::Const(name, _) => assert_eq!(name.to_string(), "Int"),
                other => panic!("expected Const(Int) as domain, got {other:?}"),
            }
            // Codomain should be Prop (from Bool)
            assert!(
                matches!(to.kind(), clean_kernel::ExprKind::Sort(level) if *level == clean_kernel::Level::zero()),
                "expected Prop as codomain, got {:?}",
                to.kind()
            );
        }
        other => panic!("expected Pi (arrow), got {other:?}"),
    }
}

// ===========================================================================
// SMT-LIB2 sort parsing
// ===========================================================================

#[test]
fn test_parse_sort_base_sorts() {
    assert_eq!(parse_smtlib2_sort("Bool").unwrap(), SmtSort::Bool);
    assert_eq!(parse_smtlib2_sort("Int").unwrap(), SmtSort::Int);
    assert_eq!(parse_smtlib2_sort("Real").unwrap(), SmtSort::Real);
}

#[test]
fn test_parse_sort_bitvec_various_widths() {
    assert_eq!(
        parse_smtlib2_sort("(_ BitVec 1)").unwrap(),
        SmtSort::BitVec(1)
    );
    assert_eq!(
        parse_smtlib2_sort("(_ BitVec 8)").unwrap(),
        SmtSort::BitVec(8)
    );
    assert_eq!(
        parse_smtlib2_sort("(_ BitVec 32)").unwrap(),
        SmtSort::BitVec(32)
    );
    assert_eq!(
        parse_smtlib2_sort("(_ BitVec 64)").unwrap(),
        SmtSort::BitVec(64)
    );
    assert_eq!(
        parse_smtlib2_sort("(_ BitVec 256)").unwrap(),
        SmtSort::BitVec(256)
    );
}

#[test]
fn test_parse_sort_array_simple() {
    let result = parse_smtlib2_sort("(Array Int Bool)").unwrap();
    assert_eq!(result, SmtSort::array(SmtSort::Int, SmtSort::Bool));
}

#[test]
fn test_parse_sort_array_nested() {
    let result = parse_smtlib2_sort("(Array Int (Array Int Bool))").unwrap();
    let expected = SmtSort::array(SmtSort::Int, SmtSort::array(SmtSort::Int, SmtSort::Bool));
    assert_eq!(result, expected);
}

#[test]
fn test_parse_sort_uninterpreted_identifiers() {
    assert_eq!(
        parse_smtlib2_sort("MySort").unwrap(),
        SmtSort::Uninterpreted("MySort".to_string())
    );
    assert_eq!(
        parse_smtlib2_sort("Elem").unwrap(),
        SmtSort::Uninterpreted("Elem".to_string())
    );
}

#[test]
fn test_parse_sort_whitespace_handling() {
    assert_eq!(parse_smtlib2_sort("  Int  ").unwrap(), SmtSort::Int);
    assert_eq!(
        parse_smtlib2_sort("  (Array  Int  Bool)  ").unwrap(),
        SmtSort::array(SmtSort::Int, SmtSort::Bool)
    );
}

#[test]
fn test_parse_sort_empty_returns_error() {
    let result = parse_smtlib2_sort("");
    assert!(result.is_err());
}

#[test]
fn test_parse_sort_unmatched_paren_returns_error() {
    let result = parse_smtlib2_sort("(Array Int Bool");
    assert!(result.is_err());
}

#[test]
fn test_parse_sort_invalid_bitvec_width_returns_error() {
    let result = parse_smtlib2_sort("(_ BitVec abc)");
    assert!(result.is_err());
}

#[test]
fn test_parse_sort_unknown_compound_returns_error() {
    let result = parse_smtlib2_sort("(Set Int)");
    assert!(result.is_err());
}

// ===========================================================================
// SMT-LIB2 term parsing
// ===========================================================================

#[test]
fn test_parse_term_boolean_literals() {
    assert_eq!(parse_smtlib2_term("true").unwrap(), SmtTerm::bool_(true));
    assert_eq!(parse_smtlib2_term("false").unwrap(), SmtTerm::bool_(false));
}

#[test]
fn test_parse_term_integer_literals() {
    assert_eq!(parse_smtlib2_term("0").unwrap(), SmtTerm::int(0));
    assert_eq!(parse_smtlib2_term("42").unwrap(), SmtTerm::int(42));
    assert_eq!(parse_smtlib2_term("-5").unwrap(), SmtTerm::int(-5));
    assert_eq!(parse_smtlib2_term("999999").unwrap(), SmtTerm::int(999999));
}

#[test]
fn test_parse_term_negated_literal_via_parens() {
    let result = parse_smtlib2_term("(- 42)").unwrap();
    assert_eq!(result, SmtTerm::int(-42));
}

#[test]
fn test_parse_term_variables() {
    assert_eq!(parse_smtlib2_term("x").unwrap(), SmtTerm::var("x"));
    assert_eq!(
        parse_smtlib2_term("my_var").unwrap(),
        SmtTerm::var("my_var")
    );
    assert_eq!(parse_smtlib2_term("x!0").unwrap(), SmtTerm::var("x!0"));
}

#[test]
fn test_parse_term_simple_function_application() {
    let result = parse_smtlib2_term("(+ x 1)").unwrap();
    match result {
        SmtTerm::App(op, args) => {
            assert_eq!(op, "+");
            assert_eq!(args.len(), 2);
            assert_eq!(args[0], SmtTerm::var("x"));
            assert_eq!(args[1], SmtTerm::int(1));
        }
        other => panic!("expected App, got {other:?}"),
    }
}

#[test]
fn test_parse_term_nested_application() {
    let result = parse_smtlib2_term("(and (= x 1) (> y 0))").unwrap();
    match result {
        SmtTerm::App(op, args) => {
            assert_eq!(op, "and");
            assert_eq!(args.len(), 2);
            match &args[0] {
                SmtTerm::App(op2, args2) => {
                    assert_eq!(op2, "=");
                    assert_eq!(args2.len(), 2);
                }
                other => panic!("expected App for first arg, got {other:?}"),
            }
        }
        other => panic!("expected App(and), got {other:?}"),
    }
}

#[test]
fn test_parse_term_let_single_binding() {
    let result = parse_smtlib2_term("(let ((x 5)) x)").unwrap();
    match result {
        SmtTerm::Let(bindings, body) => {
            assert_eq!(bindings.len(), 1);
            assert_eq!(bindings[0].0, "x");
            assert_eq!(bindings[0].1, SmtTerm::int(5));
            assert_eq!(*body, SmtTerm::var("x"));
        }
        other => panic!("expected Let, got {other:?}"),
    }
}

#[test]
fn test_parse_term_let_multiple_bindings() {
    let result = parse_smtlib2_term("(let ((x 1) (y 2)) (+ x y))").unwrap();
    match result {
        SmtTerm::Let(bindings, body) => {
            assert_eq!(bindings.len(), 2);
            assert_eq!(bindings[0].0, "x");
            assert_eq!(bindings[1].0, "y");
            match *body {
                SmtTerm::App(ref op, ref args) => {
                    assert_eq!(op, "+");
                    assert_eq!(args.len(), 2);
                }
                ref other => panic!("expected App body, got {other:?}"),
            }
        }
        other => panic!("expected Let, got {other:?}"),
    }
}

#[test]
fn test_parse_term_forall() {
    let result = parse_smtlib2_term("(forall ((n Int)) (>= n 0))").unwrap();
    match result {
        SmtTerm::Quant(q, vars, body) => {
            assert_eq!(q, Quantifier::ForAll);
            assert_eq!(vars.len(), 1);
            assert_eq!(vars[0].0, "n");
            assert_eq!(vars[0].1, SmtSort::Int);
            match *body {
                SmtTerm::App(ref op, _) => assert_eq!(op, ">="),
                ref other => panic!("expected App body, got {other:?}"),
            }
        }
        other => panic!("expected Quant, got {other:?}"),
    }
}

#[test]
fn test_parse_term_exists() {
    let result = parse_smtlib2_term("(exists ((x Bool)) x)").unwrap();
    match result {
        SmtTerm::Quant(q, vars, body) => {
            assert_eq!(q, Quantifier::Exists);
            assert_eq!(vars.len(), 1);
            assert_eq!(vars[0].0, "x");
            assert_eq!(vars[0].1, SmtSort::Bool);
            assert_eq!(*body, SmtTerm::var("x"));
        }
        other => panic!("expected Quant, got {other:?}"),
    }
}

#[test]
fn test_parse_term_forall_multiple_vars() {
    let result = parse_smtlib2_term("(forall ((x Int) (y Int)) (= x y))").unwrap();
    match result {
        SmtTerm::Quant(q, vars, _) => {
            assert_eq!(q, Quantifier::ForAll);
            assert_eq!(vars.len(), 2);
            assert_eq!(vars[0].0, "x");
            assert_eq!(vars[1].0, "y");
        }
        other => panic!("expected Quant, got {other:?}"),
    }
}

#[test]
fn test_parse_term_deeply_nested() {
    let result = parse_smtlib2_term("(or (and (= a b) (= c d)) (not e))").unwrap();
    match result {
        SmtTerm::App(op, args) => {
            assert_eq!(op, "or");
            assert_eq!(args.len(), 2);
        }
        other => panic!("expected App, got {other:?}"),
    }
}

#[test]
fn test_parse_term_nullary_app() {
    let result = parse_smtlib2_term("(f)").unwrap();
    match result {
        SmtTerm::App(op, args) => {
            assert_eq!(op, "f");
            assert!(args.is_empty());
        }
        other => panic!("expected App, got {other:?}"),
    }
}

#[test]
fn test_parse_term_empty_returns_error() {
    assert!(parse_smtlib2_term("").is_err());
}

#[test]
fn test_parse_term_unmatched_paren_returns_error() {
    assert!(parse_smtlib2_term("(+ x 1").is_err());
}

#[test]
fn test_parse_term_whitespace_only_returns_error() {
    assert!(parse_smtlib2_term("   \t\n  ").is_err());
}

// ===========================================================================
// Certificate serialization
// ===========================================================================

#[test]
fn test_certificate_json_round_trip() {
    let cert = Certificate::new(
        CertificateFormat::Drat,
        vec![0xDE, 0xAD, 0xBE, 0xEF],
        "cadical",
    )
    .with_metadata("clauses", "1024")
    .with_metadata("runtime_ms", "350");

    let json = serde_json::to_string(&cert).expect("certificate serialization");
    let restored: Certificate = serde_json::from_str(&json).expect("certificate deserialization");

    assert_eq!(restored.format, CertificateFormat::Drat);
    assert_eq!(restored.raw_bytes, vec![0xDE, 0xAD, 0xBE, 0xEF]);
    assert_eq!(restored.source_tool, "cadical");
    assert_eq!(
        restored.metadata.get("clauses").map(String::as_str),
        Some("1024")
    );
    assert_eq!(
        restored.metadata.get("runtime_ms").map(String::as_str),
        Some("350")
    );
}

#[test]
fn test_cert_replay_result_json_round_trip() {
    let result = CertReplayResult::verified(
        AxiomProfile::SAT_CERT | AxiomProfile::SMT_ORACLE,
        TrustLevel::CertificateReplayed,
        512,
    );

    let json = serde_json::to_string(&result).expect("result serialization");
    let restored: CertReplayResult = serde_json::from_str(&json).expect("result deserialization");

    assert!(restored.verified);
    assert!(restored.axiom_profile.contains(AxiomProfile::SAT_CERT));
    assert!(restored.axiom_profile.contains(AxiomProfile::SMT_ORACLE));
    assert_eq!(restored.trust_level, TrustLevel::CertificateReplayed);
    assert_eq!(restored.replay_time_us, 512);
}

#[test]
fn test_certificate_format_names() {
    assert_eq!(CertificateFormat::SmtLib2.name(), "SMT-LIB2");
    assert_eq!(CertificateFormat::Drat.name(), "DRAT");
    assert_eq!(CertificateFormat::Lrat.name(), "LRAT");
    assert_eq!(CertificateFormat::AletheLF.name(), "Alethe-LF");
    assert_eq!(CertificateFormat::Lfsc.name(), "LFSC");
    assert_eq!(
        CertificateFormat::Custom("myformat".into()).name(),
        "myformat"
    );
}

#[test]
fn test_certificate_is_empty() {
    let empty = Certificate::new(CertificateFormat::SmtLib2, vec![], "z3");
    assert!(empty.is_empty());
    assert_eq!(empty.byte_len(), 0);

    let nonempty = Certificate::new(CertificateFormat::SmtLib2, vec![1], "z3");
    assert!(!nonempty.is_empty());
    assert_eq!(nonempty.byte_len(), 1);
}

#[test]
fn test_cert_replay_result_failed() {
    let result = CertReplayResult::failed("bad step at index 7", 100);
    assert!(!result.verified);
    assert_eq!(result.trust_level, TrustLevel::TrustedOracle);
    assert_eq!(result.replay_time_us, 100);
    assert_eq!(result.diagnostics.len(), 1);
    assert!(result.diagnostics[0].contains("bad step"));
}

#[test]
fn test_certificate_format_serde_round_trip() {
    let formats = [
        CertificateFormat::SmtLib2,
        CertificateFormat::Drat,
        CertificateFormat::Lrat,
        CertificateFormat::AletheLF,
        CertificateFormat::Lfsc,
        CertificateFormat::Custom("boogie-cert".into()),
    ];
    for fmt in &formats {
        let json = serde_json::to_string(fmt).expect("format serialize");
        let restored: CertificateFormat = serde_json::from_str(&json).expect("format deserialize");
        assert_eq!(&restored, fmt);
    }
}

// ===========================================================================
// Dafny importer integration
// ===========================================================================

#[test]
fn test_dafny_importer_parses_full_vc() {
    use crate::progverif::dafny::DafnyImporter;

    let vc_text = "\
;; VC: Sort::postcondition::0
;; Method: Sort
;; File: sort.dfy
;; Line: 15
(set-logic ALL)
(assert (forall ((i Int) (j Int)) (=> (and (<= 0 i) (< i j) (< j n)) (<= (select a i) (select a j)))))
(check-sat)";

    let importer = DafnyImporter::new();
    let vc = importer.import_boogie_vc(vc_text).expect("should parse VC");
    assert_eq!(vc.name, "Sort::postcondition::0");
    assert_eq!(vc.method_name, "Sort");
    assert_eq!(vc.source_file.as_deref(), Some("sort.dfy"));
    assert_eq!(vc.source_line, Some(15));
    assert!(vc.assertion.contains("(assert"));
}

#[test]
fn test_dafny_importer_empty_input_returns_error() {
    use crate::progverif::dafny::DafnyImporter;

    let importer = DafnyImporter::new();
    let result = importer.import_boogie_vc("");
    assert!(result.is_err());
}

#[test]
fn test_dafny_importer_whitespace_only_returns_error() {
    use crate::progverif::dafny::DafnyImporter;

    let importer = DafnyImporter::new();
    let result = importer.import_boogie_vc("   \n\t  ");
    assert!(result.is_err());
}

#[test]
fn test_dafny_import_result_all_verified_no_cert() {
    use crate::progverif::dafny::DafnyImporter;

    let importer = DafnyImporter::new();
    let vc = importer
        .import_boogie_vc(";; VC: test\n;; Method: main\n(assert true)")
        .unwrap();
    let result = importer.import_dafny_result("module", &[vc], true);

    assert_eq!(result.vc_count, 1);
    assert_eq!(result.verified_count, 1);
    assert_eq!(result.axiom_profile, AxiomProfile::SMT_ORACLE);
    assert_eq!(result.trust_level, TrustLevel::TrustedOracle);
    assert_eq!(result.provenance.source, SourceSystem::Dafny);
}

#[test]
fn test_dafny_import_result_with_cert_replay() {
    use crate::progverif::dafny::DafnyImporter;

    let importer = DafnyImporter::new().with_cert_replay(true);
    let vc = importer
        .import_boogie_vc(";; VC: test\n;; Method: f\n(assert true)")
        .unwrap();
    let result = importer.import_dafny_result("module", &[vc], true);

    assert_eq!(result.axiom_profile, AxiomProfile::SAT_CERT);
    assert_eq!(result.trust_level, TrustLevel::CertificateReplayed);
}

#[test]
fn test_dafny_importer_has_default() {
    use crate::progverif::dafny::DafnyImporter;
    let _importer = DafnyImporter::default();
}

#[test]
fn test_dafny_parse_boogie_vc_standalone() {
    use crate::progverif::dafny::parse_boogie_vc;

    let vc = parse_boogie_vc(";; VC: test\n;; Method: f\n(assert true)").unwrap();
    assert_eq!(vc.name, "test");
    assert_eq!(vc.method_name, "f");
}

#[test]
fn test_dafny_parse_boogie_vc_standalone_empty_errors() {
    use crate::progverif::dafny::parse_boogie_vc;
    assert!(parse_boogie_vc("").is_err());
}

#[test]
fn test_dafny_classify_vc_kind_all_variants() {
    use crate::progverif::dafny::{classify_vc_kind, DafnyPoKind};

    assert_eq!(
        classify_vc_kind("method::precondition::0"),
        DafnyPoKind::Precondition
    );
    assert_eq!(
        classify_vc_kind("method::postcondition::0"),
        DafnyPoKind::Postcondition
    );
    assert_eq!(
        classify_vc_kind("loop_invariant_check"),
        DafnyPoKind::LoopInvariant
    );
    assert_eq!(
        classify_vc_kind("variant_decrease"),
        DafnyPoKind::LoopVariant
    );
    assert_eq!(classify_vc_kind("assert_check"), DafnyPoKind::Assertion);
    assert_eq!(classify_vc_kind("bounds_check"), DafnyPoKind::BoundsCheck);
    assert_eq!(
        classify_vc_kind("division_check"),
        DafnyPoKind::DivisionByZero
    );
    assert_eq!(classify_vc_kind("non_null_check"), DafnyPoKind::NonNull);
    assert_eq!(classify_vc_kind("something_else"), DafnyPoKind::Other);
}

#[test]
fn test_dafny_statistics_success_rate() {
    use crate::progverif::dafny::DafnyStatistics;

    let empty = DafnyStatistics::default();
    assert!((empty.success_rate() - 1.0).abs() < f64::EPSILON);

    let partial = DafnyStatistics {
        vcs_total: 10,
        vcs_proved: 7,
        ..Default::default()
    };
    assert!((partial.success_rate() - 0.7).abs() < f64::EPSILON);
}

#[test]
fn test_dafny_statistics_serde_round_trip() {
    use crate::progverif::dafny::DafnyStatistics;

    let stats = DafnyStatistics {
        vcs_total: 10,
        vcs_proved: 8,
        axioms_used: 3,
        methods_verified: 5,
        methods_with_errors: 1,
        solver_time_ms: 1500,
    };
    let json = serde_json::to_string(&stats).expect("serialize");
    let restored: DafnyStatistics = serde_json::from_str(&json).expect("deserialize");
    assert_eq!(restored, stats);
}

#[test]
fn test_dafny_proof_obligation_serde_round_trip() {
    use crate::progverif::dafny::{DafnyPoKind, DafnyProofObligation};

    let po = DafnyProofObligation {
        id: "po_42".to_string(),
        kind: DafnyPoKind::LoopInvariant,
        method_name: "BinarySearch".to_string(),
        source_file: Some("search.dfy".to_string()),
        source_line: Some(100),
        source_column: None,
        assertion: "(assert (and (<= lo hi) (>= hi 0)))".to_string(),
        discharged: false,
    };
    let json = serde_json::to_string(&po).expect("serialize");
    let restored: DafnyProofObligation = serde_json::from_str(&json).expect("deserialize");
    assert_eq!(restored, po);
}

// ===========================================================================
// Why3 importer integration
// ===========================================================================

#[test]
fn test_why3_importer_parses_session() {
    use crate::progverif::why3::Why3Importer;

    let session_xml = r#"<?xml version="1.0" encoding="UTF-8"?>
<why3session>
  <file name="sorting.mlw">
    <theory name="SelectionSort">
      <goal name="sorted_post" expl="postcondition" proved="true">
        <proof prover="Z3" time="0.10">
          <result status="valid"/>
        </proof>
      </goal>
      <goal name="permut_post" expl="postcondition" proved="true">
        <proof prover="CVC5" time="0.25">
          <result status="valid"/>
        </proof>
      </goal>
    </theory>
  </file>
</why3session>"#;

    let importer = Why3Importer::new();
    let session = importer
        .import_session(session_xml)
        .expect("should parse session");
    assert_eq!(session.theory_name, "SelectionSort");
    assert_eq!(session.goals.len(), 2);
    assert!(session.goals.iter().all(|g| g.proved));
    assert_eq!(session.file_name.as_deref(), Some("sorting.mlw"));
}

#[test]
fn test_why3_importer_empty_input_returns_error() {
    use crate::progverif::why3::Why3Importer;
    let importer = Why3Importer::new();
    assert!(importer.import_session("").is_err());
}

#[test]
fn test_why3_importer_no_theory_returns_error() {
    use crate::progverif::why3::Why3Importer;
    let importer = Why3Importer::new();
    assert!(importer
        .import_session("<why3session></why3session>")
        .is_err());
}

#[test]
fn test_why3_import_result_partial_verification() {
    use crate::progverif::why3::Why3Importer;

    let session_xml = r#"<?xml version="1.0"?>
<why3session>
  <file name="test.mlw">
    <theory name="T">
      <goal name="g1" expl="vc1" proved="true">
        <proof prover="Z3" time="0.01"><result status="valid"/></proof>
      </goal>
      <goal name="g2" expl="vc2" proved="false">
        <proof prover="Z3" time="5.0"><result status="unknown"/></proof>
      </goal>
    </theory>
  </file>
</why3session>"#;

    let importer = Why3Importer::new();
    let session = importer.import_session(session_xml).unwrap();
    let result = importer.import_result(&session);

    assert_eq!(result.goal_count, 2);
    assert_eq!(result.proved_count, 1);
    assert_eq!(result.axiom_profile, AxiomProfile::SMT_ORACLE);
    assert_eq!(result.trust_level, TrustLevel::TrustedOracle);
    assert_eq!(result.provenance.source, SourceSystem::Why3);
}

#[test]
fn test_why3_importer_has_default() {
    use crate::progverif::why3::Why3Importer;
    let _importer = Why3Importer::default();
}

#[test]
fn test_why3_parse_session_xml_standalone() {
    use crate::progverif::why3::parse_why3_session_xml;

    let session_xml = r#"<why3session><file name="f.mlw"><theory name="T">
      <goal name="g" expl="test" proved="true">
        <proof prover="Z3" time="0.01"><result status="valid"/></proof>
      </goal></theory></file></why3session>"#;

    let session = parse_why3_session_xml(session_xml).unwrap();
    assert_eq!(session.theory_name, "T");
    assert_eq!(session.goals.len(), 1);
}

#[test]
fn test_why3_parse_session_xml_standalone_empty_errors() {
    use crate::progverif::why3::parse_why3_session_xml;
    assert!(parse_why3_session_xml("").is_err());
}

#[test]
fn test_why3_driver_from_prover_name() {
    use crate::progverif::why3::Why3Driver;

    assert_eq!(Why3Driver::from_prover_name("Z3"), Why3Driver::Z3);
    assert_eq!(Why3Driver::from_prover_name("z3"), Why3Driver::Z3);
    assert_eq!(Why3Driver::from_prover_name("CVC5"), Why3Driver::Cvc5);
    assert_eq!(Why3Driver::from_prover_name("cvc4"), Why3Driver::Cvc5);
    assert_eq!(
        Why3Driver::from_prover_name("Alt-Ergo"),
        Why3Driver::AltErgo
    );
    assert_eq!(Why3Driver::from_prover_name("E"), Why3Driver::EProver);
    assert_eq!(Why3Driver::from_prover_name("Vampire"), Why3Driver::Vampire);
    assert_eq!(Why3Driver::from_prover_name("Coq"), Why3Driver::Coq);
    assert_eq!(
        Why3Driver::from_prover_name("Isabelle"),
        Why3Driver::Isabelle
    );
    assert_eq!(
        Why3Driver::from_prover_name("MyProver"),
        Why3Driver::Other("MyProver".to_string())
    );
}

#[test]
fn test_why3_driver_display_names() {
    use crate::progverif::why3::Why3Driver;

    assert_eq!(Why3Driver::Z3.display_name(), "Z3");
    assert_eq!(Why3Driver::Cvc5.display_name(), "CVC5");
    assert_eq!(Why3Driver::AltErgo.display_name(), "Alt-Ergo");
    assert_eq!(Why3Driver::EProver.display_name(), "E");
    assert_eq!(Why3Driver::Vampire.display_name(), "Vampire");
}

#[test]
fn test_why3_goal_statistics_success_rate() {
    use crate::progverif::why3::Why3GoalStatistics;

    let empty = Why3GoalStatistics::default();
    assert!((empty.success_rate() - 1.0).abs() < f64::EPSILON);

    let partial = Why3GoalStatistics {
        total_goals: 10,
        proved_goals: 7,
        ..Default::default()
    };
    assert!((partial.success_rate() - 0.7).abs() < f64::EPSILON);
}

#[test]
fn test_why3_goal_statistics_serde_round_trip() {
    use crate::progverif::why3::Why3GoalStatistics;

    let stats = Why3GoalStatistics {
        total_goals: 5,
        proved_goals: 3,
        smt_proved: 2,
        atp_proved: 1,
        interactive_proved: 0,
        total_proof_time_ms: 500,
        max_proof_time_ms: 200,
    };
    let json = serde_json::to_string(&stats).expect("serialize");
    let restored: Why3GoalStatistics = serde_json::from_str(&json).expect("deserialize");
    assert_eq!(restored, stats);
}

// ===========================================================================
// PVS importer integration
// ===========================================================================

#[test]
fn test_pvs_importer_parses_theory() {
    use crate::progverif::pvs::PvsImporter;

    let theory_text = "\
Theory: reals_ordering
Lemma: triangle_ineq | proved: true | strategy: grind
Lemma: abs_nonneg | proved: true | strategy: assert
Imports: reals";
    let importer = PvsImporter::new();
    let theory = importer
        .import_theory(theory_text)
        .expect("should parse PVS theory");
    assert_eq!(theory.name, "reals_ordering");
    assert_eq!(theory.lemmas.len(), 2);
    assert!(theory.lemmas.iter().all(|l| l.proved));
    assert_eq!(theory.imports.len(), 1);
}

#[test]
fn test_pvs_importer_empty_input_returns_error() {
    use crate::progverif::pvs::PvsImporter;
    let importer = PvsImporter::new();
    assert!(importer.import_theory("").is_err());
}

#[test]
fn test_pvs_importer_whitespace_only_returns_error() {
    use crate::progverif::pvs::PvsImporter;
    let importer = PvsImporter::new();
    assert!(importer.import_theory("   \n   ").is_err());
}

#[test]
fn test_pvs_importer_has_default() {
    use crate::progverif::pvs::PvsImporter;
    let _importer = PvsImporter::default();
}

#[test]
fn test_pvs_import_result_source_system() {
    use crate::progverif::pvs::PvsImporter;

    let theory_text = "Theory: t\nLemma: l | proved: true | strategy: assert";
    let importer = PvsImporter::new();
    let theory = importer.import_theory(theory_text).unwrap();
    let result = importer.import_result(&theory);
    assert_eq!(result.provenance.source, SourceSystem::Pvs);
}

// ===========================================================================
// ACL2 importer integration
// ===========================================================================

#[test]
fn test_acl2_importer_parses_book() {
    use crate::progverif::acl2::Acl2Importer;

    let book_text = r#"(in-package "ACL2")
(defthm append-assoc (equal (append (append x y) z) (append x (append y z))))
(defun rev (x) (if (endp x) nil (append (rev (cdr x)) (list (car x)))))
"#;
    let importer = Acl2Importer::new();
    let book = importer
        .import_book(book_text)
        .expect("should parse ACL2 book");
    assert!(!book.events.is_empty());
}

#[test]
fn test_acl2_importer_empty_input_returns_error() {
    use crate::progverif::acl2::Acl2Importer;
    let importer = Acl2Importer::new();
    assert!(importer.import_book("").is_err());
}

#[test]
fn test_acl2_importer_whitespace_only_returns_error() {
    use crate::progverif::acl2::Acl2Importer;
    let importer = Acl2Importer::new();
    assert!(importer.import_book("   \n  ").is_err());
}

#[test]
fn test_acl2_importer_has_default() {
    use crate::progverif::acl2::Acl2Importer;
    let _importer = Acl2Importer::default();
}

#[test]
fn test_acl2_import_result_source_system() {
    use crate::progverif::acl2::Acl2Importer;

    let book_text = "(defthm trivial (equal x x))";
    let importer = Acl2Importer::new();
    let book = importer.import_book(book_text).unwrap();
    let result = importer.import_result(&book);
    assert_eq!(result.provenance.source, SourceSystem::Acl2);
}

// ===========================================================================
// Nuprl importer integration
// ===========================================================================

#[test]
fn test_nuprl_importer_parses_library() {
    use crate::progverif::nuprl::NuprlImporter;

    let lib_text = "\
LIBRARY core_algebra
PROVED add_comm : ∀x,y. x+y = y+x ∈ T
PROVED mul_assoc : ∀x,y,z. (x*y)*z = x*(y*z) ∈ T
INCOMPLETE div_well_def : ∀x,y. y≠0 → x/y ∈ T
";
    let importer = NuprlImporter::new();
    let lib = importer
        .import_library(lib_text)
        .expect("should parse Nuprl library");
    assert_eq!(lib.name, "core_algebra");
    assert_eq!(lib.declarations.len(), 3);
}

#[test]
fn test_nuprl_importer_empty_input_returns_error() {
    use crate::progverif::nuprl::NuprlImporter;
    let importer = NuprlImporter::new();
    assert!(importer.import_library("").is_err());
}

#[test]
fn test_nuprl_importer_whitespace_only_returns_error() {
    use crate::progverif::nuprl::NuprlImporter;
    let importer = NuprlImporter::new();
    assert!(importer.import_library("  \n  ").is_err());
}

#[test]
fn test_nuprl_importer_has_default() {
    use crate::progverif::nuprl::NuprlImporter;
    let _importer = NuprlImporter::default();
}

#[test]
fn test_nuprl_import_result_source_system() {
    use crate::progverif::nuprl::NuprlImporter;

    let lib_text = "LIBRARY test\nPROVED t : T ∈ U\n";
    let importer = NuprlImporter::new();
    let lib = importer.import_library(lib_text).unwrap();
    let result = importer.import_result(&lib);
    assert_eq!(result.provenance.source, SourceSystem::Nuprl);
}

// ===========================================================================
// Liquid Haskell importer integration
// ===========================================================================

#[test]
fn test_lh_importer_parses_module() {
    use crate::progverif::liquid_haskell::LhImporter;

    let module_text = r#"module Data.SafeList where
import Data.List
{-@ length :: xs:[a] -> {v:Int | v >= 0} @-}
{-@ head :: {v:[a] | len v > 0} -> a @-}
"#;
    let importer = LhImporter::new();
    let module = importer
        .import_module(module_text)
        .expect("should parse LH module");
    assert_eq!(module.name, "Data.SafeList");
    assert_eq!(module.refinements.len(), 2);
    assert_eq!(module.imports.len(), 1);
}

#[test]
fn test_lh_importer_empty_input_returns_error() {
    use crate::progverif::liquid_haskell::LhImporter;
    let importer = LhImporter::new();
    assert!(importer.import_module("").is_err());
}

#[test]
fn test_lh_importer_whitespace_only_returns_error() {
    use crate::progverif::liquid_haskell::LhImporter;
    let importer = LhImporter::new();
    assert!(importer.import_module("  \n  ").is_err());
}

#[test]
fn test_lh_import_result_smt_oracle_profile() {
    use crate::progverif::liquid_haskell::LhImporter;

    let module_text = "module T where\n{-@ f :: {v:Int | v > 0} @-}\n";
    let importer = LhImporter::new();
    let module = importer.import_module(module_text).unwrap();
    let result = importer.import_result(&module);

    assert!(result.axiom_profile.contains(AxiomProfile::SMT_ORACLE));
    assert_eq!(result.provenance.source, SourceSystem::LiquidHaskell);
}

#[test]
fn test_lh_importer_has_default() {
    use crate::progverif::liquid_haskell::LhImporter;
    let _importer = LhImporter::default();
}

#[test]
fn test_lh_parse_liquid_fixpoint_single_constraint() {
    use crate::progverif::liquid_haskell::parse_liquid_fixpoint;

    let text = "constraint:\n  id 1\n  env [x : Int]\n  lhs {v:Int | v > 0}\n  rhs {v:Int | v >= 0}\n  tag \"Main.hs:10:5\"\n";
    let constraints = parse_liquid_fixpoint(text).expect("should parse");
    assert_eq!(constraints.len(), 1);
    assert_eq!(constraints[0].id, 1);
    assert_eq!(constraints[0].source_tag.as_deref(), Some("Main.hs:10:5"));
}

#[test]
fn test_lh_parse_liquid_fixpoint_multiple_constraints() {
    use crate::progverif::liquid_haskell::parse_liquid_fixpoint;

    let text = "constraint:\n  id 1\n  lhs A\n  rhs B\nconstraint:\n  id 2\n  lhs C\n  rhs D\n";
    let constraints = parse_liquid_fixpoint(text).expect("should parse");
    assert_eq!(constraints.len(), 2);
    assert_eq!(constraints[0].id, 1);
    assert_eq!(constraints[1].id, 2);
}

#[test]
fn test_lh_parse_liquid_fixpoint_empty_returns_error() {
    use crate::progverif::liquid_haskell::parse_liquid_fixpoint;
    assert!(parse_liquid_fixpoint("").is_err());
}

#[test]
fn test_lh_statistics_verification_rate() {
    use crate::progverif::liquid_haskell::LhStatistics;

    let empty = LhStatistics::default();
    assert!((empty.verification_rate() - 1.0).abs() < f64::EPSILON);

    let partial = LhStatistics {
        refinements_total: 10,
        refinements_verified: 8,
        ..Default::default()
    };
    assert!((partial.verification_rate() - 0.8).abs() < f64::EPSILON);
}

#[test]
fn test_lh_constraint_serde_round_trip() {
    use crate::progverif::liquid_haskell::LhConstraint;

    let constraint = LhConstraint {
        id: 42,
        environment: vec![("x".to_owned(), "Int".to_owned())],
        lhs: "{v:Int | v > x}".to_owned(),
        rhs: "{v:Int | v >= 0}".to_owned(),
        source_tag: None,
        satisfiable: false,
    };
    let json = serde_json::to_string(&constraint).expect("serialize");
    let restored: LhConstraint = serde_json::from_str(&json).expect("deserialize");
    assert_eq!(restored, constraint);
}

#[test]
fn test_lh_statistics_serde_round_trip() {
    use crate::progverif::liquid_haskell::LhStatistics;

    let stats = LhStatistics {
        refinements_total: 5,
        refinements_verified: 3,
        constraints_total: 10,
        constraints_satisfiable: 8,
        imports_count: 2,
        solver_time_ms: 150,
    };
    let json = serde_json::to_string(&stats).expect("serialize");
    let restored: LhStatistics = serde_json::from_str(&json).expect("deserialize");
    assert_eq!(restored, stats);
}

// ===========================================================================
// KeY / Frama-C / SPARK importer integration
// ===========================================================================

#[test]
fn test_key_framac_spark_importer_key_bundle() {
    use crate::progverif::key_framac_spark::{KeYFramaCSparkImporter, VerificationTool};

    let bundle_text =
        "TOOL KeY\nPROGRAM BankAccount\nCONTRACT deposit pre BankAccount.java 42 true 3\n";
    let importer = KeYFramaCSparkImporter::new();
    let bundle = importer
        .import_bundle(bundle_text)
        .expect("should parse KeY bundle");
    assert_eq!(bundle.tool, VerificationTool::KeY);
    assert_eq!(bundle.program_name, "BankAccount");
    assert_eq!(bundle.contracts.len(), 1);
}

#[test]
fn test_key_framac_spark_importer_framac_bundle() {
    use crate::progverif::key_framac_spark::{
        ContractKind, KeYFramaCSparkImporter, VerificationTool,
    };

    let bundle_text = "\
TOOL FramaC
PROGRAM binary_search
CONTRACT pre_check requires search.c 15 true 2
CONTRACT post_check ensures search.c 16 true 4
CONTRACT loop_inv invariant search.c 20 false 3
";
    let importer = KeYFramaCSparkImporter::new();
    let bundle = importer
        .import_bundle(bundle_text)
        .expect("should parse Frama-C bundle");
    assert_eq!(bundle.tool, VerificationTool::FramaC);
    assert_eq!(bundle.contracts.len(), 3);
    let unverified: Vec<_> = bundle.contracts.iter().filter(|c| !c.verified).collect();
    assert_eq!(unverified.len(), 1);
    assert_eq!(unverified[0].kind, ContractKind::Invariant);
}

#[test]
fn test_key_framac_spark_importer_spark_bundle() {
    use crate::progverif::key_framac_spark::{KeYFramaCSparkImporter, VerificationTool};

    let bundle_text = "TOOL SPARK\nPROGRAM Stack\nCONTRACT push_pre pre stack.ads 30 true 1\n";
    let importer = KeYFramaCSparkImporter::new();
    let bundle = importer
        .import_bundle(bundle_text)
        .expect("should parse SPARK bundle");
    assert_eq!(bundle.tool, VerificationTool::Spark);
}

#[test]
fn test_key_framac_spark_importer_empty_input_returns_error() {
    use crate::progverif::key_framac_spark::KeYFramaCSparkImporter;
    let importer = KeYFramaCSparkImporter::new();
    assert!(importer.import_bundle("").is_err());
}

#[test]
fn test_key_framac_spark_importer_whitespace_only_returns_error() {
    use crate::progverif::key_framac_spark::KeYFramaCSparkImporter;
    let importer = KeYFramaCSparkImporter::new();
    assert!(importer.import_bundle("   \n  ").is_err());
}

#[test]
fn test_key_framac_spark_import_result_source_system() {
    use crate::progverif::key_framac_spark::KeYFramaCSparkImporter;

    let bundle_text = "TOOL KeY\nPROGRAM T\nCONTRACT c pre f.java 1 true 1\n";
    let importer = KeYFramaCSparkImporter::new();
    let bundle = importer.import_bundle(bundle_text).unwrap();
    let result = importer.import_result(&bundle);
    assert_eq!(result.provenance.source, SourceSystem::KeyFramacSpark);
}

#[test]
fn test_key_framac_spark_importer_has_default() {
    use crate::progverif::key_framac_spark::KeYFramaCSparkImporter;
    let _importer = KeYFramaCSparkImporter::default();
}

#[test]
fn test_key_framac_spark_unsupported_tool_returns_error() {
    use crate::progverif::key_framac_spark::KeYFramaCSparkImporter;
    let importer = KeYFramaCSparkImporter::new();
    let result = importer.import_bundle("TOOL UnknownVerifier\nPROGRAM test\n");
    assert!(result.is_err());
}

#[test]
fn test_jml_importer_extracts_annotations() {
    use crate::progverif::key_framac_spark::{AnnotationKind, ContractKind, JmlImporter};

    let source = "//@ requires balance >= 0;\n//@ ensures \\result >= 0;\n";
    let mut jml = JmlImporter::new();
    jml.extract_annotations(source, "Account.java");

    assert_eq!(jml.annotation_count(), 2);
    let annots = jml.annotations();
    assert_eq!(annots[0].kind, AnnotationKind::Jml);
    assert_eq!(annots[0].contract_kind, ContractKind::Precondition);
    assert_eq!(annots[1].contract_kind, ContractKind::Postcondition);
}

#[test]
fn test_acsl_importer_extracts_annotations() {
    use crate::progverif::key_framac_spark::{AcslImporter, AnnotationKind, ContractKind};

    let source = "/*@ requires n > 0; */\n/*@ ensures \\result >= 0; */\n";
    let mut acsl = AcslImporter::new();
    acsl.extract_annotations(source, "abs.c");

    assert_eq!(acsl.annotation_count(), 2);
    assert_eq!(acsl.annotations()[0].kind, AnnotationKind::Acsl);
    assert_eq!(
        acsl.annotations()[0].contract_kind,
        ContractKind::Precondition
    );
    assert_eq!(
        acsl.annotations()[1].contract_kind,
        ContractKind::Postcondition
    );
}

#[test]
fn test_spark_importer_extracts_annotations() {
    use crate::progverif::key_framac_spark::{AnnotationKind, ContractKind, SparkImporter};

    let source = "with Pre => not Is_Full(S),\n     Post => Top(S) = E;\n";
    let mut spark = SparkImporter::new();
    spark.extract_annotations(source, "stack.ads");

    assert_eq!(spark.annotation_count(), 2);
    assert_eq!(spark.annotations()[0].kind, AnnotationKind::Spark);
    assert_eq!(
        spark.annotations()[0].contract_kind,
        ContractKind::Precondition
    );
    assert_eq!(
        spark.annotations()[1].contract_kind,
        ContractKind::Postcondition
    );
}

#[test]
fn test_annotation_kind_display_names() {
    use crate::progverif::key_framac_spark::AnnotationKind;
    assert_eq!(AnnotationKind::Jml.display_name(), "JML");
    assert_eq!(AnnotationKind::Acsl.display_name(), "ACSL");
    assert_eq!(AnnotationKind::Spark.display_name(), "SPARK");
}

#[test]
fn test_annotation_kind_tool_mapping() {
    use crate::progverif::key_framac_spark::{AnnotationKind, VerificationTool};
    assert_eq!(AnnotationKind::Jml.tool(), VerificationTool::KeY);
    assert_eq!(AnnotationKind::Acsl.tool(), VerificationTool::FramaC);
    assert_eq!(AnnotationKind::Spark.tool(), VerificationTool::Spark);
}

#[test]
fn test_annotation_kind_serde_round_trip() {
    use crate::progverif::key_framac_spark::AnnotationKind;
    for kind in &[
        AnnotationKind::Jml,
        AnnotationKind::Acsl,
        AnnotationKind::Spark,
    ] {
        let json = serde_json::to_string(kind).expect("serialize");
        let restored: AnnotationKind = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(&restored, kind);
    }
}

// ===========================================================================
// F* importer integration
// ===========================================================================

#[test]
fn test_fstar_importer_parses_module() {
    use crate::progverif::fstar::FStarImporter;

    let module_text = "\
(* Module: FStar.Buffer *)
(* val: create : Type -> UInt32 -> a -> Tot (buffer a) verified *)
(* let: create Tot verified *)
(* effect: ST Tot *)
";
    let importer = FStarImporter::new();
    let module = importer
        .import_module(module_text)
        .expect("should parse F* module");
    assert_eq!(module.name, "FStar.Buffer");
}

#[test]
fn test_fstar_importer_empty_input_returns_error() {
    use crate::progverif::fstar::FStarImporter;
    let importer = FStarImporter::new();
    assert!(importer.import_module("").is_err());
}

#[test]
fn test_fstar_importer_whitespace_only_returns_error() {
    use crate::progverif::fstar::FStarImporter;
    let importer = FStarImporter::new();
    assert!(importer.import_module("  \n  ").is_err());
}

#[test]
fn test_fstar_import_result_extensionality_profile() {
    use crate::progverif::fstar::FStarImporter;

    let module_text =
        "(* Module: T *)\n(* val: f : int -> Tot int verified *)\n(* let: f Tot verified *)\n";
    let importer = FStarImporter::new();
    let module = importer.import_module(module_text).unwrap();
    let result = importer.import_result(&module);

    assert_eq!(result.provenance.source, SourceSystem::FStar);
    // F* always has EXTENSIONALITY in its axiom profile.
    assert!(result.axiom_profile.contains(AxiomProfile::EXTENSIONALITY));
}

#[test]
fn test_fstar_importer_has_default() {
    use crate::progverif::fstar::FStarImporter;
    let _importer = FStarImporter::default();
}

#[test]
fn test_fstar_importer_cert_replay_toggle() {
    use crate::progverif::fstar::FStarImporter;

    let importer = FStarImporter::new().with_cert_replay(true);
    let module_text =
        "(* Module: T *)\n(* val: f : int -> Tot int verified *)\n(* let: f Tot verified *)\n";
    let module = importer.import_module(module_text).unwrap();
    let result = importer.import_result(&module);
    // With cert replay enabled and all verified, trust should be CertificateReplayed.
    assert_eq!(result.trust_level, TrustLevel::CertificateReplayed);
}

// ===========================================================================
// Metamath importer integration
// ===========================================================================

#[test]
fn test_metamath_importer_parses_database() {
    use crate::progverif::metamath::MetamathImporter;

    let db_text = "\
$c wff $.
$c |- $.
$v ph $.
$v ps $.
ax-1 $a |- ( ph -> ( ps -> ph ) ) $.
ax-mp $a |- ( ph -> ps ) $.
mp2 $p |- ps $= ax-1 ax-mp $.
";
    let importer = MetamathImporter::new();
    let db = importer
        .import_database(db_text)
        .expect("should parse Metamath database");
    assert!(!db.name.is_empty());
    assert!(db.statement_count() > 0);
}

#[test]
fn test_metamath_importer_empty_input_returns_error() {
    use crate::progverif::metamath::MetamathImporter;
    let importer = MetamathImporter::new();
    assert!(importer.import_database("").is_err());
}

#[test]
fn test_metamath_importer_whitespace_only_returns_error() {
    use crate::progverif::metamath::MetamathImporter;
    let importer = MetamathImporter::new();
    assert!(importer.import_database("  \n  ").is_err());
}

#[test]
fn test_metamath_import_result_source_system() {
    use crate::progverif::metamath::MetamathImporter;

    let db_text = "ax-1 $a |- ph $.";
    let importer = MetamathImporter::new();
    let db = importer.import_database(db_text).unwrap();
    let result = importer.import_result(&db);
    assert_eq!(result.provenance.source, SourceSystem::Metamath);
}

#[test]
fn test_metamath_importer_has_default() {
    use crate::progverif::metamath::MetamathImporter;
    let _importer = MetamathImporter::default();
}

// ===========================================================================
// Cross-importer consistency tests
// ===========================================================================

#[test]
fn test_all_importers_reject_empty_input() {
    use crate::progverif::acl2::Acl2Importer;
    use crate::progverif::dafny::DafnyImporter;
    use crate::progverif::fstar::FStarImporter;
    use crate::progverif::key_framac_spark::KeYFramaCSparkImporter;
    use crate::progverif::liquid_haskell::LhImporter;
    use crate::progverif::metamath::MetamathImporter;
    use crate::progverif::nuprl::NuprlImporter;
    use crate::progverif::pvs::PvsImporter;
    use crate::progverif::why3::Why3Importer;

    assert!(DafnyImporter::new().import_boogie_vc("").is_err());
    assert!(Why3Importer::new().import_session("").is_err());
    assert!(PvsImporter::new().import_theory("").is_err());
    assert!(Acl2Importer::new().import_book("").is_err());
    assert!(NuprlImporter::new().import_library("").is_err());
    assert!(LhImporter::new().import_module("").is_err());
    assert!(KeYFramaCSparkImporter::new().import_bundle("").is_err());
    assert!(FStarImporter::new().import_module("").is_err());
    assert!(MetamathImporter::new().import_database("").is_err());
}

#[test]
fn test_all_importers_reject_whitespace_only() {
    use crate::progverif::acl2::Acl2Importer;
    use crate::progverif::dafny::DafnyImporter;
    use crate::progverif::fstar::FStarImporter;
    use crate::progverif::key_framac_spark::KeYFramaCSparkImporter;
    use crate::progverif::liquid_haskell::LhImporter;
    use crate::progverif::metamath::MetamathImporter;
    use crate::progverif::nuprl::NuprlImporter;
    use crate::progverif::pvs::PvsImporter;
    use crate::progverif::why3::Why3Importer;

    let whitespace = "   \n  \t  ";
    assert!(DafnyImporter::new().import_boogie_vc(whitespace).is_err());
    assert!(Why3Importer::new().import_session(whitespace).is_err());
    assert!(PvsImporter::new().import_theory(whitespace).is_err());
    assert!(Acl2Importer::new().import_book(whitespace).is_err());
    assert!(NuprlImporter::new().import_library(whitespace).is_err());
    assert!(LhImporter::new().import_module(whitespace).is_err());
    assert!(KeYFramaCSparkImporter::new()
        .import_bundle(whitespace)
        .is_err());
    assert!(FStarImporter::new().import_module(whitespace).is_err());
    assert!(MetamathImporter::new().import_database(whitespace).is_err());
}

#[test]
fn test_all_importers_have_default_impl() {
    use crate::progverif::acl2::Acl2Importer;
    use crate::progverif::dafny::DafnyImporter;
    use crate::progverif::fstar::FStarImporter;
    use crate::progverif::key_framac_spark::KeYFramaCSparkImporter;
    use crate::progverif::liquid_haskell::LhImporter;
    use crate::progverif::metamath::MetamathImporter;
    use crate::progverif::nuprl::NuprlImporter;
    use crate::progverif::pvs::PvsImporter;
    use crate::progverif::why3::Why3Importer;

    let _dafny = DafnyImporter::default();
    let _why3 = Why3Importer::default();
    let _pvs = PvsImporter::default();
    let _acl2 = Acl2Importer::default();
    let _nuprl = NuprlImporter::default();
    let _lh = LhImporter::default();
    let _kfs = KeYFramaCSparkImporter::default();
    let _fstar = FStarImporter::default();
    let _mm = MetamathImporter::default();
}

#[test]
fn test_source_system_consistency_across_importers() {
    use crate::progverif::acl2::Acl2Importer;
    use crate::progverif::dafny::DafnyImporter;
    use crate::progverif::fstar::FStarImporter;
    use crate::progverif::key_framac_spark::KeYFramaCSparkImporter;
    use crate::progverif::liquid_haskell::LhImporter;
    use crate::progverif::metamath::MetamathImporter;
    use crate::progverif::nuprl::NuprlImporter;
    use crate::progverif::pvs::PvsImporter;
    use crate::progverif::why3::Why3Importer;

    // Verify each importer reports the correct SourceSystem in its provenance.
    let dafny_vc = DafnyImporter::new()
        .import_boogie_vc(";; VC: t\n;; Method: m\n(assert true)")
        .unwrap();
    let dafny_result = DafnyImporter::new().import_dafny_result("m", &[dafny_vc], true);
    assert_eq!(dafny_result.provenance.source, SourceSystem::Dafny);

    let why3_session = Why3Importer::new()
        .import_session(
            r#"<why3session><file name="f.mlw"><theory name="T">
        <goal name="g" expl="e" proved="true">
        <proof prover="Z3" time="0.01"><result status="valid"/></proof>
        </goal></theory></file></why3session>"#,
        )
        .unwrap();
    let why3_result = Why3Importer::new().import_result(&why3_session);
    assert_eq!(why3_result.provenance.source, SourceSystem::Why3);

    let pvs_theory = PvsImporter::new()
        .import_theory("Theory: t\nLemma: l | proved: true | strategy: assert")
        .unwrap();
    let pvs_result = PvsImporter::new().import_result(&pvs_theory);
    assert_eq!(pvs_result.provenance.source, SourceSystem::Pvs);

    let acl2_book = Acl2Importer::new()
        .import_book("(defthm t (equal x x))")
        .unwrap();
    let acl2_result = Acl2Importer::new().import_result(&acl2_book);
    assert_eq!(acl2_result.provenance.source, SourceSystem::Acl2);

    let nuprl_lib = NuprlImporter::new()
        .import_library("LIBRARY l\nPROVED d : T ∈ U\n")
        .unwrap();
    let nuprl_result = NuprlImporter::new().import_result(&nuprl_lib);
    assert_eq!(nuprl_result.provenance.source, SourceSystem::Nuprl);

    let lh_module = LhImporter::new()
        .import_module("module M where\n{-@ f :: {v:Int | v > 0} @-}\n")
        .unwrap();
    let lh_result = LhImporter::new().import_result(&lh_module);
    assert_eq!(lh_result.provenance.source, SourceSystem::LiquidHaskell);

    let kfs_bundle = KeYFramaCSparkImporter::new()
        .import_bundle("TOOL KeY\nPROGRAM P\nCONTRACT c pre f.java 1 true 1\n")
        .unwrap();
    let kfs_result = KeYFramaCSparkImporter::new().import_result(&kfs_bundle);
    assert_eq!(kfs_result.provenance.source, SourceSystem::KeyFramacSpark);

    let fstar_module = FStarImporter::new()
        .import_module(
            "(* Module: T *)\n(* val: f : int -> Tot int verified *)\n(* let: f Tot verified *)\n",
        )
        .unwrap();
    let fstar_result = FStarImporter::new().import_result(&fstar_module);
    assert_eq!(fstar_result.provenance.source, SourceSystem::FStar);

    let mm_db = MetamathImporter::new()
        .import_database("ax-1 $a |- ph $.")
        .unwrap();
    let mm_result = MetamathImporter::new().import_result(&mm_db);
    assert_eq!(mm_result.provenance.source, SourceSystem::Metamath);
}

// ===========================================================================
// Edge cases
// ===========================================================================

#[test]
fn test_smt_literal_variants() {
    let bool_t = SmtLiteral::Bool(true);
    let bool_f = SmtLiteral::Bool(false);
    assert_ne!(bool_t, bool_f);

    let int_pos = SmtLiteral::Int(42);
    let int_neg = SmtLiteral::Int(-42);
    let int_zero = SmtLiteral::Int(0);
    assert_ne!(int_pos, int_neg);
    assert_ne!(int_pos, int_zero);

    let bv1 = SmtLiteral::BitVec(255, 8);
    let bv2 = SmtLiteral::BitVec(255, 16);
    assert_ne!(bv1, bv2); // Same value, different width

    let str1 = SmtLiteral::String("hello".to_string());
    let str2 = SmtLiteral::String("world".to_string());
    assert_ne!(str1, str2);
}

#[test]
fn test_smt_sort_equality() {
    assert_eq!(SmtSort::Bool, SmtSort::Bool);
    assert_eq!(SmtSort::Int, SmtSort::Int);
    assert_ne!(SmtSort::Bool, SmtSort::Int);
    assert_ne!(SmtSort::BitVec(8), SmtSort::BitVec(16));
    assert_eq!(SmtSort::BitVec(32), SmtSort::BitVec(32));
    assert_eq!(
        SmtSort::array(SmtSort::Int, SmtSort::Bool),
        SmtSort::array(SmtSort::Int, SmtSort::Bool)
    );
    assert_ne!(
        SmtSort::array(SmtSort::Int, SmtSort::Bool),
        SmtSort::array(SmtSort::Bool, SmtSort::Int)
    );
    assert_eq!(SmtSort::uninterpreted("X"), SmtSort::uninterpreted("X"));
    assert_ne!(SmtSort::uninterpreted("X"), SmtSort::uninterpreted("Y"));
}

#[test]
fn test_smt_term_equality() {
    assert_eq!(SmtTerm::var("x"), SmtTerm::var("x"));
    assert_ne!(SmtTerm::var("x"), SmtTerm::var("y"));
    assert_eq!(SmtTerm::bool_(true), SmtTerm::bool_(true));
    assert_ne!(SmtTerm::bool_(true), SmtTerm::bool_(false));
    assert_eq!(SmtTerm::int(0), SmtTerm::int(0));
    assert_ne!(SmtTerm::int(0), SmtTerm::int(1));
    assert_eq!(
        SmtTerm::app("+", vec![SmtTerm::var("x"), SmtTerm::int(1)]),
        SmtTerm::app("+", vec![SmtTerm::var("x"), SmtTerm::int(1)])
    );
}

#[test]
fn test_certificate_metadata_overwriting() {
    let cert = Certificate::new(CertificateFormat::SmtLib2, vec![], "z3")
        .with_metadata("key", "value1")
        .with_metadata("key", "value2");
    assert_eq!(cert.metadata.get("key").map(String::as_str), Some("value2"));
}

#[test]
fn test_axiom_profile_bit_combinations() {
    let classical_smt = AxiomProfile::CLASSICAL | AxiomProfile::SMT_ORACLE;
    assert!(classical_smt.contains(AxiomProfile::CLASSICAL));
    assert!(classical_smt.contains(AxiomProfile::SMT_ORACLE));
    assert!(!classical_smt.contains(AxiomProfile::SAT_CERT));

    let all_certs = AxiomProfile::SAT_CERT | AxiomProfile::ATP_CERT | AxiomProfile::SMT_ORACLE;
    assert!(all_certs.contains(AxiomProfile::SAT_CERT));
    assert!(all_certs.contains(AxiomProfile::ATP_CERT));
    assert!(all_certs.contains(AxiomProfile::SMT_ORACLE));
    assert!(!all_certs.contains(AxiomProfile::EXTENSIONALITY));

    let none = AxiomProfile::NONE;
    assert!(!none.contains(AxiomProfile::CLASSICAL));
    assert!(!none.contains(AxiomProfile::SMT_ORACLE));
}

#[test]
fn test_trust_level_ordering() {
    // KernelVerified < AxiomDependent < CertificateReplayed < PartiallyAxiomatized < TrustedOracle
    assert!(TrustLevel::KernelVerified < TrustLevel::AxiomDependent);
    assert!(TrustLevel::AxiomDependent < TrustLevel::CertificateReplayed);
    assert!(TrustLevel::CertificateReplayed < TrustLevel::PartiallyAxiomatized);
    assert!(TrustLevel::PartiallyAxiomatized < TrustLevel::TrustedOracle);
    assert!(TrustLevel::KernelVerified < TrustLevel::TrustedOracle);
}

#[test]
fn test_quantifier_variants() {
    assert_eq!(Quantifier::ForAll, Quantifier::ForAll);
    assert_eq!(Quantifier::Exists, Quantifier::Exists);
    assert_ne!(Quantifier::ForAll, Quantifier::Exists);
}

#[test]
fn test_smt_bridge_error_variants() {
    let parse_err = SmtBridgeError::ParseError {
        reason: "test".to_string(),
    };
    let logic_err = SmtBridgeError::UnsupportedLogic {
        logic: "QF_UNKNOWN".to_string(),
    };
    let trans_err = SmtBridgeError::TranslationFailed {
        reason: "cannot translate".to_string(),
    };
    // Verify these are all distinct error types via Display.
    let parse_msg = format!("{parse_err}");
    let logic_msg = format!("{logic_err}");
    let trans_msg = format!("{trans_err}");
    assert!(parse_msg.contains("test"));
    assert!(logic_msg.contains("QF_UNKNOWN"));
    assert!(trans_msg.contains("cannot translate"));
}

#[test]
fn test_cert_replay_error_variants() {
    let invalid = CertReplayError::InvalidCert {
        reason: "bad data".to_string(),
    };
    let unsupported = CertReplayError::UnsupportedFormat {
        format: "unknown".to_string(),
    };
    let failed = CertReplayError::VerificationFailed {
        reason: "step mismatch".to_string(),
    };
    let timeout = CertReplayError::ReplayTimeout { timeout_us: 5000 };
    assert!(format!("{invalid}").contains("bad data"));
    assert!(format!("{unsupported}").contains("unknown"));
    assert!(format!("{failed}").contains("step mismatch"));
    assert!(format!("{timeout}").contains("5000"));
}

#[test]
fn test_smt_vc_bundle_assertion_source_line_tracking() {
    let bundle = SmtVcBundle::new("QF_LIA")
        .with_assertion(SmtAssertion {
            name: Some("line_10".into()),
            term: SmtTerm::bool_(true),
            source_line: Some(10),
        })
        .with_assertion(SmtAssertion {
            name: Some("line_20".into()),
            term: SmtTerm::bool_(false),
            source_line: Some(20),
        })
        .with_assertion(SmtAssertion {
            name: None,
            term: SmtTerm::var("x"),
            source_line: None,
        });

    assert_eq!(bundle.assertions[0].source_line, Some(10));
    assert_eq!(bundle.assertions[1].source_line, Some(20));
    assert_eq!(bundle.assertions[2].source_line, None);
    assert_eq!(bundle.assertions[0].name.as_deref(), Some("line_10"));
    assert!(bundle.assertions[2].name.is_none());
}

#[test]
fn test_multiple_replay_strategies_on_same_cert() {
    // A certificate in DRAT format should succeed with DRAT strategy, fail with Alethe.
    let cert = Certificate::new(CertificateFormat::Drat, b"1 2 0\n3 0\n".to_vec(), "cadical");

    let null = NullReplayStrategy;
    let drat = DratReplayStrategy::new();
    let alethe = AletheLfReplayStrategy::new();

    let null_result = null.replay(&cert).expect("null always succeeds");
    assert!(null_result.verified);

    let drat_result = drat.replay(&cert).expect("DRAT should accept DRAT cert");
    assert!(drat_result.verified);
    assert_eq!(drat_result.trust_level, TrustLevel::CertificateReplayed);

    let alethe_result = alethe.replay(&cert);
    assert!(alethe_result.is_err(), "Alethe should reject DRAT cert");
}

#[test]
fn test_certificate_clone_independence() {
    let cert1 = Certificate::new(CertificateFormat::SmtLib2, b"data".to_vec(), "z3")
        .with_metadata("key", "val");
    let cert2 = cert1.clone();

    assert_eq!(cert1.format, cert2.format);
    assert_eq!(cert1.raw_bytes, cert2.raw_bytes);
    assert_eq!(cert1.source_tool, cert2.source_tool);
    assert_eq!(cert1.metadata.get("key"), cert2.metadata.get("key"));
}

#[test]
fn test_smt_vc_bundle_clone_independence() {
    let bundle1 = SmtVcBundle::new("QF_LIA")
        .with_sort(SmtSort::Int)
        .with_assertion(SmtAssertion {
            name: Some("a1".into()),
            term: SmtTerm::bool_(true),
            source_line: None,
        });
    let bundle2 = bundle1.clone();

    assert_eq!(bundle2.logic, "QF_LIA");
    assert_eq!(bundle2.sorts.len(), 1);
    assert_eq!(bundle2.assertion_count(), 1);
}

#[test]
fn test_smt_term_constructors_convenience() {
    let b = SmtTerm::bool_(true);
    assert_eq!(b, SmtTerm::Literal(SmtLiteral::Bool(true)));

    let i = SmtTerm::int(-100);
    assert_eq!(i, SmtTerm::Literal(SmtLiteral::Int(-100)));

    let v = SmtTerm::var("alpha");
    assert_eq!(v, SmtTerm::Var("alpha".to_string()));

    let a = SmtTerm::app("not", vec![SmtTerm::var("p")]);
    match a {
        SmtTerm::App(op, args) => {
            assert_eq!(op, "not");
            assert_eq!(args.len(), 1);
        }
        other => panic!("expected App, got {other:?}"),
    }
}

#[test]
fn test_parse_sort_bitvec_array_combination() {
    // (Array (_ BitVec 32) (_ BitVec 8))
    let result = parse_smtlib2_sort("(Array (_ BitVec 32) (_ BitVec 8))").unwrap();
    let expected = SmtSort::array(SmtSort::BitVec(32), SmtSort::BitVec(8));
    assert_eq!(result, expected);
}

#[test]
fn test_parse_term_three_arg_app() {
    let result = parse_smtlib2_term("(ite (> x 0) x (- x))").unwrap();
    match result {
        SmtTerm::App(op, args) => {
            assert_eq!(op, "ite");
            assert_eq!(args.len(), 3);
        }
        other => panic!("expected 3-arg App, got {other:?}"),
    }
}

#[test]
fn test_parse_term_nested_let_in_quantifier() {
    let input = "(forall ((x Int)) (let ((y (+ x 1))) (>= y 0)))";
    let result = parse_smtlib2_term(input).unwrap();
    match result {
        SmtTerm::Quant(Quantifier::ForAll, vars, body) => {
            assert_eq!(vars.len(), 1);
            assert_eq!(vars[0].0, "x");
            match *body {
                SmtTerm::Let(ref bindings, _) => {
                    assert_eq!(bindings.len(), 1);
                    assert_eq!(bindings[0].0, "y");
                }
                ref other => panic!("expected Let body, got {other:?}"),
            }
        }
        other => panic!("expected Quant, got {other:?}"),
    }
}

#[test]
fn test_verification_tool_display_names() {
    use crate::progverif::key_framac_spark::VerificationTool;

    assert_eq!(VerificationTool::KeY.display_name(), "KeY");
    assert_eq!(VerificationTool::FramaC.display_name(), "Frama-C");
    assert_eq!(VerificationTool::Spark.display_name(), "SPARK/GNATprove");
}

#[test]
fn test_dafny_statistics_from_vcs() {
    use crate::progverif::dafny::{DafnyImporter, DafnyStatistics};

    let importer = DafnyImporter::new();
    let vc1 = importer
        .import_boogie_vc(";; VC: v1\n;; Method: A\n(assert true)")
        .unwrap();
    let vc2 = importer
        .import_boogie_vc(";; VC: v2\n;; Method: B\n(assert false)")
        .unwrap();
    let vc3 = importer
        .import_boogie_vc(";; VC: v3\n;; Method: A\n(assert (= x x))")
        .unwrap();

    let stats = DafnyStatistics::from_vcs(&[vc1, vc2, vc3], true, 7);
    assert_eq!(stats.vcs_total, 3);
    assert_eq!(stats.vcs_proved, 3);
    assert_eq!(stats.axioms_used, 7);
    assert_eq!(stats.methods_verified, 2); // A, B (dedup)
    assert_eq!(stats.methods_with_errors, 0);
}

#[test]
fn test_why3_goal_statistics_from_session() {
    use crate::progverif::why3::{Why3GoalStatistics, Why3Importer};

    let session_xml = r#"<why3session><file name="t.mlw"><theory name="T">
      <goal name="g1" expl="vc" proved="true">
        <proof prover="Z3" time="0.5"><result status="valid"/></proof>
      </goal>
      <goal name="g2" expl="vc" proved="true">
        <proof prover="eprover" time="1.0"><result status="valid"/></proof>
      </goal>
      <goal name="g3" expl="vc" proved="false">
        <proof prover="Z3" time="5.0"><result status="unknown"/></proof>
      </goal>
    </theory></file></why3session>"#;

    let session = Why3Importer::new().import_session(session_xml).unwrap();
    let stats = Why3GoalStatistics::from_session(&session);

    assert_eq!(stats.total_goals, 3);
    assert_eq!(stats.proved_goals, 2);
    assert_eq!(stats.smt_proved, 1); // Z3
    assert_eq!(stats.atp_proved, 1); // eprover
    assert_eq!(stats.interactive_proved, 0);
    assert_eq!(stats.total_proof_time_ms, 500 + 1000 + 5000);
    assert_eq!(stats.max_proof_time_ms, 5000);
}

#[test]
fn test_lh_statistics_from_module_and_constraints() {
    use crate::progverif::liquid_haskell::{LhConstraint, LhImporter, LhStatistics};

    let module_text = "module T where\n{-@ f :: {v:Int | v > 0} @-}\n{-@ g :: Int @-}\n";
    let module = LhImporter::new().import_module(module_text).unwrap();

    let constraints = vec![
        LhConstraint {
            id: 1,
            environment: vec![],
            lhs: "A".to_owned(),
            rhs: "B".to_owned(),
            source_tag: None,
            satisfiable: true,
        },
        LhConstraint {
            id: 2,
            environment: vec![],
            lhs: "C".to_owned(),
            rhs: "D".to_owned(),
            source_tag: None,
            satisfiable: false,
        },
    ];

    let stats = LhStatistics::from_module_and_constraints(&module, &constraints);
    assert_eq!(stats.refinements_total, 2);
    assert_eq!(stats.refinements_verified, 2);
    assert_eq!(stats.constraints_total, 2);
    assert_eq!(stats.constraints_satisfiable, 1);
    assert_eq!(stats.imports_count, 0);
}

#[test]
fn test_sub_importers_empty_source_yields_zero_annotations() {
    use crate::progverif::key_framac_spark::{AcslImporter, JmlImporter, SparkImporter};

    let mut jml = JmlImporter::new();
    jml.extract_annotations("", "empty.java");
    assert_eq!(jml.annotation_count(), 0);

    let mut acsl = AcslImporter::new();
    acsl.extract_annotations("", "empty.c");
    assert_eq!(acsl.annotation_count(), 0);

    let mut spark = SparkImporter::new();
    spark.extract_annotations("", "empty.ads");
    assert_eq!(spark.annotation_count(), 0);
}

#[test]
fn test_sub_importers_no_annotation_patterns_yields_zero() {
    use crate::progverif::key_framac_spark::{AcslImporter, JmlImporter, SparkImporter};

    let java_src = "public class Foo { int x = 5; }";
    let c_src = "int main() { return 0; }";
    let ada_src = "procedure Noop is begin null; end Noop;";

    let mut jml = JmlImporter::new();
    jml.extract_annotations(java_src, "Foo.java");
    assert_eq!(jml.annotation_count(), 0);

    let mut acsl = AcslImporter::new();
    acsl.extract_annotations(c_src, "main.c");
    assert_eq!(acsl.annotation_count(), 0);

    let mut spark = SparkImporter::new();
    spark.extract_annotations(ada_src, "noop.adb");
    assert_eq!(spark.annotation_count(), 0);
}
