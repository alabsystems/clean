// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Fixture-loading smoke tests for external certificates (Part of #1195).
//!
//! These tests load the canonical JSON fixtures from `tests/fixtures/external_certificates/`
//! and verify them through the full deserialization + verification pipeline.
//! They catch schema drift between the shipped fixtures and the code.

use super::*;

fn fixture_path(name: &str) -> std::path::PathBuf {
    let workspace_root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .parent()
        .unwrap();
    workspace_root
        .join("tests/fixtures/external_certificates")
        .join(name)
}

#[test]
fn test_fixture_farkas_loads_and_verifies() {
    let json = std::fs::read_to_string(fixture_path("gamma_crown_farkas_valid.json"))
        .expect("farkas fixture should exist");
    let cert: ExternalCertificate =
        serde_json::from_str(&json).expect("farkas fixture should deserialize");
    match cert {
        ExternalCertificate::Farkas(farkas) => {
            assert_eq!(farkas.version, "1.0");
            assert_eq!(farkas.constraints.len(), 2);
            assert_eq!(farkas.multipliers.len(), 2);
            assert_eq!(farkas.conclusion, "contradiction");
            let residual =
                verify_farkas_certificate(&farkas).expect("farkas fixture should verify");
            assert!(
                residual.is_negative(),
                "valid contradiction should have negative residual, got {residual:?}"
            );
        }
        other => panic!("expected Farkas variant, got {other:?}"),
    }
}

#[test]
fn test_fixture_entailment_loads_and_verifies() {
    let json = std::fs::read_to_string(fixture_path("gamma_crown_entailment_valid.json"))
        .expect("entailment fixture should exist");
    let cert: ExternalCertificate =
        serde_json::from_str(&json).expect("entailment fixture should deserialize");
    match cert {
        ExternalCertificate::Entailment(entailment) => {
            assert_eq!(entailment.version, "1.0");
            assert_eq!(entailment.premises.len(), 1);
            assert_eq!(entailment.multipliers.len(), 1);
            let (premise_bound, conclusion_bound) = verify_entailment_certificate(&entailment)
                .expect("entailment fixture should verify");
            assert!(
                premise_bound <= conclusion_bound,
                "entailment should hold: premise bound {premise_bound:?} <= conclusion bound {conclusion_bound:?}"
            );
        }
        other => panic!("expected Entailment variant, got {other:?}"),
    }
}

#[test]
fn test_fixture_batch_loads_and_verifies_all() {
    let json = std::fs::read_to_string(fixture_path("gamma_crown_batch_valid.json"))
        .expect("batch fixture should exist");
    let certs: Vec<ExternalCertificate> =
        serde_json::from_str(&json).expect("batch fixture should deserialize as Vec");
    assert_eq!(
        certs.len(),
        2,
        "batch fixture should contain exactly 2 certificates"
    );

    for (i, cert) in certs.iter().enumerate() {
        match cert {
            ExternalCertificate::Farkas(farkas) => {
                verify_farkas_certificate(farkas)
                    .unwrap_or_else(|e| panic!("batch item {i} (Farkas) should verify: {e}"));
            }
            ExternalCertificate::Entailment(entailment) => {
                verify_entailment_certificate(entailment)
                    .unwrap_or_else(|e| panic!("batch item {i} (Entailment) should verify: {e}"));
            }
            ExternalCertificate::Alethe(_) => {
                // Alethe in batch is a serialization contract; skip verification
            }
        }
    }
}

#[test]
fn test_fixture_alethe_loads_and_verifies_when_available() {
    let json = std::fs::read_to_string(fixture_path("ay_alethe_envelope.json"))
        .expect("Alethe envelope fixture should exist");
    let cert: ExternalCertificate =
        serde_json::from_str(&json).expect("Alethe envelope should deserialize");
    match cert {
        ExternalCertificate::Alethe(alethe) => {
            assert_eq!(alethe.version, "1.0");
            assert!(
                alethe.problem.contains("QF_UF"),
                "Alethe problem should contain QF_UF logic declaration"
            );
            assert!(
                alethe.proof.contains(":rule resolution"),
                "Alethe proof should contain a resolution step"
            );
            #[cfg(feature = "carcara-verify")]
            {
                let valid = verify_alethe_certificate(&alethe)
                    .expect("Alethe fixture should verify when Carcara is enabled");
                assert!(valid, "Alethe fixture should be fully verified");
            }
            #[cfg(not(feature = "carcara-verify"))]
            {
                let err = verify_alethe_certificate(&alethe)
                    .expect_err("Alethe verification should require carcara-verify feature");
                #[cfg(feature = "ay-smt")]
                {
                    assert_eq!(err.code, ExternalCertErrorCode::ProofVerificationFailed);
                    assert_eq!(
                        err.detail,
                        "carcara-verify feature required for tier 1 verification"
                    );
                }
                #[cfg(not(feature = "ay-smt"))]
                {
                    assert_eq!(err.code, ExternalCertErrorCode::VerifierNotAvailable);
                    assert!(
                        err.detail.contains("ay-smt feature required"),
                        "unexpected verifier-not-available detail: {}",
                        err.detail
                    );
                }
            }
        }
        other => panic!("expected Alethe variant, got {other:?}"),
    }
}

#[test]
fn test_fixture_malformed_json_rejected() {
    let malformed = r#"{"type": "farkas_certificate", "version": "1.0"}"#;
    let result: Result<ExternalCertificate, _> = serde_json::from_str(malformed);
    assert!(
        result.is_err(),
        "malformed certificate missing required fields should be rejected"
    );
}

#[test]
fn test_fixture_unknown_type_rejected() {
    let unknown = r#"{"type": "unknown_certificate", "version": "1.0", "data": {}}"#;
    let result: Result<ExternalCertificate, _> = serde_json::from_str(unknown);
    assert!(
        result.is_err(),
        "certificate with unknown type tag should be rejected"
    );
}

// ============================================================================//
// gamma-crown Whisper-tiny 4-block IBP/Farkas fixtures (clean#3525)
// ============================================================================//
//
// Phase 2 delivery from gamma-crown: `to_clean_flat_entailments` +
// `gamma-cli export-proof --format json-clean --method farkas` emits per-block
// entailment certificates for the longest finite-bounds prefix of Whisper-tiny
// (4 blocks total). Each block is a uniform-1.0 Farkas combination of
// 2 * input_dim paired bound constraints (`x_i <= eps`, `-x_i <= eps`). The
// variable coefficients cancel pairwise and the conclusion bounds `sum = 0`
// against `2 * input_dim * eps`. Uniform-1.0 multipliers are
// pipeline-validation only and carry no network-specific information — they
// still pass `verify_entailment_certificate` because the Farkas combination
// is mathematically valid.
//
// Fixture files live under
// `tests/fixtures/external_certificates/gamma_crown_whisper_tiny_4block/` and
// mirror the upstream `~/gamma-crown/tests/fixtures/proof_certificates/
// whisper_tiny_4block/` source. These tests lock in the decimal-rational
// parser extension (`0.00001`, `0.234562084`, ...) that landed with this
// commit and serve as the cross-repo consumer contract for the IBP soundness
// pipeline (clean mail #4492 / #3505 Phase 1 / #3525 Phase 2).

/// Per-block shape pulled from upstream `metadata.json`. Kept inline so the
/// behavioral test has a checkable ground truth independent of the metadata
/// JSON (i.e., the test fails if either the block JSON drifts OR the upstream
/// metadata claims drift away from this snapshot).
///
/// Block 0's conclusion constant IS the analytic `2 * input_dim * epsilon`
/// (= 320 * 1e-5 = 0.0032) because its premises are the raw input-eps
/// bounds. Blocks 1-3 are post-IBP propagated intervals: the paired bounds
/// are not symmetric `±eps`, so the conclusion constant is an empirical
/// sum recorded from the fixture, not a closed-form value.
struct BlockShape {
    name: &'static str,
    file: &'static str,
    input_dim: usize,
    /// Snapshot of `conclusion.constant` as a rational string exactly matching
    /// the fixture. Drift indicates schema change upstream.
    expected_conclusion_constant: &'static str,
}

const WHISPER_TINY_4BLOCK_SHAPES: [BlockShape; 4] = [
    BlockShape {
        name: "block_0",
        file: "gamma_crown_whisper_tiny_4block/block_0.json",
        input_dim: 160,
        // 2 * 160 * 1e-5 = 0.0032 (closed form for raw-input block).
        expected_conclusion_constant: "0.0032",
    },
    BlockShape {
        name: "block_1",
        file: "gamma_crown_whisper_tiny_4block/block_1.json",
        input_dim: 768,
        // Empirical sum of signed (Le/Ge) constants for the 1536 IBP-propagated
        // paired bounds. NOT 2*input_dim*epsilon — post-IBP intervals are
        // asymmetric around zero.
        // Conservatively rounded to the Farkas-derived bound
        // 18415161/250000000 = 0.073660644.
        expected_conclusion_constant: "0.073660644",
    },
    BlockShape {
        name: "block_2",
        file: "gamma_crown_whisper_tiny_4block/block_2.json",
        input_dim: 768,
        expected_conclusion_constant: "0.027698889",
    },
    BlockShape {
        name: "block_3",
        file: "gamma_crown_whisper_tiny_4block/block_3.json",
        input_dim: 384,
        expected_conclusion_constant: "0.234562084",
    },
];

/// Load a block-shape fixture file and extract the `ExternalEntailmentCert`
/// payload, panicking with a labeled message on any failure.
fn load_whisper_block_entailment(shape: &BlockShape) -> ExternalEntailmentCert {
    let path = fixture_path(shape.file);
    let json = std::fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("{}: fixture should exist ({e})", shape.name));
    let cert: ExternalCertificate = serde_json::from_str(&json)
        .unwrap_or_else(|e| panic!("{}: fixture should deserialize ({e})", shape.name));
    match cert {
        ExternalCertificate::Entailment(e) => e,
        other => panic!("{}: expected Entailment variant, got {other:?}", shape.name),
    }
}

/// Assert schema-level invariants for one Whisper-tiny Farkas block:
/// 2 * input_dim paired-bound premises, uniform-1.0 multipliers, empty
/// conclusion coefficients, and the recorded conclusion constant snapshot.
fn assert_whisper_block_schema(shape: &BlockShape, entailment: &ExternalEntailmentCert) {
    assert_eq!(entailment.version, "1.0", "{}: version", shape.name);
    let expected_premises = 2 * shape.input_dim;
    assert_eq!(
        entailment.premises.len(),
        expected_premises,
        "{}: premise count should be 2 * input_dim = {}",
        shape.name,
        expected_premises,
    );
    assert_eq!(
        entailment.multipliers.len(),
        entailment.premises.len(),
        "{}: multipliers.len() must match premises.len()",
        shape.name,
    );
    for (i, m) in entailment.multipliers.iter().enumerate() {
        assert_eq!(
            *m,
            ExternalRational::ONE,
            "{}: multiplier[{i}] should be uniform 1.0",
            shape.name,
        );
    }
    // Conclusion is `(empty coeffs) <= constant` because uniform-1.0 over
    // paired bounds cancels all variable coefficients.
    assert!(
        matches!(entailment.conclusion.kind, ConstraintKind::Le),
        "{}: conclusion kind should be Le",
        shape.name,
    );
    assert!(
        entailment.conclusion.coefficients.is_empty(),
        "{}: conclusion coefficients should be empty (paired bounds cancel), got {:?}",
        shape.name,
        entailment.conclusion.coefficients,
    );
    let expected = rational::parse_rational_str_for_test(shape.expected_conclusion_constant)
        .expect("test constant should parse");
    assert_eq!(
        entailment.conclusion.constant, expected,
        "{}: conclusion constant should match recorded snapshot",
        shape.name,
    );
}

/// Drive `verify_entailment_certificate` and assert every block is accepted.
fn assert_whisper_block_verify_outcome(shape: &BlockShape, entailment: &ExternalEntailmentCert) {
    let (derived, claimed) = verify_entailment_certificate(entailment)
        .unwrap_or_else(|e| panic!("{}: fixture should verify ({e})", shape.name));
    assert!(
        derived <= claimed,
        "{}: derived bound {derived:?} should imply claimed bound {claimed:?}",
        shape.name,
    );
}

#[test]
fn test_fixture_whisper_tiny_4block_per_block_loads_and_verifies() {
    for shape in &WHISPER_TINY_4BLOCK_SHAPES {
        let entailment = load_whisper_block_entailment(shape);
        assert_whisper_block_schema(shape, &entailment);
        assert_whisper_block_verify_outcome(shape, &entailment);
    }
}

#[test]
fn test_fixture_whisper_tiny_4block_flat_array_loads() {
    // `entailments_clean.json` is the flat `Vec<LeanEntailment>` shape emitted
    // by `to_clean_flat_entailments` — a single JSON array of all 4 block
    // entailments. This is the shape used by the gamma-crown CLI export-proof
    // --format json-clean surface.
    let path = fixture_path("gamma_crown_whisper_tiny_4block/entailments.json");
    let json = std::fs::read_to_string(&path).expect("flat entailments fixture should exist");
    let certs: Vec<ExternalCertificate> =
        serde_json::from_str(&json).expect("flat fixture should deserialize as Vec");
    assert_eq!(
        certs.len(),
        4,
        "flat fixture should contain exactly 4 entailments (one per block)"
    );
    for (i, cert) in certs.iter().enumerate() {
        let entailment = match cert {
            ExternalCertificate::Entailment(e) => e,
            other => panic!("flat[{i}]: expected Entailment variant, got {other:?}"),
        };
        // Schema-level invariant applies to every block: conclusion has empty
        // coefficients because uniform-1.0 paired bounds cancel variable
        // coefficients.
        assert!(
            entailment.conclusion.coefficients.is_empty(),
            "flat[{i}]: conclusion should have empty coefficients",
        );
        // Behavioral verification should accept every block now that block_1 is
        // conservatively rounded.
        let shape = &WHISPER_TINY_4BLOCK_SHAPES[i];
        verify_entailment_certificate(entailment)
            .unwrap_or_else(|e| panic!("flat[{i}] ({}): should verify ({e})", shape.name));
    }
    // Cross-check: the flat array and the per-block files agree block-for-block
    // on conclusion constants.
    for (i, shape) in WHISPER_TINY_4BLOCK_SHAPES.iter().enumerate() {
        let entailment = match &certs[i] {
            ExternalCertificate::Entailment(e) => e,
            _ => unreachable!("checked above"),
        };
        let expected = rational::parse_rational_str_for_test(shape.expected_conclusion_constant)
            .expect("test constant should parse");
        assert_eq!(
            entailment.conclusion.constant, expected,
            "flat[{i}] ({}): conclusion constant mismatch with metadata snapshot",
            shape.name,
        );
    }
}
