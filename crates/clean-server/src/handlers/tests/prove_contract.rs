// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Contract-focused tests for `ProveResult`.

use crate::handlers::{
    build_verified_prove_result, prove_result_from_smt_verification, ProveResult, ProveStatus,
    TrustSummary,
};
use clean_auto::bridge::{BridgeError, ProofMethod, SmtVerificationResult};
use clean_kernel::sorry::{create_sorry_term_with_kind, create_trusted_ay_term, SorryKind};
use clean_kernel::{Environment, Expr, Level, Name};

fn true_goal() -> Expr {
    Expr::const_(Name::from_string("True"), vec![])
}

fn fully_verified_trust_summary() -> TrustSummary {
    TrustSummary {
        sorry_count: 0,
        sorry_provenance: Some(crate::handlers::SorryProvenance {
            has_explicit_sorry: false,
            has_synthetic_sorry: false,
        }),
        ay_count: 0,
        ay_provenance: None,
        arith_count: 0,
        arith_provenance: None,
        kernel_check_failures: 0,
        fully_verified: true,
        smt_recovery: None,
    }
}

fn assert_verified_prove_result(result: &ProveResult) {
    assert!(result.found, "verified prove results must set found=true");
    assert!(
        result.proof_term.is_some(),
        "verified prove results must include a proof_term"
    );
    assert_eq!(result.method.as_deref(), Some("smt"));
    assert!(
        result.reason.is_none(),
        "verified prove results must omit reason"
    );
    let trust_summary = result
        .trust_summary
        .as_ref()
        .expect("verified prove results must include trust_summary");
    assert!(
        trust_summary.sorry_provenance.is_some(),
        "verified prove results must surface closed-proof sorry provenance"
    );
}

fn assert_unverified_prove_result(result: &ProveResult) {
    assert!(result.found, "unverified prove results must set found=true");
    assert!(
        result.proof_term.is_none(),
        "unverified prove results must omit proof_term"
    );
    assert_eq!(result.method.as_deref(), Some("smt_unverified"));
    assert!(
        result.trust_summary.is_none(),
        "unverified prove results must omit trust_summary"
    );
}

fn assert_kernel_rejected_prove_result(result: &ProveResult) {
    assert!(
        result.found,
        "kernel-rejected prove results still found a candidate term"
    );
    assert!(
        result.proof_term.is_some(),
        "kernel-rejected results must surface the rejected proof_term for inspection"
    );
    assert!(
        result.reason.is_some(),
        "kernel-rejected results must explain the rejection"
    );
    let trust_summary = result
        .trust_summary
        .as_ref()
        .expect("kernel-rejected results must include the failing trust_summary");
    assert!(
        !trust_summary.fully_verified,
        "kernel-rejected results must never be fully_verified"
    );
}

fn assert_proofless_prove_result(result: &ProveResult) {
    assert!(
        !result.found,
        "refuted/unknown prove results must set found=false"
    );
    assert!(
        result.proof_term.is_none(),
        "refuted/unknown prove results must omit proof_term"
    );
    assert!(
        result.trust_summary.is_none(),
        "refuted/unknown prove results must omit trust_summary"
    );
}

fn assert_prove_status_invariants(result: &ProveResult) {
    match result.status {
        ProveStatus::Verified => assert_verified_prove_result(result),
        ProveStatus::Unverified => assert_unverified_prove_result(result),
        ProveStatus::KernelRejected => assert_kernel_rejected_prove_result(result),
        ProveStatus::Refuted | ProveStatus::Unknown => {
            assert_proofless_prove_result(result);
            if matches!(result.status, ProveStatus::Refuted) {
                assert!(
                    result.reason.is_none(),
                    "refuted prove results must omit reason"
                );
            }
        }
    }
}

/// SOUNDNESS regression: a proof term that FAILS the kernel re-check must never
/// be reported as `Verified`. Before the fix, `build_verified_prove_result`
/// hardcoded `status: Verified` and only `trust_summary.fully_verified` reflected
/// the failure — a trust oracle that lies about acceptance to any client keying
/// on `status`.
#[test]
fn test_build_verified_prove_result_kernel_rejection_is_not_verified() {
    // `Prop` (Sort 0) has type `Sort 1`, not `Prop` — so `check_type(Prop, Prop)`
    // is rejected by the kernel even in an empty env (no constant lookups needed).
    let env = Environment::new();
    let goal = Expr::prop();
    let bad_proof = Expr::prop();

    let result = build_verified_prove_result(&env, &goal, &bad_proof, "bogus reconstruction");

    assert_ne!(
        result.status,
        ProveStatus::Verified,
        "a proof term rejected by the kernel must NOT report status=Verified"
    );
    assert_eq!(result.status, ProveStatus::KernelRejected);
    assert_prove_status_invariants(&result);

    let trust_summary = result
        .trust_summary
        .as_ref()
        .expect("trust_summary must be present on a kernel-rejected result");
    assert!(
        !trust_summary.fully_verified,
        "kernel-rejected result must not be fully_verified"
    );
}

/// Positive control: a genuinely kernel-checkable term still reports `Verified`,
/// so the regression guard above is not passing vacuously.
#[test]
fn test_build_verified_prove_result_valid_term_is_verified() {
    // `Prop` (Sort 0) has type `Sort 1`, so `check_type(Prop, Sort 1)` succeeds.
    let env = Environment::new();
    let goal = Expr::sort(Level::succ(Level::zero())); // Sort 1
    let good_proof = Expr::prop(); // Prop : Sort 1

    let result = build_verified_prove_result(&env, &goal, &good_proof, "sort tower");

    assert_eq!(
        result.status,
        ProveStatus::Verified,
        "a kernel-checkable term must report Verified"
    );
    assert!(result.reason.is_none());
    assert_prove_status_invariants(&result);
}

fn assert_json_roundtrip_case(
    status: ProveStatus,
    found: bool,
    proof_term: Option<&str>,
    proof_sketch: Option<&str>,
    method: Option<&str>,
    reason: Option<&str>,
    trust_summary: Option<TrustSummary>,
    expected_status: &str,
) {
    let result = ProveResult {
        found,
        proof_term: proof_term.map(str::to_string),
        proof_sketch: proof_sketch.map(str::to_string),
        method: method.map(str::to_string),
        status,
        reason: reason.map(str::to_string),
        trust_summary: trust_summary.clone(),
        time_ms: 42,
        time_ns: Some(42_000_000),
    };

    let json = serde_json::to_value(&result).unwrap();
    assert_eq!(
        json.get("status").and_then(serde_json::Value::as_str),
        Some(expected_status)
    );

    let deserialized: ProveResult = serde_json::from_value(json).unwrap();
    assert_eq!(deserialized.status, status);
    assert_eq!(deserialized.found, found);
    assert_eq!(deserialized.reason.as_deref(), reason);
    assert_eq!(
        deserialized.trust_summary.is_some(),
        trust_summary.is_some(),
        "trust_summary presence should round-trip"
    );
    assert_eq!(deserialized.time_ms, 42);
    assert_prove_status_invariants(&deserialized);
}

#[test]
fn test_prove_result_json_roundtrip() {
    let cases = [
        (
            ProveStatus::Verified,
            true,
            Some("fun x => x"),
            Some("identity"),
            Some("smt"),
            None,
            Some(fully_verified_trust_summary()),
            "verified",
        ),
        (
            ProveStatus::Unverified,
            true,
            None,
            Some("SMT proved goal but proof reconstruction unavailable"),
            Some("smt_unverified"),
            Some("translation failed: unsupported quantifier elimination step"),
            None,
            "unverified",
        ),
        (
            ProveStatus::Refuted,
            false,
            None,
            None,
            None,
            None,
            None,
            "refuted",
        ),
        (
            ProveStatus::Unknown,
            false,
            None,
            None,
            None,
            Some("solver returned unknown after timeout"),
            None,
            "unknown",
        ),
    ];

    for (status, found, proof_term, proof_sketch, method, reason, trust_summary, expected_status) in
        cases
    {
        assert_json_roundtrip_case(
            status,
            found,
            proof_term,
            proof_sketch,
            method,
            reason,
            trust_summary,
            expected_status,
        );
    }
}

#[test]
fn test_prove_result_json_without_status_defaults_to_unknown() {
    let json = r#"{"found":false,"time_ms":42}"#;
    let deserialized: ProveResult = serde_json::from_str(json).unwrap();

    assert_eq!(deserialized.status, ProveStatus::Unknown);
    assert!(deserialized.reason.is_none());
    assert!(deserialized.trust_summary.is_none());
    assert_eq!(deserialized.time_ms, 42);
}

#[test]
fn test_prove_result_from_unverified_preserves_reason() {
    let env = Environment::with_prelude();
    let goal = true_goal();
    let reason = BridgeError::TranslationFailed {
        context: "unsupported quantifier elimination step".to_string(),
    };
    let result = prove_result_from_smt_verification(
        &env,
        &goal,
        SmtVerificationResult::Unverified {
            reason,
            method: ProofMethod::SmtUnsat,
        },
    );

    assert_eq!(result.status, ProveStatus::Unverified);
    assert!(result.found, "unverified prove results must set found=true");
    assert!(
        result
            .reason
            .as_deref()
            .is_some_and(|r| r.contains("unsupported quantifier elimination step")),
        "unverified reason must preserve BridgeError message, got: {:?}",
        result.reason
    );
    assert_eq!(result.method.as_deref(), Some("smt_unverified"));
    assert_prove_status_invariants(&result);
}

#[test]
fn test_prove_result_from_unknown_preserves_reason() {
    let env = Environment::with_prelude();
    let goal = true_goal();
    let result = prove_result_from_smt_verification(
        &env,
        &goal,
        SmtVerificationResult::Unknown("lossy SMT translation dropped a hypothesis".to_string()),
    );

    assert_eq!(result.status, ProveStatus::Unknown);
    assert!(
        !result.found,
        "unknown prove results must not set found=true"
    );
    assert_eq!(
        result.reason.as_deref(),
        Some("lossy SMT translation dropped a hypothesis")
    );
}

#[test]
fn test_build_verified_prove_result_surfaces_clean_trust_summary() {
    let env = Environment::with_prelude();
    let goal = true_goal();
    let result = build_verified_prove_result(
        &env,
        &goal,
        &Expr::const_(Name::from_string("True.intro"), vec![]),
        "exact True.intro",
    );

    let trust_summary = result
        .trust_summary
        .as_ref()
        .expect("verified prove result should include trust_summary");
    assert_eq!(result.status, ProveStatus::Verified);
    assert_eq!(trust_summary.sorry_count, 0);
    assert_eq!(trust_summary.ay_count, 0);
    assert_eq!(trust_summary.arith_count, 0);
    assert_eq!(trust_summary.kernel_check_failures, 0);
    assert!(trust_summary.ay_provenance.is_none());
    assert!(trust_summary.arith_provenance.is_none());
    assert!(
        trust_summary.fully_verified,
        "clean kernel-checked proof should be fully verified"
    );
}

#[test]
fn test_build_verified_prove_result_surfaces_trusted_ay_counts() {
    let env = Environment::with_prelude();
    let goal = true_goal();
    let proof_term = create_trusted_ay_term(&env, &goal);
    let result = build_verified_prove_result(&env, &goal, &proof_term, "trustedAy");

    let trust_summary = result
        .trust_summary
        .as_ref()
        .expect("verified prove result should include trust_summary");
    let ay_provenance = trust_summary
        .ay_provenance
        .as_ref()
        .expect("trustedAy-backed proof should expose ay provenance");

    assert_eq!(trust_summary.sorry_count, 0);
    assert_eq!(trust_summary.ay_count, 1);
    assert_eq!(ay_provenance.unclassified_steps, 1);
    assert_eq!(trust_summary.arith_count, 0);
    assert!(
        !trust_summary.fully_verified,
        "trustedAy-backed proof must not be fully verified"
    );
}

#[test]
fn test_build_verified_prove_result_surfaces_trusted_arith_counts() {
    let env = Environment::with_prelude();
    let goal = true_goal();
    let proof_term = Expr::app(
        Expr::const_(Name::from_string("trustedArith"), vec![Level::zero()]),
        goal.clone(),
    );
    let result = build_verified_prove_result(&env, &goal, &proof_term, "trustedArith");

    let trust_summary = result
        .trust_summary
        .as_ref()
        .expect("verified prove result should include trust_summary");
    let arith_provenance = trust_summary
        .arith_provenance
        .as_ref()
        .expect("trustedArith-backed proof should expose arith provenance");

    assert_eq!(trust_summary.sorry_count, 0);
    assert_eq!(trust_summary.ay_count, 0);
    assert_eq!(trust_summary.arith_count, 1);
    assert_eq!(arith_provenance.unclassified_steps, 1);
    assert!(
        !trust_summary.fully_verified,
        "trustedArith-backed proof must not be fully verified"
    );
}

#[test]
fn test_build_verified_prove_result_surfaces_sorry_provenance() {
    let env = Environment::with_prelude();
    let goal = true_goal();
    let proof_term = create_sorry_term_with_kind(&env, &goal, SorryKind::Explicit);
    let result = build_verified_prove_result(&env, &goal, &proof_term, "sorry");

    let trust_summary = result
        .trust_summary
        .as_ref()
        .expect("verified prove result should include trust_summary");
    let sorry_provenance = trust_summary
        .sorry_provenance
        .as_ref()
        .expect("sorry-backed proof should expose sorry provenance");

    assert_eq!(trust_summary.sorry_count, 1);
    assert!(sorry_provenance.has_explicit_sorry);
    assert!(!sorry_provenance.has_synthetic_sorry);
    assert!(
        !trust_summary.fully_verified,
        "sorry-backed proof must not be fully verified"
    );
}

#[test]
fn test_build_verified_prove_result_counts_legacy_sorry_once() {
    let env = Environment::new();
    let goal = Expr::prop();
    let proof_term = create_sorry_term_with_kind(&env, &goal, SorryKind::Explicit);
    let result = build_verified_prove_result(&env, &goal, &proof_term, "legacy sorry");

    let trust_summary = result
        .trust_summary
        .as_ref()
        .expect("legacy sorry proof should include trust_summary");
    assert_eq!(
        trust_summary.sorry_count, 1,
        "legacy sorry applications should count once, not once for the spine and once for the head"
    );
}

#[test]
fn test_build_verified_prove_result_omits_smt_recovery() {
    let env = Environment::new();
    let goal = Expr::prop();
    let proof = create_sorry_term_with_kind(&env, &goal, SorryKind::Explicit);
    let result = build_verified_prove_result(&env, &goal, &proof, "smt_recovery negative control");

    let trust_summary = result
        .trust_summary
        .as_ref()
        .expect("prove result should include trust_summary");
    assert!(
        trust_summary.smt_recovery.is_none(),
        "standalone prove route must not synthesize smt_recovery from closed proof scanning"
    );
}
