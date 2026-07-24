// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use crate::handlers::*;
use clean_kernel::env::Declaration;
use clean_kernel::{Environment, Expr, Name};

fn make_batch_item(
    id: impl Into<String>,
    goal: impl Into<String>,
    proof: impl Into<String>,
) -> VerifyProofBatchItem {
    VerifyProofBatchItem {
        id: id.into(),
        goal: goal.into(),
        proof: proof.into(),
        context: None,
    }
}

fn assert_sorry_provenance(
    summary: &TrustSummary,
    expected_explicit: bool,
    expected_synthetic: bool,
    context: &str,
) {
    let provenance = summary
        .sorry_provenance
        .as_ref()
        .expect("closed-proof trust summaries should include sorry provenance");
    assert_eq!(
        provenance.has_explicit_sorry, expected_explicit,
        "{context}: unexpected explicit sorry provenance"
    );
    assert_eq!(
        provenance.has_synthetic_sorry, expected_synthetic,
        "{context}: unexpected synthetic sorry provenance"
    );
}

fn assert_clean_batch_item(item: &VerifyProofBatchItemResult) {
    let trust_summary = item
        .trust_summary
        .as_ref()
        .expect("batch items must include trust_summary");
    assert!(item.verified, "batch proof should verify: {}", item.id);
    assert_eq!(trust_summary.sorry_count, 0);
    assert_sorry_provenance(trust_summary, false, false, &item.id);
    assert_eq!(trust_summary.ay_count, 0);
    assert!(
        trust_summary.ay_provenance.is_none(),
        "clean item should omit ay provenance: {}",
        item.id
    );
    assert_eq!(trust_summary.arith_count, 0);
    assert!(
        trust_summary.arith_provenance.is_none(),
        "clean item should omit arith provenance: {}",
        item.id
    );
    assert_eq!(trust_summary.kernel_check_failures, 0);
    assert!(
        trust_summary.fully_verified,
        "clean item should remain fully verified: {}",
        item.id
    );
}

fn assert_sorry_batch_item(item: &VerifyProofBatchItemResult) {
    let trust_summary = item
        .trust_summary
        .as_ref()
        .expect("batch items must include trust_summary");
    assert!(item.verified, "batch proof should verify: {}", item.id);
    assert_eq!(trust_summary.sorry_count, 1);
    assert_sorry_provenance(trust_summary, true, false, &item.id);
    assert_eq!(trust_summary.ay_count, 0);
    assert!(
        trust_summary.ay_provenance.is_none(),
        "sorry-backed item should omit ay provenance: {}",
        item.id
    );
    assert_eq!(trust_summary.arith_count, 0);
    assert!(
        trust_summary.arith_provenance.is_none(),
        "sorry-backed item should omit arith provenance: {}",
        item.id
    );
    assert_eq!(trust_summary.kernel_check_failures, 0);
    assert!(
        !trust_summary.fully_verified,
        "sorry-backed item must not be fully verified: {}",
        item.id
    );
}

fn assert_fail_closed_batch_item(item: &VerifyProofBatchItemResult, context: &str) {
    assert!(
        item.trust_summary.is_some(),
        "{context}: trust_summary should be present; error: {:?}",
        item.error
    );
    let ts = item.trust_summary.as_ref().unwrap();
    assert!(
        !item.verified,
        "{context}: fail-closed item must stay unverified; error: {:?}; trust: {:?}",
        item.error, item.trust_summary
    );
    let error = item
        .error
        .as_ref()
        .expect("fail-closed item should report the arithmetic failure");
    assert!(
        error
            .message
            .contains("certified modular contradiction has no kernel proof"),
        "{context}: unexpected error message: {error:?}"
    );
    assert_eq!(ts.sorry_count, 0, "{context}: should not use sorry");
    assert!(
        ts.sorry_provenance.is_none(),
        "{context}: incomplete fail-closed items should omit sorry provenance"
    );
    assert_eq!(ts.ay_count, 0, "{context}: should not use trustedAy");
    assert!(
        ts.ay_provenance.is_none(),
        "{context}: fail-closed summaries should omit ay provenance"
    );
    assert_eq!(
        ts.arith_count, 0,
        "{context}: fail-closed path must not use trustedArith"
    );
    assert!(
        ts.arith_provenance.is_none(),
        "{context}: fail-closed summaries should omit arith provenance"
    );
    assert_eq!(
        ts.kernel_check_failures, 0,
        "{context}: fail-closed path should not report kernel check failures"
    );
    assert!(
        !ts.fully_verified,
        "{context}: fail-closed item must not be fully_verified"
    );
}

fn add_parity_predicates(env: &mut Environment) {
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    for name in ["Even", "Odd"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: Expr::arrow(nat.clone(), Expr::prop()),
        })
        .unwrap();
    }
}

/// verifyProofBatch populates trust summaries for all items.
#[tokio::test]
async fn test_verify_proof_batch_trust_summary_populated_for_all_items() {
    let state = ServerState::new();

    let proofs: Vec<VerifyProofBatchItem> = (0..8)
        .map(|i| make_batch_item(format!("p{i}"), "Type", "exact Prop"))
        .collect();

    let params = VerifyProofBatchParams {
        proofs,
        threads: Some(4),
        timeout_ms: None,
    };

    let response = handle_verify_proof_batch(&state, RequestId::Number(1), params).await;
    assert!(response.error.is_none(), "RPC error: {:?}", response.error);

    let result: VerifyProofBatchResult = serde_json::from_value(response.result.unwrap()).unwrap();

    assert_eq!(result.results.len(), 8);
    for item in &result.results {
        assert_clean_batch_item(item);
    }
}

#[tokio::test]
async fn test_verify_proof_batch_mixed_trust_items_stay_isolated() {
    const RUNS: usize = 6;
    const PAIRS_PER_RUN: usize = 8;

    let state = ServerState::new();

    for run in 0..RUNS {
        let mut proofs = Vec::with_capacity(PAIRS_PER_RUN * 2);
        for idx in 0..PAIRS_PER_RUN {
            proofs.push(make_batch_item(
                format!("trusted-{run}-{idx}"),
                "Prop",
                "sorry",
            ));
            proofs.push(make_batch_item(
                format!("clean-{run}-{idx}"),
                "(A : Type) -> A -> A",
                "intro A\nintro a\nassumption",
            ));
        }

        let params = VerifyProofBatchParams {
            proofs,
            threads: Some(8),
            timeout_ms: None,
        };

        let response = handle_verify_proof_batch(&state, RequestId::Number(1), params).await;
        assert!(response.error.is_none(), "RPC error: {:?}", response.error);

        let result: VerifyProofBatchResult =
            serde_json::from_value(response.result.unwrap()).unwrap();

        assert_eq!(result.results.len(), PAIRS_PER_RUN * 2);
        for item in &result.results {
            if item.id.starts_with("trusted-") {
                assert_sorry_batch_item(item);
            } else {
                assert!(
                    item.id.starts_with("clean-"),
                    "unexpected batch item id: {}",
                    item.id
                );
                assert_clean_batch_item(item);
            }
        }
    }
}

/// verifyProofBatch should keep fail-closed modular mathverse items zero-trust.
///
/// The sorry-based isolation test above covers sorry_count contamination. This
/// regression keeps the parity mathverse fixture on the batch handler, but after
/// #2564 it must fail closed instead of recording trustedArith.
#[tokio::test]
async fn test_verify_proof_batch_mathverse_fail_closed_stays_zero_trust() {
    let mut env = Environment::with_prelude();
    add_parity_predicates(&mut env);
    let state = ServerState::new().with_env(env);

    let proofs = vec![
        make_batch_item(
            "trusted-mathverse",
            "(n : Nat) -> Even n -> Odd n -> False",
            "intro n\nintro h_even\nintro h_odd\nomega",
        ),
        make_batch_item("clean", "Type", "exact Prop"),
    ];

    let params = VerifyProofBatchParams {
        proofs,
        threads: Some(2),
        timeout_ms: None,
    };

    let response = handle_verify_proof_batch(&state, RequestId::Number(1), params).await;
    assert!(response.error.is_none(), "RPC error: {:?}", response.error);

    let result: VerifyProofBatchResult = serde_json::from_value(response.result.unwrap()).unwrap();

    assert_eq!(result.results.len(), 2);
    assert_fail_closed_batch_item(&result.results[0], "verifyProofBatch mathverse item");
    assert_clean_batch_item(&result.results[1]);
}
