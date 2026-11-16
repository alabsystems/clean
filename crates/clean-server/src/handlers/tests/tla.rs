// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use crate::handlers::*;

// =========================================================================
// Single obligation tests for handle_prove_tla (#1654)
// =========================================================================

/// Test handle_prove_tla with a trivially true obligation (Always(True)).
#[tokio::test]
async fn test_prove_tla_single_true_obligation() {
    let state = ServerState::new();

    let params = ProveTlaParams {
        obligation: clean_tla::obligation::TlaObligation::new(
            clean_tla::encoding::TlaFormula::True,
        ),
        timeout_ms: Some(5000),
    };

    let response = handle_prove_tla(&state, RequestId::Number(1), params).await;
    assert!(
        response.error.is_none(),
        "RPC-level error: {:?}",
        response.error
    );

    let result: ProveTlaResult = serde_json::from_value(response.result.unwrap()).unwrap();
    assert!(result.proved, "TRUE should be trivially provable");
    assert!(
        !result.tactics_tried.is_empty(),
        "Should report tactics tried"
    );
}

/// Test handle_prove_tla with a False obligation (unprovable).
#[tokio::test]
async fn test_prove_tla_single_false_obligation() {
    let state = ServerState::new();

    let params = ProveTlaParams {
        obligation: clean_tla::obligation::TlaObligation::new(
            clean_tla::encoding::TlaFormula::False,
        ),
        timeout_ms: Some(5000),
    };

    let response = handle_prove_tla(&state, RequestId::Number(1), params).await;
    assert!(
        response.error.is_none(),
        "RPC-level error: {:?}",
        response.error
    );

    let result: ProveTlaResult = serde_json::from_value(response.result.unwrap()).unwrap();
    assert!(!result.proved, "FALSE should not be provable");
}

/// Test handle_prove_tla records metrics.
#[tokio::test]
async fn test_prove_tla_records_metrics() {
    let state = ServerState::new();

    let params = ProveTlaParams {
        obligation: clean_tla::obligation::TlaObligation::new(
            clean_tla::encoding::TlaFormula::True,
        ),
        timeout_ms: Some(5000),
    };

    let _response = handle_prove_tla(&state, RequestId::Number(1), params).await;

    assert!(
        state
            .metrics
            .total_requests
            .load(std::sync::atomic::Ordering::Relaxed)
            > 0,
        "Metrics should record the proveTLA request"
    );
}

/// Test handle_prove_tla JSON serialization roundtrip for params.
#[test]
fn test_prove_tla_params_json_roundtrip() {
    let params = ProveTlaParams {
        obligation: clean_tla::obligation::TlaObligation::new(
            clean_tla::encoding::TlaFormula::True,
        ),
        timeout_ms: Some(3000),
    };

    let json = serde_json::to_string(&params).unwrap();
    let deserialized: ProveTlaParams = serde_json::from_str(&json).unwrap();

    assert_eq!(deserialized.timeout_ms, Some(3000));
}

// =========================================================================
// Batch tests
// =========================================================================

#[tokio::test]
async fn test_batch_prove_tla_adaptive_progress_frequency() {
    use tokio::sync::mpsc;

    let state = ServerState::new();

    // Create 200 obligations (enough to trigger adaptive frequency: interval = 200/50 = 4)
    let items: Vec<BatchProveTlaItem> = (0..200)
        .map(|i| BatchProveTlaItem {
            id: format!("tla_{i}"),
            obligation: clean_tla::obligation::TlaObligation::new(
                clean_tla::encoding::TlaFormula::Always(Box::new(
                    clean_tla::encoding::TlaFormula::True,
                )),
            ),
        })
        .collect();

    let params = BatchProveTlaParams {
        items,
        threads: 1, // Single thread for predictable ordering
        timeout_ms: None,
    };

    let (tx, mut rx) = mpsc::channel(300);
    let progress = ProgressSender::new(RequestId::Number(99), tx);

    let response =
        handle_batch_prove_tla(&state, RequestId::Number(1), params, Some(progress)).await;
    assert!(
        response.error.is_none(),
        "unexpected error: {:?}",
        response.error
    );

    let mut updates = Vec::new();
    // Use 5s timeout to avoid flakiness under CI load
    while let Ok(update) = tokio::time::timeout(Duration::from_secs(5), rx.recv()).await {
        match update {
            Some(u) => updates.push(u),
            None => break,
        }
    }

    // Count per-item progress updates (excluding start and complete messages)
    let per_item_updates: Vec<_> = updates.iter().filter(|u| u.message.contains('/')).collect();

    // For 200 items with interval=4, we expect approximately 50 updates
    // Plus the first and last item always sent
    // Actual: 1 (first) + 50 (on intervals) = ~51 updates
    // Note: exact count depends on timing and scheduling - use wide range to avoid flakiness
    assert!(
        per_item_updates.len() <= 70,
        "expected adaptive frequency to reduce updates from 200 to ~30-70, got {}",
        per_item_updates.len()
    );
    assert!(
        per_item_updates.len() >= 30,
        "expected at least ~30 progress updates for 200 items, got {}",
        per_item_updates.len()
    );

    // Verify first and last items were reported
    assert!(
        per_item_updates
            .iter()
            .any(|u| u.message.contains("[1/200]")),
        "first item should always be reported"
    );
    assert!(
        per_item_updates
            .iter()
            .any(|u| u.message.contains("[200/200]")),
        "last item should always be reported"
    );
}

// =========================================================================
// Edge-case and error-path tests (#1654)
// =========================================================================

/// Test handle_prove_tla with default timeout (None).
#[tokio::test]
async fn test_prove_tla_default_timeout() {
    let state = ServerState::new();

    let params = ProveTlaParams {
        obligation: clean_tla::obligation::TlaObligation::new(
            clean_tla::encoding::TlaFormula::True,
        ),
        timeout_ms: None, // should use default 10_000ms
    };

    let response = handle_prove_tla(&state, RequestId::Number(1), params).await;
    assert!(
        response.error.is_none(),
        "Default timeout should not fail for trivial obligation: {:?}",
        response.error
    );

    let result: ProveTlaResult = serde_json::from_value(response.result.unwrap()).unwrap();
    assert!(
        result.proved,
        "TRUE should be provable with default timeout"
    );
}

/// Test handle_prove_tla with an obligation that has hypotheses.
#[tokio::test]
async fn test_prove_tla_with_hypotheses() {
    let state = ServerState::new();

    let obligation =
        clean_tla::obligation::TlaObligation::new(clean_tla::encoding::TlaFormula::True)
            .with_hypothesis("h1", clean_tla::encoding::TlaFormula::True);

    let params = ProveTlaParams {
        obligation,
        timeout_ms: Some(5000),
    };

    let response = handle_prove_tla(&state, RequestId::Number(1), params).await;
    assert!(
        response.error.is_none(),
        "Obligation with hypotheses should not RPC-error: {:?}",
        response.error
    );

    let result: ProveTlaResult = serde_json::from_value(response.result.unwrap()).unwrap();
    assert!(
        result.proved,
        "TRUE with TRUE hypothesis should be provable"
    );
}

/// Test handle_prove_tla with declarations.
#[tokio::test]
async fn test_prove_tla_with_declarations() {
    let state = ServerState::new();

    let obligation =
        clean_tla::obligation::TlaObligation::new(clean_tla::encoding::TlaFormula::True)
            .with_declare(clean_tla::obligation::TlaDeclare::Variable {
                name: "x".to_string(),
            });

    let params = ProveTlaParams {
        obligation,
        timeout_ms: Some(5000),
    };

    let response = handle_prove_tla(&state, RequestId::Number(1), params).await;
    assert!(
        response.error.is_none(),
        "Obligation with declarations should not RPC-error: {:?}",
        response.error
    );

    let result: ProveTlaResult = serde_json::from_value(response.result.unwrap()).unwrap();
    assert!(
        result.proved,
        "TRUE with variable declaration should be provable"
    );
}

/// Test handle_prove_tla with tactic hint.
#[tokio::test]
async fn test_prove_tla_with_tactic_hint() {
    let state = ServerState::new();

    let obligation =
        clean_tla::obligation::TlaObligation::new(clean_tla::encoding::TlaFormula::True)
            .with_tactic("zenon");

    let params = ProveTlaParams {
        obligation,
        timeout_ms: Some(5000),
    };

    let response = handle_prove_tla(&state, RequestId::Number(1), params).await;
    assert!(
        response.error.is_none(),
        "Obligation with tactic hint should not RPC-error: {:?}",
        response.error
    );
}

/// Test handle_prove_tla with temporal formula (Eventually).
#[tokio::test]
async fn test_prove_tla_eventually_true() {
    let state = ServerState::new();

    let params = ProveTlaParams {
        obligation: clean_tla::obligation::TlaObligation::new(
            clean_tla::encoding::TlaFormula::Eventually(Box::new(
                clean_tla::encoding::TlaFormula::True,
            )),
        ),
        timeout_ms: Some(5000),
    };

    let response = handle_prove_tla(&state, RequestId::Number(1), params).await;
    assert!(
        response.error.is_none(),
        "Eventually(True) should not RPC-error: {:?}",
        response.error
    );
}

/// Test handle_batch_prove_tla with empty items list.
#[tokio::test]
async fn test_batch_prove_tla_empty_items() {
    let state = ServerState::new();

    let params = BatchProveTlaParams {
        items: vec![],
        threads: 1,
        timeout_ms: None,
    };

    let response = handle_batch_prove_tla(&state, RequestId::Number(1), params, None).await;
    assert!(
        response.error.is_none(),
        "Empty batch should succeed: {:?}",
        response.error
    );

    let result: BatchProveTlaResult = serde_json::from_value(response.result.unwrap()).unwrap();
    assert!(result.results.is_empty(), "No results for empty batch");
    // Stats should handle empty gracefully
    assert_eq!(result.stats.total, 0);
}

/// Test handle_batch_prove_tla with mixed results (some provable, some not).
#[tokio::test]
async fn test_batch_prove_tla_mixed_results() {
    let state = ServerState::new();

    let items = vec![
        BatchProveTlaItem {
            id: "provable".to_string(),
            obligation: clean_tla::obligation::TlaObligation::new(
                clean_tla::encoding::TlaFormula::True,
            ),
        },
        BatchProveTlaItem {
            id: "unprovable".to_string(),
            obligation: clean_tla::obligation::TlaObligation::new(
                clean_tla::encoding::TlaFormula::False,
            ),
        },
        BatchProveTlaItem {
            id: "also_provable".to_string(),
            obligation: clean_tla::obligation::TlaObligation::new(
                clean_tla::encoding::TlaFormula::Always(Box::new(
                    clean_tla::encoding::TlaFormula::True,
                )),
            ),
        },
    ];

    let params = BatchProveTlaParams {
        items,
        threads: 1,
        timeout_ms: None,
    };

    let response = handle_batch_prove_tla(&state, RequestId::Number(1), params, None).await;
    assert!(
        response.error.is_none(),
        "Mixed batch should succeed: {:?}",
        response.error
    );

    let result: BatchProveTlaResult = serde_json::from_value(response.result.unwrap()).unwrap();
    assert_eq!(result.results.len(), 3, "Should have 3 results");
    assert_eq!(result.stats.total, 3);

    // Find each result by id
    let provable = result.results.iter().find(|r| r.id == "provable").unwrap();
    assert!(provable.proved, "TRUE should be provable");

    let unprovable = result
        .results
        .iter()
        .find(|r| r.id == "unprovable")
        .unwrap();
    assert!(!unprovable.proved, "FALSE should not be provable");

    let also_provable = result
        .results
        .iter()
        .find(|r| r.id == "also_provable")
        .unwrap();
    assert!(also_provable.proved, "Always(True) should be provable");

    // Stats should reflect mixed results
    assert!(!result.stats.all_proved, "Not all items should be proved");
    assert_eq!(result.stats.proved, 2, "Two items should be proved");
    assert_eq!(result.stats.failed, 1, "One item should fail");
}

/// Test handle_batch_prove_tla with single item (degenerate batch).
#[tokio::test]
async fn test_batch_prove_tla_single_item() {
    let state = ServerState::new();

    let items = vec![BatchProveTlaItem {
        id: "only".to_string(),
        obligation: clean_tla::obligation::TlaObligation::new(
            clean_tla::encoding::TlaFormula::True,
        ),
    }];

    let params = BatchProveTlaParams {
        items,
        threads: 1,
        timeout_ms: Some(5000),
    };

    let response = handle_batch_prove_tla(&state, RequestId::Number(1), params, None).await;
    assert!(
        response.error.is_none(),
        "Single-item batch should succeed: {:?}",
        response.error
    );

    let result: BatchProveTlaResult = serde_json::from_value(response.result.unwrap()).unwrap();
    assert_eq!(result.results.len(), 1);
    assert!(result.stats.all_proved);
    assert_eq!(result.stats.total, 1);
    assert_eq!(result.stats.proved, 1);
    // min and max times should be equal for single item
    assert_eq!(
        result.stats.min_time_us, result.stats.max_time_us,
        "min and max should be equal for single item"
    );
}

/// Test handle_batch_prove_tla with threads=0 (auto thread pool).
#[tokio::test]
async fn test_batch_prove_tla_auto_threads() {
    let state = ServerState::new();

    let items = vec![
        BatchProveTlaItem {
            id: "a".to_string(),
            obligation: clean_tla::obligation::TlaObligation::new(
                clean_tla::encoding::TlaFormula::True,
            ),
        },
        BatchProveTlaItem {
            id: "b".to_string(),
            obligation: clean_tla::obligation::TlaObligation::new(
                clean_tla::encoding::TlaFormula::True,
            ),
        },
    ];

    let params = BatchProveTlaParams {
        items,
        threads: 0, // auto
        timeout_ms: Some(5000),
    };

    let response = handle_batch_prove_tla(&state, RequestId::Number(1), params, None).await;
    assert!(
        response.error.is_none(),
        "Auto-threaded batch should succeed: {:?}",
        response.error
    );

    let result: BatchProveTlaResult = serde_json::from_value(response.result.unwrap()).unwrap();
    assert_eq!(result.results.len(), 2);
    assert!(result.stats.all_proved);
}
