// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use crate::handlers::*;
use crate::proof_state::ProofStateCacheConfig;
use clean_elab::tactic::ProofState;
use clean_kernel::cert::ProofCert;
use clean_kernel::name::NameInterner;
use clean_kernel::{Environment, Expr, Level};
use std::path::PathBuf;
use std::sync::atomic::Ordering;
use std::time::Duration;
use tokio::time::sleep;

fn lean_toolchain_fixture() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures/lean_toolchain/repo-root/lean-toolchain")
}

#[tokio::test]
async fn test_get_config_default() {
    let state = ServerState::new();
    let response = handle_get_config(&state, RequestId::Number(1)).await;

    let result: GetConfigResult = serde_json::from_value(response.result.unwrap()).unwrap();

    assert_eq!(result.worker_threads, 0); // Default is auto
    assert!(result.effective_threads > 0); // Should be at least 1
    assert!(!result.gpu_enabled);
    assert_eq!(result.default_timeout_ms, 5000);
}

#[tokio::test]
async fn test_get_config_with_worker_threads() {
    let state = ServerState::new().with_worker_threads(4);
    let response = handle_get_config(&state, RequestId::Number(1)).await;

    let result: GetConfigResult = serde_json::from_value(response.result.unwrap()).unwrap();

    assert_eq!(result.worker_threads, 4);
    assert_eq!(result.effective_threads, 4);
}

#[tokio::test]
async fn test_get_config_json_serialization() {
    let result = GetConfigResult {
        gpu_enabled: true,
        default_timeout_ms: 10000,
        worker_threads: 8,
        effective_threads: 8,
        lean_toolchain_version: None,
    };

    let json = serde_json::to_string(&result).unwrap();
    assert!(json.contains("\"worker_threads\":8"));
    assert!(json.contains("\"effective_threads\":8"));
    assert!(json.contains("\"gpu_enabled\":true"));
}

#[tokio::test]
async fn test_get_config_surfaces_toolchain_version_from_fixture() {
    let tmp = tempfile::TempDir::new().unwrap();
    std::fs::write(
        tmp.path().join("lakefile.lean"),
        "package demo\nlean_lib Demo",
    )
    .unwrap();
    std::fs::copy(lean_toolchain_fixture(), tmp.path().join("lean-toolchain")).unwrap();

    let state = ServerState::from_root(tmp.path());
    let response = handle_get_config(&state, RequestId::Number(1)).await;
    let result: GetConfigResult = serde_json::from_value(response.result.unwrap()).unwrap();

    assert_eq!(result.lean_toolchain_version.as_deref(), Some("v4.13.0"));
}

#[tokio::test]
async fn test_server_info_surfaces_toolchain_version_from_fixture() {
    let tmp = tempfile::TempDir::new().unwrap();
    std::fs::write(
        tmp.path().join("lakefile.lean"),
        "package demo\nlean_lib Demo",
    )
    .unwrap();
    std::fs::copy(lean_toolchain_fixture(), tmp.path().join("lean-toolchain")).unwrap();

    let state = ServerState::from_root(tmp.path());
    let response = handle_server_info(&state, RequestId::Number(1)).await;
    let result: ServerInfo = serde_json::from_value(response.result.unwrap()).unwrap();

    assert_eq!(result.lean_toolchain_version.as_deref(), Some("v4.13.0"));
}

#[tokio::test]
async fn test_server_state_ignores_malformed_toolchain_file() {
    let tmp = tempfile::TempDir::new().unwrap();
    std::fs::write(
        tmp.path().join("lakefile.lean"),
        "package demo\nlean_lib Demo",
    )
    .unwrap();
    std::fs::write(
        tmp.path().join("lean-toolchain"),
        "leanprover/lean4:v4.29.1\nleanprover/lean4:v4.28.0\n",
    )
    .unwrap();

    let state = ServerState::from_root(tmp.path());

    assert!(state.lean_toolchain().is_none());
    assert!(state.lean_toolchain_version().is_none());
}

// ========================================================================
// Thread Pool Configuration Tests
// ========================================================================

#[tokio::test]
async fn test_get_metrics_basic() {
    let state = ServerState::new();
    let name_interner_before = NameInterner::global().len() as u64;
    let response = handle_get_metrics(&state, RequestId::Number(1)).await;
    let name_interner_after = NameInterner::global().len() as u64;

    assert!(
        response.error.is_none(),
        "unexpected error: {:?}",
        response.error
    );
    let result: GetMetricsResult = serde_json::from_value(response.result.unwrap()).unwrap();

    // Fresh server should have zero requests
    assert_eq!(result.total_requests, 0);
    assert_eq!(result.successful_requests, 0);
    assert_eq!(result.failed_requests, 0);
    assert_eq!(result.success_rate, 1.0); // 1.0 when no requests
    assert_eq!(result.avg_latency_us, 0);

    // Method counts should all be zero
    assert_eq!(result.method_counts.check, 0);
    assert_eq!(result.method_counts.prove, 0);
    assert_eq!(result.method_counts.get_type, 0);
    assert_eq!(result.method_counts.batch_check, 0);
    assert_eq!(result.method_counts.verify_cert, 0);
    assert_eq!(result.method_counts.batch_verify_cert, 0);
    assert_eq!(result.method_counts.verify_cert_archive, 0);
    assert_eq!(result.method_counts.batch_verify_cert_archive, 0);
    assert_eq!(result.method_counts.verify_c, 0);

    // Batch stats should be zero
    assert_eq!(result.batch_stats.items_processed, 0);
    assert_eq!(result.batch_stats.certificates_verified, 0);

    // NameInterner is process-global, so parallel tests may grow it while this
    // test runs. getMetrics should report a live snapshot within our before/after window.
    assert!(
        result.name_interner_entries >= name_interner_before,
        "name interner count should not move backward"
    );
    assert!(
        result.name_interner_entries <= name_interner_after,
        "name interner count should not exceed the post-call snapshot"
    );
}

#[tokio::test]
async fn test_metrics_record_request() {
    let metrics = ServerMetrics::new();

    // Record some requests
    metrics.record_request("check", true, 100);
    metrics.record_request("check", true, 200);
    metrics.record_request("prove", false, 500);

    assert_eq!(metrics.total_requests.load(Ordering::Relaxed), 3);
    assert_eq!(metrics.successful_requests.load(Ordering::Relaxed), 2);
    assert_eq!(metrics.failed_requests.load(Ordering::Relaxed), 1);
    assert_eq!(metrics.check_requests.load(Ordering::Relaxed), 2);
    assert_eq!(metrics.prove_requests.load(Ordering::Relaxed), 1);
    assert_eq!(metrics.cumulative_time_us.load(Ordering::Relaxed), 800);
    assert_eq!(metrics.avg_latency_us(), 266); // 800 / 3
}

#[tokio::test]
async fn test_metrics_batch_tracking() {
    let metrics = ServerMetrics::new();

    metrics.record_batch_items(50);
    metrics.record_batch_items(100);
    metrics.record_certs_verified(10);

    assert_eq!(metrics.batch_items_processed.load(Ordering::Relaxed), 150);
    assert_eq!(metrics.certificates_verified.load(Ordering::Relaxed), 10);
}

#[tokio::test]
async fn test_metrics_timing_breakdown() {
    let metrics = ServerMetrics::new();

    metrics.record_type_check_time(1000);
    metrics.record_cert_verify_time(500);
    metrics.record_type_check_time(500);

    assert_eq!(metrics.type_check_time_us.load(Ordering::Relaxed), 1500);
    assert_eq!(metrics.cert_verify_time_us.load(Ordering::Relaxed), 500);
}

#[tokio::test]
async fn test_get_metrics_json_serialization() {
    let state = ServerState::new();
    let response = handle_get_metrics(&state, RequestId::Number(1)).await;

    let result: GetMetricsResult = serde_json::from_value(response.result.unwrap()).unwrap();

    // Verify JSON round-trip works
    let json = serde_json::to_string(&result).unwrap();
    let _: GetMetricsResult = serde_json::from_str(&json).unwrap();
}

#[tokio::test]
async fn test_metrics_success_rate() {
    let metrics = ServerMetrics::new();

    // 0 requests should return 1.0
    assert_eq!(metrics.success_rate(), 1.0);

    // Add some requests
    metrics.record_request("check", true, 100);
    metrics.record_request("check", true, 100);
    metrics.record_request("check", false, 100);
    metrics.record_request("check", false, 100);

    // 2 successful out of 4 = 0.5
    assert_eq!(metrics.success_rate(), 0.5);
}

#[tokio::test]
async fn test_handler_metrics_integration_check() {
    let state = ServerState::new();

    // Initially no requests
    assert_eq!(state.metrics.check_requests.load(Ordering::Relaxed), 0);
    assert_eq!(state.metrics.total_requests.load(Ordering::Relaxed), 0);

    // Call check handler
    let params = CheckParams {
        code: "Type".to_string(),
        timeout_ms: None,
    };
    let _response = handle_check(&state, RequestId::Number(1), params).await;

    // Verify metrics were recorded
    assert_eq!(state.metrics.check_requests.load(Ordering::Relaxed), 1);
    assert_eq!(state.metrics.total_requests.load(Ordering::Relaxed), 1);
    assert_eq!(state.metrics.successful_requests.load(Ordering::Relaxed), 1);
    assert!(state.metrics.cumulative_time_us.load(Ordering::Relaxed) > 0);
}

#[tokio::test]
async fn test_handler_metrics_integration_prove() {
    let state = ServerState::new();

    // Initially no requests
    assert_eq!(state.metrics.prove_requests.load(Ordering::Relaxed), 0);

    // Call prove handler with a simple goal
    let params = ProveParams {
        goal: "Type".to_string(),
        hypotheses: vec![],
        timeout_ms: Some(100),
        strategy: None,
    };
    let _response = handle_prove(&state, RequestId::Number(1), params).await;

    // Verify metrics were recorded
    assert_eq!(state.metrics.prove_requests.load(Ordering::Relaxed), 1);
    assert_eq!(state.metrics.total_requests.load(Ordering::Relaxed), 1);
}

#[tokio::test]
async fn test_handler_metrics_integration_get_type() {
    let state = ServerState::new();

    // Initially no requests
    assert_eq!(state.metrics.get_type_requests.load(Ordering::Relaxed), 0);

    // Call get_type handler
    let params = GetTypeParams {
        expr: "Type".to_string(),
    };
    let _response = handle_get_type(&state, RequestId::Number(1), params).await;

    // Verify metrics were recorded
    assert_eq!(state.metrics.get_type_requests.load(Ordering::Relaxed), 1);
    assert_eq!(state.metrics.total_requests.load(Ordering::Relaxed), 1);
}

#[tokio::test]
async fn test_handler_metrics_integration_batch_check() {
    let state = ServerState::new();

    // Initially no requests
    assert_eq!(
        state.metrics.batch_check_requests.load(Ordering::Relaxed),
        0
    );
    assert_eq!(
        state.metrics.batch_items_processed.load(Ordering::Relaxed),
        0
    );

    // Call batch_check handler with 3 items
    let params = BatchCheckParams {
        items: vec![
            BatchCheckItem {
                id: "1".to_string(),
                code: "Type".to_string(),
            },
            BatchCheckItem {
                id: "2".to_string(),
                code: "Prop".to_string(),
            },
            BatchCheckItem {
                id: "3".to_string(),
                code: "Type 1".to_string(),
            },
        ],
        use_gpu: false,
        timeout_ms: None,
    };
    let _response = handle_batch_check(&state, RequestId::Number(1), params, None).await;

    // Verify metrics were recorded
    assert_eq!(
        state.metrics.batch_check_requests.load(Ordering::Relaxed),
        1
    );
    assert_eq!(
        state.metrics.batch_items_processed.load(Ordering::Relaxed),
        3
    );
    assert_eq!(state.metrics.total_requests.load(Ordering::Relaxed), 1);
}

#[tokio::test]
async fn test_handler_metrics_integration_verify_cert() {
    let state = ServerState::new();

    // Initially no requests
    assert_eq!(
        state.metrics.verify_cert_requests.load(Ordering::Relaxed),
        0
    );
    assert_eq!(
        state.metrics.certificates_verified.load(Ordering::Relaxed),
        0
    );

    // Call verify_cert handler with a simple Sort certificate
    let params = VerifyCertParams {
        cert: ProofCert::Sort { level: Level::Zero },
        expr: Expr::sort(Level::Zero),
        timeout_ms: None,
    };
    let _response = handle_verify_cert(&state, RequestId::Number(1), params).await;

    // Verify metrics were recorded
    assert_eq!(
        state.metrics.verify_cert_requests.load(Ordering::Relaxed),
        1
    );
    assert_eq!(
        state.metrics.certificates_verified.load(Ordering::Relaxed),
        1
    );
    assert_eq!(state.metrics.total_requests.load(Ordering::Relaxed), 1);
    // Note: cert_verify_time_us not asserted > 0 because in optimized builds,
    // operations can complete in sub-microsecond time, rounding to 0
}

#[tokio::test]
async fn test_handler_metrics_visible_in_get_metrics() {
    let state = ServerState::new();

    // Make some calls to exercise metrics
    let check_params = CheckParams {
        code: "Type".to_string(),
        timeout_ms: None,
    };
    let check_response = handle_check(&state, RequestId::Number(1), check_params).await;
    assert!(
        check_response.error.is_none(),
        "unexpected check error: {:?}",
        check_response.error
    );

    let get_type_params = GetTypeParams {
        expr: "Prop".to_string(),
    };
    let get_type_response = handle_get_type(&state, RequestId::Number(2), get_type_params).await;
    assert!(
        get_type_response.error.is_none(),
        "unexpected get_type error: {:?}",
        get_type_response.error
    );

    // Now call get_metrics and verify the results
    let response = handle_get_metrics(&state, RequestId::Number(3)).await;
    let result: GetMetricsResult = serde_json::from_value(response.result.unwrap()).unwrap();

    // Verify metrics are visible
    assert_eq!(result.total_requests, 2);
    assert_eq!(result.successful_requests, 2);
    assert_eq!(result.method_counts.check, 1);
    assert_eq!(result.method_counts.get_type, 1);
    // Note: avg_latency_us not asserted > 0 because in optimized builds,
    // operations can complete in sub-microsecond time, rounding to 0
}

#[tokio::test]
async fn test_get_cache_metrics_reports_values() {
    let state = ServerState::new();

    state
        .cache_metrics
        .type_cache_enabled
        .store(1, Ordering::Relaxed);
    state
        .cache_metrics
        .type_cache_hits
        .store(9, Ordering::Relaxed);
    state
        .cache_metrics
        .type_cache_misses
        .store(3, Ordering::Relaxed);
    state
        .cache_metrics
        .type_cache_entries
        .store(12, Ordering::Relaxed);
    state
        .cache_metrics
        .whnf_cache_entries
        .store(7, Ordering::Relaxed);
    state
        .cache_metrics
        .def_eq_cache_entries
        .store(4, Ordering::Relaxed);

    let response = handle_get_cache_metrics(&state, RequestId::Number(1)).await;
    assert!(
        response.error.is_none(),
        "unexpected error: {:?}",
        response.error
    );

    let result: GetCacheMetricsResult = serde_json::from_value(response.result.unwrap()).unwrap();
    let type_cache = result.type_cache.expect("type cache should be enabled");

    assert_eq!(type_cache.hits, 9);
    assert_eq!(type_cache.misses, 3);
    assert_eq!(type_cache.entries, 12);
    assert!((type_cache.hit_rate - 75.0).abs() < f64::EPSILON);
    assert!(result.def_eq_cache_enabled);
    assert_eq!(result.whnf_cache_entries, 7);
    assert_eq!(result.def_eq_cache_entries, 4);
    assert_eq!(result.proof_state_cache_entries, 0);
}

#[tokio::test]
async fn test_get_cache_metrics_records_from_type_checker() {
    let state = ServerState::new();

    let params = GetTypeParams {
        expr: "fun (A : Type) (x : A) => x".to_string(),
    };
    let get_type_response = handle_get_type(&state, RequestId::Number(1), params).await;
    assert!(
        get_type_response.error.is_none(),
        "unexpected get_type error: {:?}",
        get_type_response.error
    );

    let response = handle_get_cache_metrics(&state, RequestId::Number(2)).await;
    assert!(
        response.error.is_none(),
        "unexpected error: {:?}",
        response.error
    );
    let result: GetCacheMetricsResult = serde_json::from_value(response.result.unwrap()).unwrap();

    assert!(
        result.type_cache.is_none(),
        "type cache should be None when not explicitly enabled, got: {:?}",
        result.type_cache
    );
    assert_eq!(
        result.whnf_cache_entries,
        state
            .cache_metrics
            .whnf_cache_entries
            .load(Ordering::Relaxed)
    );
    assert_eq!(
        result.def_eq_cache_entries,
        state
            .cache_metrics
            .def_eq_cache_entries
            .load(Ordering::Relaxed)
    );
}

#[tokio::test]
async fn test_get_cache_metrics_evicts_expired_proof_states() {
    let mut state = ServerState::new();
    state.proof_cache = crate::proof_state::ProofStateCache::new(ProofStateCacheConfig {
        max_states: 4,
        default_ttl: Duration::from_millis(1),
    });

    let env = Environment::new();
    let goal = Expr::sort(Level::zero());
    let proof_state = ProofState::new(env, goal);
    let _id = state.proof_cache.insert(proof_state, None, None, 0);
    assert_eq!(state.proof_cache.len(), 1);

    sleep(Duration::from_millis(5)).await;
    let response = handle_get_cache_metrics(&state, RequestId::Number(1)).await;
    assert!(
        response.error.is_none(),
        "unexpected error: {:?}",
        response.error
    );

    let result: GetCacheMetricsResult = serde_json::from_value(response.result.unwrap()).unwrap();
    assert_eq!(result.proof_state_cache_entries, 0);
    assert_eq!(state.proof_cache.len(), 0);
}

// ========================================================================
// Environment Handler Tests
// ========================================================================
