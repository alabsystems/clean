// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the HTTP oracle backend using a tiny in-process TCP mock server.

use super::http::{strip_code_fence, HttpOracle};
use super::{OracleConfig, OracleError, OracleRequest, ProofOracle};
use std::io::{Read, Write};
use std::net::TcpListener;
use std::time::Duration;

/// Start a tiny single-request mock server that returns the given HTTP response
/// body as a 200 JSON response. Returns the bound address.
fn mock_server_once(json_body: &str) -> (std::thread::JoinHandle<()>, String) {
    let listener = TcpListener::bind("127.0.0.1:0").expect("bind mock server");
    let addr = listener.local_addr().expect("local addr");
    let url = format!("http://{addr}/v1");
    let response = format!(
        "HTTP/1.1 200 OK\r\nContent-Type: application/json\r\nContent-Length: {}\r\n\r\n{}",
        json_body.len(),
        json_body
    );
    let handle = std::thread::spawn(move || {
        if let Ok((mut stream, _)) = listener.accept() {
            let mut buf = vec![0u8; 4096];
            let _ = stream.read(&mut buf);
            let _ = stream.write_all(response.as_bytes());
            let _ = stream.flush();
        }
    });
    (handle, url)
}

/// Start a mock server that returns the given HTTP status code with a body.
fn mock_server_status(status: u16, body: &str) -> (std::thread::JoinHandle<()>, String) {
    let listener = TcpListener::bind("127.0.0.1:0").expect("bind mock server");
    let addr = listener.local_addr().expect("local addr");
    let url = format!("http://{addr}/v1");
    let reason = match status {
        400 => "Bad Request",
        429 => "Too Many Requests",
        500 => "Internal Server Error",
        _ => "Error",
    };
    let response = format!(
        "HTTP/1.1 {status} {reason}\r\nContent-Type: application/json\r\nContent-Length: {}\r\n\r\n{}",
        body.len(),
        body
    );
    let handle = std::thread::spawn(move || {
        if let Ok((mut stream, _)) = listener.accept() {
            let mut buf = vec![0u8; 4096];
            let _ = stream.read(&mut buf);
            let _ = stream.write_all(response.as_bytes());
            let _ = stream.flush();
        }
    });
    (handle, url)
}

fn test_config(endpoint: &str) -> OracleConfig {
    OracleConfig {
        model_id: "test-model".to_string(),
        fallback_model_ids: Vec::new(),
        endpoint_url: Some(endpoint.to_string()),
        api_key: None,
        max_tokens: 256,
        num_candidates: 2,
        temperature: 0.6,
        timeout: Duration::from_secs(5),
        use_cot: false,
    }
}

fn well_formed_response() -> String {
    serde_json::json!({
        "choices": [
            {"index": 0, "message": {"role": "assistant", "content": "simp [Nat.zero_add]"}},
            {"index": 1, "message": {"role": "assistant", "content": "mathverse"}}
        ],
        "usage": {"completion_tokens": 42, "prompt_tokens": 100, "total_tokens": 142}
    })
    .to_string()
}

#[test]
fn test_http_oracle_well_formed_response_returns_sorted_candidates() {
    let (handle, url) = mock_server_once(&well_formed_response());
    let oracle = HttpOracle::new(test_config(&url)).expect("create oracle");
    let request = OracleRequest::new("0 + n = n").with_candidates(2);

    let candidates = oracle.suggest_proof(&request).expect("suggest_proof");
    handle.join().expect("mock server thread");

    assert_eq!(candidates.len(), 2);
    assert_eq!(candidates[0].tactic_text, "simp [Nat.zero_add]");
    assert_eq!(candidates[1].tactic_text, "mathverse");
    // First candidate (index 0) should have higher confidence than second.
    assert!(candidates[0].confidence > candidates[1].confidence);
}

#[test]
fn test_http_oracle_strips_markdown_code_fence() {
    let response = serde_json::json!({
        "choices": [
            {"index": 0, "message": {"role": "assistant", "content": "```lean\nsimp [Nat.add_comm]\n```"}}
        ]
    })
    .to_string();
    let (handle, url) = mock_server_once(&response);
    let oracle = HttpOracle::new(test_config(&url)).expect("create oracle");
    let request = OracleRequest::new("a + b = b + a").with_candidates(1);

    let candidates = oracle.suggest_proof(&request).expect("suggest_proof");
    handle.join().expect("mock server thread");

    assert_eq!(candidates.len(), 1);
    assert_eq!(candidates[0].tactic_text, "simp [Nat.add_comm]");
}

#[test]
fn test_http_oracle_malformed_json_returns_invalid_response() {
    let (handle, url) = mock_server_once("this is not json at all");
    let oracle = HttpOracle::new(test_config(&url)).expect("create oracle");
    let request = OracleRequest::new("True").with_candidates(1);

    let result = oracle.suggest_proof(&request);
    handle.join().expect("mock server thread");

    match result {
        Err(OracleError::InvalidResponse(msg)) => {
            assert!(msg.contains("invalid JSON"), "got: {msg}");
        }
        other => panic!("expected InvalidResponse, got: {other:?}"),
    }
}

#[test]
fn test_http_oracle_empty_choices_returns_invalid_response() {
    let response = serde_json::json!({"choices": []}).to_string();
    let (handle, url) = mock_server_once(&response);
    let oracle = HttpOracle::new(test_config(&url)).expect("create oracle");
    let request = OracleRequest::new("True").with_candidates(1);

    let result = oracle.suggest_proof(&request);
    handle.join().expect("mock server thread");

    match result {
        Err(OracleError::InvalidResponse(msg)) => {
            assert!(msg.contains("empty choices"), "got: {msg}");
        }
        other => panic!("expected InvalidResponse for empty choices, got: {other:?}"),
    }
}

#[test]
fn test_http_oracle_server_error_returns_model_error() {
    let (handle, url) = mock_server_status(500, r#"{"error": "internal"}"#);
    let oracle = HttpOracle::new(test_config(&url)).expect("create oracle");
    let request = OracleRequest::new("True").with_candidates(1);

    let result = oracle.suggest_proof(&request);
    handle.join().expect("mock server thread");

    match result {
        Err(OracleError::ModelError(msg)) => {
            assert!(msg.contains("500"), "got: {msg}");
        }
        other => panic!("expected ModelError for 500, got: {other:?}"),
    }
}

#[test]
fn test_http_oracle_rate_limit_returns_rate_limited() {
    let (handle, url) = mock_server_status(429, r#"{"error": "rate limited"}"#);
    let oracle = HttpOracle::new(test_config(&url)).expect("create oracle");
    let request = OracleRequest::new("True").with_candidates(1);

    let result = oracle.suggest_proof(&request);
    handle.join().expect("mock server thread");

    match result {
        Err(OracleError::RateLimited { .. }) => {}
        other => panic!("expected RateLimited for 429, got: {other:?}"),
    }
}

#[test]
fn test_http_oracle_connection_refused_returns_connection_failed() {
    // Use a port that nothing is listening on.
    let config = OracleConfig {
        endpoint_url: Some("http://127.0.0.1:1".to_string()),
        timeout: Duration::from_secs(1),
        ..test_config("http://127.0.0.1:1")
    };
    let oracle = HttpOracle::new(config).expect("create oracle");
    let request = OracleRequest::new("True").with_candidates(1);

    let result = oracle.suggest_proof(&request);

    match result {
        Err(OracleError::ConnectionFailed(_)) => {}
        Err(OracleError::Timeout { .. }) => {} // also acceptable on some platforms
        other => panic!("expected ConnectionFailed or Timeout, got: {other:?}"),
    }
}

#[test]
fn test_http_oracle_is_available_returns_true_for_reachable_endpoint() {
    let (handle, url) = mock_server_status(400, r#"{"error": "bad request"}"#);
    let oracle = HttpOracle::new(test_config(&url)).expect("create oracle");

    let available = oracle.is_available();
    handle.join().expect("mock server thread");

    assert!(available, "reachable endpoint should report available");
}

#[test]
fn test_http_oracle_is_available_returns_false_for_unreachable_endpoint() {
    let config = OracleConfig {
        endpoint_url: Some("http://127.0.0.1:1".to_string()),
        timeout: Duration::from_secs(1),
        ..test_config("http://127.0.0.1:1")
    };
    let oracle = HttpOracle::new(config).expect("create oracle");

    assert!(!oracle.is_available());
}

#[test]
fn test_http_oracle_not_configured_returns_error() {
    let config = OracleConfig {
        endpoint_url: None,
        ..OracleConfig::default()
    };
    match HttpOracle::new(config) {
        Err(OracleError::NotConfigured) => {}
        Ok(_) => panic!("expected NotConfigured, got Ok"),
        Err(e) => panic!("expected NotConfigured, got: {e:?}"),
    }
}

#[test]
fn test_http_oracle_preserves_reasoning_content() {
    let response = serde_json::json!({
        "choices": [
            {
                "index": 0,
                "message": {
                    "role": "assistant",
                    "content": "exact Nat.zero_add n",
                    "reasoning_content": "The goal follows from Nat.zero_add"
                }
            }
        ]
    })
    .to_string();
    let (handle, url) = mock_server_once(&response);
    let oracle = HttpOracle::new(test_config(&url)).expect("create oracle");
    let request = OracleRequest::new("0 + n = n").with_candidates(1);

    let candidates = oracle.suggest_proof(&request).expect("suggest_proof");
    handle.join().expect("mock server thread");

    assert_eq!(candidates.len(), 1);
    assert_eq!(
        candidates[0].reasoning.as_deref(),
        Some("The goal follows from Nat.zero_add")
    );
}

#[test]
fn test_http_oracle_records_metrics() {
    let (handle, url) = mock_server_once(&well_formed_response());
    let oracle = HttpOracle::new(test_config(&url)).expect("create oracle");
    let request = OracleRequest::new("0 + n = n").with_candidates(2);

    let _ = oracle.suggest_proof(&request).expect("suggest_proof");
    handle.join().expect("mock server thread");

    let metrics = oracle.last_metrics().expect("should have metrics");
    assert_eq!(metrics.model_id, "test-model");
    assert_eq!(metrics.candidates_returned, 2);
    assert_eq!(metrics.total_tokens, 42);
    assert!(metrics.latency_ms < 5000);
}

#[test]
fn test_strip_code_fence_helper() {
    assert_eq!(strip_code_fence("simp"), "simp");
    assert_eq!(strip_code_fence("```lean\nsimp\n```"), "simp");
    assert_eq!(strip_code_fence("```\nsimp\n```"), "simp");
    assert_eq!(
        strip_code_fence("```lean\nsimp [h]\nmathverse\n```"),
        "simp [h]\nmathverse"
    );
    // Single line with backticks should NOT be stripped (no closing fence).
    assert_eq!(strip_code_fence("```lean"), "```lean");
}
