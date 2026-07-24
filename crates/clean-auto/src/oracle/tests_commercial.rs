// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the commercial LLM oracle backends (AI Model, AI Model, AI Provider).
//!
//! Uses in-process TCP mock servers to validate request formatting and
//! response parsing without hitting real APIs.

use super::claude::ClaudeOracle;
use super::gemini::GeminiOracle;
use super::openai::OpenAiOracle;
use super::{OracleConfig, OracleError, OracleRequest, ProofOracle};
use std::io::{Read, Write};
use std::net::TcpListener;
use std::time::Duration;

// ============================================================================
// Test helpers
// ============================================================================

/// Start a mock server that captures the request and returns a JSON response.
fn mock_server_json(json_body: &str) -> (std::thread::JoinHandle<Vec<u8>>, String) {
    let listener = TcpListener::bind("127.0.0.1:0").expect("bind");
    let addr = listener.local_addr().expect("addr");
    let url = format!("http://{addr}");
    let response = format!(
        "HTTP/1.1 200 OK\r\nContent-Type: application/json\r\nContent-Length: {}\r\n\r\n{}",
        json_body.len(),
        json_body
    );
    let handle = std::thread::spawn(move || {
        let mut captured = Vec::new();
        if let Ok((mut stream, _)) = listener.accept() {
            let mut buf = vec![0u8; 8192];
            if let Ok(n) = stream.read(&mut buf) {
                captured.extend_from_slice(&buf[..n]);
            }
            let _ = stream.write_all(response.as_bytes());
            let _ = stream.flush();
        }
        captured
    });
    (handle, url)
}

fn test_config(endpoint: &str) -> OracleConfig {
    OracleConfig {
        model_id: "test-model".to_string(),
        fallback_model_ids: Vec::new(),
        endpoint_url: Some(endpoint.to_string()),
        api_key: Some("test-key-12345".to_string()),
        max_tokens: 256,
        num_candidates: 2,
        temperature: 0.4,
        timeout: Duration::from_secs(5),
        use_cot: false,
    }
}

// ============================================================================
// AI Model oracle tests
// ============================================================================

fn claude_response(text: &str) -> String {
    serde_json::json!({
        "content": [{"type": "text", "text": text}],
        "usage": {"input_tokens": 50, "output_tokens": 20}
    })
    .to_string()
}

#[test]
fn test_claude_oracle_parses_single_candidate() {
    let (handle, url) = mock_server_json(&claude_response("exact Nat.zero_add n"));
    let oracle = ClaudeOracle::new(test_config(&url)).expect("create");
    let request = OracleRequest::new("0 + n = n").with_candidates(1);

    let candidates = oracle.suggest_proof(&request).expect("suggest");
    let captured = handle.join().expect("join");

    assert_eq!(candidates.len(), 1);
    assert_eq!(candidates[0].tactic_text, "exact Nat.zero_add n");

    // Verify auth header was sent.
    let req_str = String::from_utf8_lossy(&captured);
    assert!(req_str.contains("x-api-key: test-key-12345"));
    assert!(req_str.contains("AI Provider-version: 2023-06-01"));
}

#[test]
fn test_claude_oracle_splits_multiple_candidates() {
    let response = claude_response("exact Nat.zero_add n\n\nsimp [Nat.zero_add]\n\nmathverse");
    let (handle, url) = mock_server_json(&response);
    let oracle = ClaudeOracle::new(test_config(&url)).expect("create");
    let request = OracleRequest::new("0 + n = n").with_candidates(3);

    let candidates = oracle.suggest_proof(&request).expect("suggest");
    handle.join().expect("join");

    assert_eq!(candidates.len(), 3);
    assert_eq!(candidates[0].tactic_text, "exact Nat.zero_add n");
    assert_eq!(candidates[1].tactic_text, "simp [Nat.zero_add]");
    assert_eq!(candidates[2].tactic_text, "mathverse");
}

#[test]
fn test_claude_oracle_strips_code_fence() {
    let response = claude_response("```lean\nsimp [Nat.add_comm]\n```");
    let (handle, url) = mock_server_json(&response);
    let oracle = ClaudeOracle::new(test_config(&url)).expect("create");
    let request = OracleRequest::new("a + b = b + a").with_candidates(1);

    let candidates = oracle.suggest_proof(&request).expect("suggest");
    handle.join().expect("join");

    assert_eq!(candidates[0].tactic_text, "simp [Nat.add_comm]");
}

#[test]
fn test_claude_oracle_not_configured_without_key() {
    let config = OracleConfig {
        api_key: None,
        ..test_config("http://localhost:1")
    };
    match ClaudeOracle::new(config) {
        Err(OracleError::NotConfigured) => {}
        other => panic!("expected NotConfigured, got: {other:?}"),
    }
}

#[test]
fn test_claude_oracle_records_metrics() {
    let (handle, url) = mock_server_json(&claude_response("mathverse"));
    let oracle = ClaudeOracle::new(test_config(&url)).expect("create");
    let request = OracleRequest::new("True").with_candidates(1);

    let _ = oracle.suggest_proof(&request).expect("suggest");
    handle.join().expect("join");

    let metrics = oracle.last_metrics().expect("metrics");
    assert_eq!(metrics.model_id, "test-model");
    assert_eq!(metrics.total_tokens, 20);
    assert!(metrics.latency_ms < 5000);
}

// ============================================================================
// AI Model oracle tests
// ============================================================================

fn gemini_response_single(text: &str) -> String {
    serde_json::json!({
        "candidates": [
            {"content": {"role": "model", "parts": [{"text": text}]}}
        ],
        "usageMetadata": {"promptTokenCount": 40, "candidatesTokenCount": 15}
    })
    .to_string()
}

fn gemini_response_multi(texts: &[&str]) -> String {
    let candidates: Vec<_> = texts
        .iter()
        .map(|t| serde_json::json!({"content": {"role": "model", "parts": [{"text": t}]}}))
        .collect();
    serde_json::json!({
        "candidates": candidates,
        "usageMetadata": {"promptTokenCount": 40, "candidatesTokenCount": 30}
    })
    .to_string()
}

#[test]
fn test_gemini_oracle_parses_single_candidate() {
    let (handle, url) = mock_server_json(&gemini_response_single("exact Nat.zero_add n"));
    let oracle = GeminiOracle::new(test_config(&url)).expect("create");
    let request = OracleRequest::new("0 + n = n").with_candidates(1);

    let candidates = oracle.suggest_proof(&request).expect("suggest");
    let captured = handle.join().expect("join");

    assert_eq!(candidates.len(), 1);
    assert_eq!(candidates[0].tactic_text, "exact Nat.zero_add n");

    // Verify API key is in URL query param.
    let req_str = String::from_utf8_lossy(&captured);
    assert!(req_str.contains("key=test-key-12345"));
}

#[test]
fn test_gemini_oracle_parses_multiple_candidates() {
    let response = gemini_response_multi(&["exact Nat.zero_add n", "mathverse"]);
    let (handle, url) = mock_server_json(&response);
    let oracle = GeminiOracle::new(test_config(&url)).expect("create");
    let request = OracleRequest::new("0 + n = n").with_candidates(2);

    let candidates = oracle.suggest_proof(&request).expect("suggest");
    handle.join().expect("join");

    assert_eq!(candidates.len(), 2);
    assert_eq!(candidates[0].tactic_text, "exact Nat.zero_add n");
    assert_eq!(candidates[1].tactic_text, "mathverse");
    assert!(candidates[0].confidence > candidates[1].confidence);
}

#[test]
fn test_gemini_oracle_strips_code_fence() {
    let response = gemini_response_single("```lean\nsimp\n```");
    let (handle, url) = mock_server_json(&response);
    let oracle = GeminiOracle::new(test_config(&url)).expect("create");
    let request = OracleRequest::new("True").with_candidates(1);

    let candidates = oracle.suggest_proof(&request).expect("suggest");
    handle.join().expect("join");

    assert_eq!(candidates[0].tactic_text, "simp");
}

#[test]
fn test_gemini_oracle_not_configured_without_key() {
    let config = OracleConfig {
        api_key: None,
        ..test_config("http://localhost:1")
    };
    match GeminiOracle::new(config) {
        Err(OracleError::NotConfigured) => {}
        other => panic!("expected NotConfigured, got: {other:?}"),
    }
}

#[test]
fn test_gemini_oracle_records_metrics() {
    let (handle, url) = mock_server_json(&gemini_response_single("mathverse"));
    let oracle = GeminiOracle::new(test_config(&url)).expect("create");
    let request = OracleRequest::new("True").with_candidates(1);

    let _ = oracle.suggest_proof(&request).expect("suggest");
    handle.join().expect("join");

    let metrics = oracle.last_metrics().expect("metrics");
    assert_eq!(metrics.total_tokens, 15);
}

// ============================================================================
// AI Provider oracle tests
// ============================================================================

fn openai_response(choices: &[(&str, usize)]) -> String {
    let choices: Vec<_> = choices
        .iter()
        .map(|(text, idx)| {
            serde_json::json!({"index": idx, "message": {"role": "assistant", "content": text}})
        })
        .collect();
    serde_json::json!({
        "choices": choices,
        "usage": {"completion_tokens": 25, "prompt_tokens": 60, "total_tokens": 85}
    })
    .to_string()
}

#[test]
fn test_openai_oracle_parses_response() {
    let response = openai_response(&[("exact Nat.zero_add n", 0), ("mathverse", 1)]);
    let (handle, url) = mock_server_json(&response);
    let oracle = OpenAiOracle::new(test_config(&url)).expect("create");
    let request = OracleRequest::new("0 + n = n").with_candidates(2);

    let candidates = oracle.suggest_proof(&request).expect("suggest");
    let captured = handle.join().expect("join");

    assert_eq!(candidates.len(), 2);
    assert_eq!(candidates[0].tactic_text, "exact Nat.zero_add n");
    assert_eq!(candidates[1].tactic_text, "mathverse");

    // Verify Bearer auth header.
    let req_str = String::from_utf8_lossy(&captured);
    assert!(
        req_str.contains("authorization: Bearer test-key-12345")
            || req_str.contains("Authorization: Bearer test-key-12345"),
        "expected Authorization header in request: {req_str}"
    );
}

#[test]
fn test_openai_oracle_strips_code_fence() {
    let response = openai_response(&[("```lean\nsimp [Nat.add_comm]\n```", 0)]);
    let (handle, url) = mock_server_json(&response);
    let oracle = OpenAiOracle::new(test_config(&url)).expect("create");
    let request = OracleRequest::new("a + b = b + a").with_candidates(1);

    let candidates = oracle.suggest_proof(&request).expect("suggest");
    handle.join().expect("join");

    assert_eq!(candidates[0].tactic_text, "simp [Nat.add_comm]");
}

#[test]
fn test_openai_oracle_preserves_reasoning() {
    let response = serde_json::json!({
        "choices": [{
            "index": 0,
            "message": {
                "role": "assistant",
                "content": "exact Nat.zero_add n",
                "reasoning_content": "Direct application of zero_add lemma"
            }
        }],
        "usage": {"completion_tokens": 10}
    })
    .to_string();
    let (handle, url) = mock_server_json(&response);
    let oracle = OpenAiOracle::new(test_config(&url)).expect("create");
    let request = OracleRequest::new("0 + n = n").with_candidates(1);

    let candidates = oracle.suggest_proof(&request).expect("suggest");
    handle.join().expect("join");

    assert_eq!(
        candidates[0].reasoning.as_deref(),
        Some("Direct application of zero_add lemma")
    );
}

#[test]
fn test_openai_oracle_not_configured_without_key() {
    let config = OracleConfig {
        api_key: None,
        ..test_config("http://localhost:1")
    };
    match OpenAiOracle::new(config) {
        Err(OracleError::NotConfigured) => {}
        other => panic!("expected NotConfigured, got: {other:?}"),
    }
}

#[test]
fn test_openai_oracle_records_metrics() {
    let response = openai_response(&[("mathverse", 0)]);
    let (handle, url) = mock_server_json(&response);
    let oracle = OpenAiOracle::new(test_config(&url)).expect("create");
    let request = OracleRequest::new("True").with_candidates(1);

    let _ = oracle.suggest_proof(&request).expect("suggest");
    handle.join().expect("join");

    let metrics = oracle.last_metrics().expect("metrics");
    assert_eq!(metrics.model_id, "test-model");
    assert_eq!(metrics.total_tokens, 25);
}

// ============================================================================
// Config preset tests
// ============================================================================

#[test]
fn test_config_claude_opus_preset() {
    let config = OracleConfig::claude_opus();
    assert_eq!(config.model_id, "AI Model-opus-4-6-20260410");
    assert!(config
        .endpoint_url
        .as_deref()
        .unwrap()
        .contains("AI Provider"));
    assert_eq!(config.max_tokens, 4096);
}

#[test]
fn test_config_gemini_pro_preset() {
    let config = OracleConfig::gemini_pro();
    assert_eq!(config.model_id, "AI Model-3.1-pro");
    assert!(config
        .endpoint_url
        .as_deref()
        .unwrap()
        .contains("googleapis"));
}

#[test]
fn test_config_openai_o4_mini_preset() {
    let config = OracleConfig::openai_o4_mini();
    assert_eq!(config.model_id, "o4-mini");
    assert!(config
        .endpoint_url
        .as_deref()
        .unwrap()
        .contains("AI Provider"));
}

#[test]
fn test_config_with_api_key_builder() {
    let config = OracleConfig::default().with_api_key("sk-test");
    assert_eq!(config.api_key.as_deref(), Some("sk-test"));
}

// ============================================================================
// Trait object compatibility
// ============================================================================

#[test]
fn test_commercial_oracles_are_object_safe() {
    // Verify all three backends can be used as trait objects (compile-time check).
    fn accept_oracle(_oracle: &dyn ProofOracle) {}

    let config = test_config("http://127.0.0.1:1");
    let claude = ClaudeOracle::new(config.clone()).expect("create");
    let gemini = GeminiOracle::new(config.clone()).expect("create");
    let openai = OpenAiOracle::new(config).expect("create");

    accept_oracle(&claude);
    accept_oracle(&gemini);
    accept_oracle(&openai);
}
