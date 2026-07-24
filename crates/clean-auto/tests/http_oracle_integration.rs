// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Integration test: prove that [`HttpOracle`] can drive the oracle seam
//! from `clean-auto` with a mock AI Provider-compatible endpoint.
//!
//! This test exercises the hosted adapter through `ProofOracle::suggest_proof`
//! and then feeds the candidates through an `OracleCandidateRunner` — the same
//! flow that `AutomationEngine::try_oracle_detailed` uses internally.

#![cfg(feature = "oracle-http")]

use clean_auto::oracle::{
    HttpOracle, OracleCandidateRunner, OracleConfig, OracleRequest, OracleRunError, ProofOracle,
};
use clean_auto::ProofResult;
use clean_kernel::{Environment, Expr, LocalContext, Name};
use std::io::{Read, Write};
use std::net::TcpListener;
use std::time::Duration;

use clean_auto::oracle::OracleCandidate;

/// A runner that "verifies" every candidate by returning a synthetic proof.
struct IntegrationRunner;

impl OracleCandidateRunner for IntegrationRunner {
    fn try_candidate(
        &self,
        _env: &Environment,
        _local_ctx: Option<&LocalContext>,
        _goal: &Expr,
        _candidate: &OracleCandidate,
        _timeout: Duration,
    ) -> Result<Option<ProofResult>, OracleRunError> {
        Ok(Some(ProofResult::new(
            Expr::const_(Name::from_string("oracle_proof"), vec![]),
            "oracle-integration-test",
            0,
            None,
        )))
    }
}

/// Single-request mock server returning a 200 JSON response.
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
            let mut buf = vec![0u8; 8192];
            let _ = stream.read(&mut buf);
            let _ = stream.write_all(response.as_bytes());
            let _ = stream.flush();
        }
    });
    (handle, url)
}

/// End-to-end test: HttpOracle → suggest_proof → OracleCandidateRunner
///
/// This exercises the same code path as `AutomationEngine::try_oracle_detailed`
/// without going through the SMT/superposition fallback chain.
#[test]
fn test_http_oracle_suggest_then_runner_verifies() {
    let response = serde_json::json!({
        "choices": [
            {
                "index": 0,
                "message": {
                    "role": "assistant",
                    "content": "exact test_goal_proof"
                }
            }
        ],
        "usage": {"completion_tokens": 10}
    })
    .to_string();

    let (handle, url) = mock_server_once(&response);

    let config = OracleConfig {
        model_id: "integration-test-model".to_string(),
        fallback_model_ids: Vec::new(),
        endpoint_url: Some(url),
        api_key: None,
        max_tokens: 128,
        num_candidates: 1,
        temperature: 0.0,
        timeout: Duration::from_secs(5),
        use_cot: false,
    };

    let oracle = HttpOracle::new(config).expect("create HttpOracle");

    // Step 1: suggest_proof (calls the mock endpoint).
    let request = OracleRequest::new("∀ n : Nat, n = n").with_candidates(1);
    let candidates = oracle.suggest_proof(&request).expect("suggest_proof");
    handle.join().expect("mock server thread");

    assert_eq!(candidates.len(), 1);
    assert_eq!(candidates[0].tactic_text, "exact test_goal_proof");

    // Step 2: feed candidates through the runner (mirrors try_oracle_detailed).
    let env = Environment::new();
    let goal = Expr::prop();
    let runner = IntegrationRunner;

    for candidate in &candidates {
        let result = runner
            .try_candidate(&env, None, &goal, candidate, Duration::from_secs(1))
            .expect("runner should not fail");
        let proof = result.expect("runner should verify candidate");
        assert_eq!(proof.proof_text(), "oracle-integration-test");
    }

    // Verify metrics were recorded.
    let metrics = oracle.last_metrics().expect("metrics should be recorded");
    assert_eq!(metrics.model_id, "integration-test-model");
    assert_eq!(metrics.total_tokens, 10);
    assert_eq!(metrics.candidates_returned, 1);
}
