// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the neural proof oracle module.

use super::*;

/// Mock oracle for testing that returns predefined candidates.
pub struct MockOracle {
    candidates: Vec<OracleCandidate>,
    available: bool,
}

impl MockOracle {
    pub fn new(candidates: Vec<OracleCandidate>) -> Self {
        Self {
            candidates,
            available: true,
        }
    }

    pub fn unavailable() -> Self {
        Self {
            candidates: Vec::new(),
            available: false,
        }
    }
}

impl ProofOracle for MockOracle {
    fn suggest_proof(&self, request: &OracleRequest) -> Result<Vec<OracleCandidate>, OracleError> {
        if !self.available {
            return Err(OracleError::ConnectionFailed(
                "mock oracle unavailable".to_string(),
            ));
        }
        let n = request.num_candidates.min(self.candidates.len());
        Ok(self.candidates[..n].to_vec())
    }

    fn model_id(&self) -> &str {
        "mock-oracle"
    }

    fn is_available(&self) -> bool {
        self.available
    }
}

#[test]
fn test_oracle_request_builder() {
    let request = OracleRequest::new("∀ n : Nat, 0 + n = n")
        .with_hypothesis("n", "Nat")
        .with_lemma("Nat.zero_add", "∀ (n : Nat), 0 + n = n")
        .with_candidates(4)
        .with_temperature(0.8);

    assert_eq!(request.goal, "∀ n : Nat, 0 + n = n");
    assert_eq!(request.hypotheses.len(), 1);
    assert_eq!(request.hypotheses[0].0, "n");
    assert_eq!(request.relevant_lemmas.len(), 1);
    assert_eq!(request.num_candidates, 4);
    assert!((request.temperature - 0.8).abs() < f64::EPSILON);
}

#[test]
fn test_oracle_request_format_prompt() {
    let request = OracleRequest::new("0 + n = n")
        .with_hypothesis("n", "Nat")
        .with_lemma("Nat.zero_add", "∀ (n : Nat), 0 + n = n");

    let prompt = request.format_prompt();
    assert!(prompt.contains("theorem goal"));
    assert!(prompt.contains("(n : Nat)"));
    assert!(prompt.contains(": 0 + n = n := by"));
    assert!(prompt.contains("Nat.zero_add"));
}

#[test]
fn test_oracle_request_format_prompt_no_hypotheses() {
    let request = OracleRequest::new("True");
    let prompt = request.format_prompt();
    assert_eq!(prompt, "theorem goal : True := by\n");
}

#[test]
fn test_mock_oracle_returns_candidates() {
    let oracle = MockOracle::new(vec![
        OracleCandidate::new("exact Nat.zero_add n", 0.95),
        OracleCandidate::new("simp [Nat.zero_add]", 0.80),
        OracleCandidate::new("mathverse", 0.60),
    ]);

    assert!(oracle.is_available());
    assert_eq!(oracle.model_id(), "mock-oracle");

    let request = OracleRequest::new("0 + n = n").with_candidates(2);
    let candidates = oracle.suggest_proof(&request).expect("should succeed");
    assert_eq!(candidates.len(), 2);
    assert!((candidates[0].confidence - 0.95).abs() < f64::EPSILON);
}

#[test]
fn test_mock_oracle_unavailable() {
    let oracle = MockOracle::unavailable();
    assert!(!oracle.is_available());

    let request = OracleRequest::new("True");
    let result = oracle.suggest_proof(&request);
    match result {
        Err(OracleError::ConnectionFailed(_)) => {}
        other => panic!("unavailable oracle should return ConnectionFailed, got: {other:?}"),
    }
}

#[test]
fn test_oracle_candidate_display() {
    let candidate = OracleCandidate::new("exact Nat.zero_add n", 0.95);
    let display = format!("{candidate}");
    assert_eq!(display, "[95.0%] exact Nat.zero_add n");
}

#[test]
fn test_oracle_config_presets() {
    let goedel = OracleConfig::goedel_v2_8b();
    assert_eq!(goedel.model_id, "Goedel-Prover-V2-8B");
    assert!(goedel.use_cot);

    let dsp = OracleConfig::deepseek_prover_v2_7b();
    assert_eq!(dsp.model_id, "DeepSeek-Prover-V2-7B");
    assert_eq!(dsp.max_tokens, 4096);
}

#[test]
fn test_oracle_config_with_endpoint() {
    let config = OracleConfig::goedel_v2_8b().with_endpoint("http://localhost:8080/v1");
    assert_eq!(
        config.endpoint_url.as_deref(),
        Some("http://localhost:8080/v1")
    );
}

#[test]
fn test_oracle_error_display() {
    let err = OracleError::Timeout { timeout_ms: 5000 };
    assert_eq!(err.to_string(), "oracle request timed out after 5000ms");

    let err = OracleError::RateLimited {
        retry_after_ms: 1000,
    };
    assert!(err.to_string().contains("rate limit"));
}
