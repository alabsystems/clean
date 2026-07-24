// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Discovery oracle runner: bridges LLM oracle responses to `CandidateTheorem`.
//!
//! Takes raw tactic/proof text from commercial LLM backends and parses it into
//! `CandidateTheorem` values that the kernel can verify.

use crate::candidate::{CandidateId, CandidateTheorem, ParamVec};
use crate::error::DiscoveryError;
use crate::family::TheoremFamily;
use clean_auto::oracle::{OracleCandidate, OracleError, ProofOracle};

use super::prompt::DiscoveryPrompt;

/// Runs LLM oracle queries and converts responses to discovery candidates.
///
/// The runner holds a reference to a [`ProofOracle`] backend (AI Model, AI Model,
/// AI Provider, or HTTP) and a base candidate ID counter. Each call to
/// [`generate`](Self::generate) queries the oracle and produces
/// `CandidateTheorem` values with tactic text stored in the proof field
/// as `Expr::lit_str` for downstream tactic execution.
pub struct DiscoveryOracleRunner<'a> {
    oracle: &'a dyn ProofOracle,
    next_id: u64,
}

impl<'a> DiscoveryOracleRunner<'a> {
    /// Create a new runner backed by the given oracle.
    pub fn new(oracle: &'a dyn ProofOracle) -> Self {
        Self { oracle, next_id: 0 }
    }

    /// Create a runner with a starting candidate ID offset.
    ///
    /// Useful when combining oracle candidates with parametric search candidates
    /// to avoid ID collisions.
    pub fn with_id_offset(oracle: &'a dyn ProofOracle, offset: u64) -> Self {
        Self {
            oracle,
            next_id: offset,
        }
    }

    /// Query the oracle and generate discovery candidates.
    ///
    /// Sends the prompt to the LLM, parses the response, and wraps each
    /// candidate tactic sequence as a `CandidateTheorem`. The theorem
    /// statement is set to `Prop` (a placeholder; the kernel will infer
    /// the actual type from the proof term). The proof field contains
    /// `Expr::lit_str` with the raw tactic text for later execution.
    ///
    /// # Errors
    ///
    /// Returns `DiscoveryError` if the oracle call fails or returns
    /// no usable candidates.
    pub fn generate(
        &mut self,
        prompt: &DiscoveryPrompt,
    ) -> Result<Vec<CandidateTheorem>, DiscoveryError> {
        let request = prompt.to_oracle_request();
        let candidates = self
            .oracle
            .suggest_proof(&request)
            .map_err(oracle_to_discovery_error)?;

        if candidates.is_empty() {
            return Err(DiscoveryError::NoCandidates {
                family: prompt.family.to_string(),
            });
        }

        let theorems = candidates
            .iter()
            .map(|c| self.candidate_to_theorem(c, prompt.family))
            .collect();

        Ok(theorems)
    }

    /// Check if the underlying oracle is available.
    pub fn is_available(&self) -> bool {
        self.oracle.is_available()
    }

    /// Get the model identifier of the underlying oracle.
    pub fn model_id(&self) -> &str {
        self.oracle.model_id()
    }

    /// Get the last oracle call metrics, if available.
    pub fn last_metrics(&self) -> Option<clean_auto::oracle::OracleMetrics> {
        self.oracle.last_metrics()
    }

    /// Convert a single oracle candidate to a discovery `CandidateTheorem`.
    fn candidate_to_theorem(
        &mut self,
        candidate: &OracleCandidate,
        family: TheoremFamily,
    ) -> CandidateTheorem {
        let id = CandidateId(self.next_id);
        self.next_id += 1;

        // Store the tactic text as a string literal expression. The discovery
        // runner can later feed this to the tactic framework for execution.
        let proof = clean_kernel::Expr::str_lit(&candidate.tactic_text);

        CandidateTheorem {
            id,
            family,
            params: ParamVec::new(),
            statement: clean_kernel::Expr::prop(),
            proof: Some(proof),
        }
    }
}

/// Map `OracleError` to `DiscoveryError`.
fn oracle_to_discovery_error(err: OracleError) -> DiscoveryError {
    match err {
        OracleError::NotConfigured => DiscoveryError::InvalidConfig {
            reason: "oracle not configured: missing API key".to_string(),
        },
        OracleError::Timeout { timeout_ms } => DiscoveryError::InvalidConfig {
            reason: format!("oracle timed out after {timeout_ms}ms"),
        },
        OracleError::RateLimited { retry_after_ms } => DiscoveryError::InvalidConfig {
            reason: format!("oracle rate limited, retry after {retry_after_ms}ms"),
        },
        OracleError::ConnectionFailed(msg) => DiscoveryError::InvalidConfig {
            reason: format!("oracle connection failed: {msg}"),
        },
        OracleError::InvalidResponse(msg) => DiscoveryError::InvalidConfig {
            reason: format!("oracle returned invalid response: {msg}"),
        },
        OracleError::ModelError(msg) => DiscoveryError::InvalidConfig {
            reason: format!("oracle model error: {msg}"),
        },
        OracleError::Other(msg) => DiscoveryError::InvalidConfig {
            reason: format!("oracle error: {msg}"),
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_auto::oracle::{OracleMetrics, ProofTermCandidate};

    /// Mock oracle for testing that returns canned responses.
    struct MockOracle {
        responses: Vec<OracleCandidate>,
        model: String,
    }

    impl MockOracle {
        fn new(responses: Vec<OracleCandidate>) -> Self {
            Self {
                responses,
                model: "mock-model".to_string(),
            }
        }
    }

    impl ProofOracle for MockOracle {
        fn suggest_proof(
            &self,
            _request: &clean_auto::oracle::OracleRequest,
        ) -> Result<Vec<OracleCandidate>, OracleError> {
            Ok(self.responses.clone())
        }

        fn suggest_proof_term(
            &self,
            _request: &clean_auto::oracle::OracleRequest,
        ) -> Result<Vec<ProofTermCandidate>, OracleError> {
            Ok(Vec::new())
        }

        fn model_id(&self) -> &str {
            &self.model
        }

        fn is_available(&self) -> bool {
            true
        }

        fn last_metrics(&self) -> Option<OracleMetrics> {
            None
        }
    }

    /// Mock oracle that always fails.
    struct FailingOracle;

    impl ProofOracle for FailingOracle {
        fn suggest_proof(
            &self,
            _request: &clean_auto::oracle::OracleRequest,
        ) -> Result<Vec<OracleCandidate>, OracleError> {
            Err(OracleError::ConnectionFailed("mock failure".to_string()))
        }

        fn suggest_proof_term(
            &self,
            _request: &clean_auto::oracle::OracleRequest,
        ) -> Result<Vec<ProofTermCandidate>, OracleError> {
            Err(OracleError::ConnectionFailed("mock failure".to_string()))
        }

        fn model_id(&self) -> &str {
            "failing-model"
        }

        fn is_available(&self) -> bool {
            false
        }
    }

    #[test]
    fn test_discovery_oracle_runner_generates_candidates() {
        let oracle = MockOracle::new(vec![
            OracleCandidate::new("exact Nat.zero_add n", 0.9),
            OracleCandidate::new("simp [Nat.add_comm]", 0.7),
        ]);
        let mut runner = DiscoveryOracleRunner::new(&oracle);
        let prompt = DiscoveryPrompt::new(TheoremFamily::CertSizeBound).with_num_candidates(2);

        let candidates = runner.generate(&prompt).expect("should generate");
        assert_eq!(candidates.len(), 2);
        assert_eq!(candidates[0].id, CandidateId(0));
        assert_eq!(candidates[1].id, CandidateId(1));
        assert_eq!(candidates[0].family, TheoremFamily::CertSizeBound);
        assert!(candidates[0].proof.is_some());
    }

    #[test]
    fn test_discovery_oracle_runner_increments_ids() {
        let oracle = MockOracle::new(vec![OracleCandidate::new("mathverse", 0.5)]);
        let mut runner = DiscoveryOracleRunner::with_id_offset(&oracle, 100);
        let prompt = DiscoveryPrompt::new(TheoremFamily::DomainTightness);

        let batch1 = runner.generate(&prompt).expect("batch 1");
        assert_eq!(batch1[0].id, CandidateId(100));

        let batch2 = runner.generate(&prompt).expect("batch 2");
        assert_eq!(batch2[0].id, CandidateId(101));
    }

    #[test]
    fn test_discovery_oracle_runner_handles_oracle_failure() {
        let oracle = FailingOracle;
        let mut runner = DiscoveryOracleRunner::new(&oracle);
        let prompt = DiscoveryPrompt::new(TheoremFamily::CertSizeBound);

        let result = runner.generate(&prompt);
        assert!(result.is_err());
        let err = result.unwrap_err();
        assert!(
            err.to_string().contains("connection failed"),
            "expected connection failure, got: {err}"
        );
    }

    #[test]
    fn test_discovery_oracle_runner_empty_response() {
        let oracle = MockOracle::new(vec![]);
        let mut runner = DiscoveryOracleRunner::new(&oracle);
        let prompt = DiscoveryPrompt::new(TheoremFamily::NewAbstractDomain);

        let result = runner.generate(&prompt);
        assert!(result.is_err());
        let err = result.unwrap_err();
        assert!(
            err.to_string().contains("no candidates"),
            "expected NoCandidates, got: {err}"
        );
    }

    #[test]
    fn test_discovery_oracle_runner_model_id() {
        let oracle = MockOracle::new(vec![]);
        let runner = DiscoveryOracleRunner::new(&oracle);
        assert_eq!(runner.model_id(), "mock-model");
    }

    #[test]
    fn test_discovery_oracle_runner_is_available() {
        let oracle = MockOracle::new(vec![]);
        let runner = DiscoveryOracleRunner::new(&oracle);
        assert!(runner.is_available());

        let failing = FailingOracle;
        let runner2 = DiscoveryOracleRunner::new(&failing);
        assert!(!runner2.is_available());
    }
}
