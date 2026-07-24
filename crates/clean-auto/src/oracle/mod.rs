// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Neural proof oracle interface for clean.
//!
//! Provides a model-agnostic trait for neural theorem provers (e.g.,
//! Goedel-Prover-V2-8B, DeepSeek-Prover-V2-7B) to integrate with clean's
//! proof search pipeline.
//!
//! # Architecture
//!
//! ```text
//! clean proof search
//!   ├─ native tactics (100+)
//!   ├─ SMT bridge (ay)
//!   └─ neural oracle ← Goedel-Prover-V2-8B (primary)
//!                     ← DSP-V2-7B (secondary, subgoal decomposition)
//! ```
//!
//! The oracle receives a proof goal (pretty-printed Lean 4 syntax) and
//! returns candidate tactic sequences. clean parses and executes these
//! tactics, type-checking the resulting proof terms at sub-microsecond
//! speed. This verification speed enables 1000x more search iterations
//! than stock Lean 4.
//!
//! # Usage
//!
//! Implementors provide a concrete [`ProofOracle`] (e.g., backed by MLX,
//! llama.cpp, vLLM, or an HTTP API). The tactic framework calls
//! [`ProofOracle::suggest_proof`] and executes returned candidates.
//!
//! ```text
//! // 1. Create oracle with the HTTP backend (requires `oracle-http` feature)
//! use clean_auto::oracle::{HttpOracle, OracleConfig, OracleRequest};
//!
//! let config = OracleConfig::goedel_v2_8b()
//!     .with_endpoint("http://localhost:8080/v1");
//! let oracle = HttpOracle::new(config)?;
//!
//! // 2. Build request from proof state
//! let request = OracleRequest::new("∀ n : Nat, 0 + n = n")
//!     .with_hypothesis("n", "Nat")
//!     .with_candidates(8)
//!     .with_temperature(0.6);
//!
//! // 3. Get candidates
//! let candidates = oracle.suggest_proof(&request)?;
//!
//! // 4. Try each candidate (parse + execute + type-check)
//! for candidate in &candidates {
//!     if let Ok(proof) = try_execute_tactic(&candidate.tactic_text) {
//!         return Ok(proof);
//!     }
//! }
//! ```

mod config;

pub use config::OracleConfig;

use crate::ProofResult;
use clean_kernel::{Environment, Expr, LocalContext};
use std::fmt;
use std::time::Duration;
use thiserror::Error;

/// A candidate proof returned by a neural oracle.
///
/// Contains a Lean 4 tactic sequence that, if valid, closes the current goal.
/// Candidates are ranked by confidence score for priority ordering.
#[derive(Debug, Clone)]
pub struct OracleCandidate {
    /// Lean 4 tactic sequence (for example, `intro h\nsimp [h]\nmathverse`)
    pub tactic_text: String,
    /// Model confidence score (0.0 to 1.0, higher = more confident)
    pub confidence: f64,
    /// Optional chain-of-thought reasoning from CoT models
    pub reasoning: Option<String>,
    /// Token count for the generation (for budget tracking)
    pub token_count: Option<u32>,
}

/// A candidate proof term returned directly by a neural oracle.
///
/// Unlike [`OracleCandidate`] (which carries tactic text that must be parsed and
/// executed), a `ProofTermCandidate` carries a kernel [`Expr`] that the engine
/// validates through the type checker immediately. This path avoids the need for
/// an [`OracleCandidateRunner`] and is useful for models that output proof terms
/// in a serialised format (e.g., s-expression or JSON-encoded Expr).
#[derive(Debug, Clone)]
pub struct ProofTermCandidate {
    /// The candidate proof term (kernel `Expr`).
    pub proof_term: Expr,
    /// Model confidence score (0.0 to 1.0, higher = more confident).
    pub confidence: f64,
    /// Optional human-readable description of the proof strategy.
    pub description: Option<String>,
}

/// Request to a neural proof oracle.
///
/// Contains the goal and context needed for the model to generate proof tactics.
/// Pretty-printed in Lean 4 syntax to match model training data format.
#[derive(Debug, Clone)]
pub struct OracleRequest {
    /// The goal type to prove (pretty-printed Lean 4 syntax)
    pub goal: String,
    /// Local hypotheses: (name, type as Lean 4 string)
    pub hypotheses: Vec<(String, String)>,
    /// Relevant lemmas from premise selection: (name, type as Lean 4 string)
    pub relevant_lemmas: Vec<(String, String)>,
    /// Maximum number of candidates to return
    pub num_candidates: usize,
    /// Sampling temperature (0.0 = greedy, 1.0 = diverse)
    pub temperature: f64,
    /// Maximum tokens for generation (model-dependent)
    pub max_tokens: Option<usize>,
}

/// Metrics from an oracle call, for performance tracking and search budget management.
#[derive(Debug, Clone, Default)]
pub struct OracleMetrics {
    /// Total tokens generated across all candidates
    pub total_tokens: u32,
    /// Number of candidates returned
    pub candidates_returned: usize,
    /// Latency of the oracle call in milliseconds
    pub latency_ms: u64,
    /// Model identifier used
    pub model_id: String,
}

/// Errors from oracle operations.
#[derive(Debug, Error)]
pub enum OracleError {
    /// Failed to connect to the oracle backend
    #[error("oracle connection failed: {0}")]
    ConnectionFailed(String),
    /// Oracle call timed out
    #[error("oracle request timed out after {timeout_ms}ms")]
    Timeout {
        /// Timeout duration in milliseconds
        timeout_ms: u64,
    },
    /// Oracle returned unparseable response
    #[error("oracle returned invalid response: {0}")]
    InvalidResponse(String),
    /// No oracle backend is configured
    #[error("no oracle configured")]
    NotConfigured,
    /// Model returned an error
    #[error("model error: {0}")]
    ModelError(String),
    /// Rate limit exceeded
    #[error("oracle rate limit exceeded, retry after {retry_after_ms}ms")]
    RateLimited {
        /// Suggested retry delay in milliseconds
        retry_after_ms: u64,
    },
    /// Other oracle error
    #[error("oracle error: {0}")]
    Other(String),
}

/// Trait for neural proof oracles.
///
/// Implementations connect to model inference servers (MLX, llama.cpp, vLLM,
/// or remote APIs) and return candidate tactic sequences for proof goals.
///
/// # Thread Safety
///
/// Implementations must be `Send + Sync` for use across parallel proof
/// search (e.g., `batchApplyTactic`, `find_first_valid_parallel`).
///
/// # Implementors
///
/// - `HttpOracle`: Calls AI Provider-compatible `/v1/chat/completions` endpoint
///   (works with MLX, llama.cpp, vLLM, or any hosted API). Requires the
///   `oracle-http` feature.
/// - Mock oracle for testing (see tests module)
pub trait ProofOracle: Send + Sync {
    /// Request candidate proofs for a goal.
    ///
    /// Returns up to `request.num_candidates` tactic sequences, sorted by
    /// descending confidence. Each candidate is a complete Lean 4 tactic
    /// sequence that should close the goal if correct.
    ///
    /// # Errors
    ///
    /// Returns [`OracleError`] if the backend is unreachable, times out,
    /// or returns an unparseable response.
    fn suggest_proof(&self, request: &OracleRequest) -> Result<Vec<OracleCandidate>, OracleError>;

    /// Request candidate tactic scripts for a goal.
    ///
    /// This is a semantic alias for [`Self::suggest_proof`] that makes intent
    /// clearer at call sites focused on tactic generation. The default
    /// implementation delegates to `suggest_proof`.
    fn suggest_tactic(&self, request: &OracleRequest) -> Result<Vec<OracleCandidate>, OracleError> {
        self.suggest_proof(request)
    }

    /// Request candidate proof terms for a goal.
    ///
    /// Unlike [`Self::suggest_proof`] / [`Self::suggest_tactic`] which return
    /// tactic text that requires parsing and execution, this method returns
    /// kernel [`Expr`] proof terms that the engine validates directly through
    /// the type checker. This avoids the need for an
    /// [`OracleCandidateRunner`].
    ///
    /// The default implementation returns an empty vec (no proof-term
    /// suggestions). Oracles that can produce serialised proof terms should
    /// override this.
    fn suggest_proof_term(
        &self,
        _request: &OracleRequest,
    ) -> Result<Vec<ProofTermCandidate>, OracleError> {
        Ok(Vec::new())
    }

    /// Model identifier for logging and metrics.
    fn model_id(&self) -> &str;

    /// Check if the oracle backend is available (e.g., server is running).
    ///
    /// This should be a fast check (no model inference). Returns `false` if
    /// the backend is unreachable or not configured.
    fn is_available(&self) -> bool;

    /// Get metrics from the last oracle call, if tracked.
    fn last_metrics(&self) -> Option<OracleMetrics> {
        None
    }
}

/// Errors raised while executing oracle candidates inside a caller-owned runner.
#[derive(Debug, Error)]
pub enum OracleRunError {
    /// Candidate execution ran out of budget.
    #[error("oracle candidate execution timed out after {timeout_ms}ms")]
    Timeout {
        /// Timeout duration in milliseconds.
        timeout_ms: u64,
    },
    /// The runner encountered an internal integration failure.
    #[error("oracle candidate execution failed: {0}")]
    Internal(String),
}

/// Host-provided executor for tactic candidates returned by a [`ProofOracle`].
pub trait OracleCandidateRunner: Send + Sync {
    /// Try to turn one candidate script into a kernel-verifiable proof.
    ///
    /// Returns `Ok(Some(_))` only for candidates that fully close the goal and
    /// produce a proof term that the caller can re-check through the kernel.
    /// Normal candidate failure should return `Ok(None)` so the engine can try
    /// the next suggestion; `Err(_)` is reserved for runner-level failures such
    /// as timeouts or context setup bugs.
    fn try_candidate(
        &self,
        env: &Environment,
        local_ctx: Option<&LocalContext>,
        goal: &Expr,
        candidate: &OracleCandidate,
        timeout: Duration,
    ) -> Result<Option<ProofResult>, OracleRunError>;
}

// ============================================================================
// Builder API for OracleRequest
// ============================================================================

impl OracleRequest {
    /// Create a new oracle request for the given goal.
    pub fn new(goal: impl Into<String>) -> Self {
        Self {
            goal: goal.into(),
            hypotheses: Vec::new(),
            relevant_lemmas: Vec::new(),
            num_candidates: 8,
            temperature: 0.6,
            max_tokens: None,
        }
    }

    /// Add a hypothesis to the request.
    pub fn with_hypothesis(mut self, name: impl Into<String>, ty: impl Into<String>) -> Self {
        self.hypotheses.push((name.into(), ty.into()));
        self
    }

    /// Add a relevant lemma to the request.
    pub fn with_lemma(mut self, name: impl Into<String>, ty: impl Into<String>) -> Self {
        self.relevant_lemmas.push((name.into(), ty.into()));
        self
    }

    /// Set the number of candidates to request.
    pub fn with_candidates(mut self, n: usize) -> Self {
        self.num_candidates = n;
        self
    }

    /// Set the sampling temperature.
    pub fn with_temperature(mut self, t: f64) -> Self {
        self.temperature = t;
        self
    }

    /// Set the maximum token count for generation.
    pub fn with_max_tokens(mut self, n: usize) -> Self {
        self.max_tokens = Some(n);
        self
    }

    /// Build a request directly from a kernel goal and optional local context.
    pub fn from_goal_and_context(goal: &Expr, local_ctx: Option<&LocalContext>) -> Self {
        let mut request = Self::new(format!("{goal}"));

        if let Some(local_ctx) = local_ctx {
            for decl in local_ctx.iter() {
                request = request.with_hypothesis(decl.name.to_string(), format!("{}", decl.type_));
            }
        }

        request
    }

    /// Format the request as a prompt string for the model.
    ///
    /// Uses the standard format expected by Lean 4 proof generation models
    /// (Goedel-Prover-V2, DeepSeek-Prover-V2, etc.):
    ///
    /// ```text
    /// /-- <goal description> -/
    /// theorem goal_name (hyp1 : Type1) (hyp2 : Type2) : GoalType := by
    /// ```
    pub fn format_prompt(&self) -> String {
        let mut prompt = String::with_capacity(512);

        // Format hypotheses as theorem parameters
        if !self.hypotheses.is_empty() {
            prompt.push_str("theorem goal");
            for (name, ty) in &self.hypotheses {
                prompt.push_str(&format!(" ({name} : {ty})"));
            }
            prompt.push_str(&format!(" : {} := by\n", self.goal));
        } else {
            prompt.push_str(&format!("theorem goal : {} := by\n", self.goal));
        }

        // Append relevant lemmas as comments for context
        if !self.relevant_lemmas.is_empty() {
            prompt.push_str("  -- Relevant lemmas:\n");
            for (name, ty) in &self.relevant_lemmas {
                prompt.push_str(&format!("  -- {name} : {ty}\n"));
            }
        }

        prompt
    }
}

/// Sort oracle candidates by descending confidence, preserving existing order
/// for NaN/indeterminate comparisons.
pub fn sort_oracle_candidates(candidates: &mut [OracleCandidate]) {
    candidates.sort_by(|a, b| {
        b.confidence
            .partial_cmp(&a.confidence)
            .unwrap_or(std::cmp::Ordering::Equal)
    });
}

impl Default for OracleRequest {
    fn default() -> Self {
        Self::new("")
    }
}

// ============================================================================
// OracleCandidate ordering
// ============================================================================

impl OracleCandidate {
    /// Create a new candidate with the given tactic text and confidence.
    pub fn new(tactic_text: impl Into<String>, confidence: f64) -> Self {
        Self {
            tactic_text: tactic_text.into(),
            confidence,
            reasoning: None,
            token_count: None,
        }
    }

    /// Add chain-of-thought reasoning.
    pub fn with_reasoning(mut self, reasoning: impl Into<String>) -> Self {
        self.reasoning = Some(reasoning.into());
        self
    }
}

impl fmt::Display for OracleCandidate {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[{:.1}%] {}", self.confidence * 100.0, self.tactic_text)
    }
}

// ============================================================================
// ProofTermCandidate constructors
// ============================================================================

impl ProofTermCandidate {
    /// Create a new proof-term candidate.
    pub fn new(proof_term: Expr, confidence: f64) -> Self {
        Self {
            proof_term,
            confidence,
            description: None,
        }
    }

    /// Attach a human-readable description.
    pub fn with_description(mut self, description: impl Into<String>) -> Self {
        self.description = Some(description.into());
        self
    }
}

/// Sort proof-term candidates by descending confidence, preserving existing
/// order for NaN/indeterminate comparisons.
pub fn sort_proof_term_candidates(candidates: &mut [ProofTermCandidate]) {
    candidates.sort_by(|a, b| {
        b.confidence
            .partial_cmp(&a.confidence)
            .unwrap_or(std::cmp::Ordering::Equal)
    });
}

#[cfg(feature = "oracle-http")]
mod http;
#[cfg(feature = "oracle-http")]
pub use http::HttpOracle;

#[cfg(feature = "oracle-http")]
mod claude;
#[cfg(feature = "oracle-http")]
pub use claude::ClaudeOracle;

#[cfg(feature = "oracle-http")]
mod gemini;
#[cfg(feature = "oracle-http")]
pub use gemini::GeminiOracle;

#[cfg(feature = "oracle-http")]
mod openai;
#[cfg(feature = "oracle-http")]
pub use openai::OpenAiOracle;

#[cfg(all(test, feature = "oracle-http"))]
mod tests_http;

#[cfg(all(test, feature = "oracle-http"))]
mod tests_commercial;

#[cfg(test)]
mod tests;
