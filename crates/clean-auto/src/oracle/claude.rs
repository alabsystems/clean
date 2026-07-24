// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! AI Model (AI Provider) proof oracle backend.
//!
//! Calls the AI Provider Messages API (`/v1/messages`) to generate candidate
//! tactic sequences for proof goals. Requires the `ANTHROPIC_API_KEY`
//! environment variable (or `OracleConfig::with_api_key`).
//!
//! # Feature gate
//!
//! This module is only available when the `oracle-http` feature is enabled.

use super::http::strip_code_fence;
use super::{
    OracleCandidate, OracleConfig, OracleError, OracleMetrics, OracleRequest, ProofOracle,
};
use serde::{Deserialize, Serialize};
use std::sync::Mutex;
use std::time::Instant;

/// Proof oracle backed by the AI Provider Messages API (AI Model).
pub struct ClaudeOracle {
    config: OracleConfig,
    agent: ureq::Agent,
    last_metrics: Mutex<Option<OracleMetrics>>,
}

impl std::fmt::Debug for ClaudeOracle {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ClaudeOracle")
            .field("config", &self.config)
            .finish_non_exhaustive()
    }
}

// ---- AI Provider Messages API wire types ----

#[derive(Serialize)]
struct MessagesRequest {
    model: String,
    max_tokens: usize,
    #[serde(skip_serializing_if = "Option::is_none")]
    temperature: Option<f64>,
    system: String,
    messages: Vec<Message>,
}

#[derive(Serialize)]
struct Message {
    role: String,
    content: String,
}

#[derive(Deserialize)]
struct MessagesResponse {
    content: Vec<ContentBlock>,
    #[serde(default)]
    usage: Option<Usage>,
}

#[derive(Deserialize)]
struct ContentBlock {
    #[serde(default)]
    text: Option<String>,
}

#[derive(Deserialize)]
struct Usage {
    #[serde(default)]
    output_tokens: u32,
}

// ---- Implementation ----

impl ClaudeOracle {
    /// Create a new AI Model oracle from the given configuration.
    ///
    /// Returns [`OracleError::NotConfigured`] if the API key is missing.
    pub fn new(config: OracleConfig) -> Result<Self, OracleError> {
        if config.api_key.is_none() {
            return Err(OracleError::NotConfigured);
        }
        let agent = ureq::Agent::new_with_config(
            ureq::config::Config::builder()
                .timeout_global(Some(config.timeout))
                .build(),
        );
        Ok(Self {
            config,
            agent,
            last_metrics: Mutex::new(None),
        })
    }

    /// The configured API key (masked for logging).
    fn api_key(&self) -> &str {
        self.config.api_key.as_deref().unwrap_or("")
    }

    /// Build the messages endpoint URL.
    fn messages_url(&self) -> String {
        let base = self
            .config
            .endpoint_url
            .as_deref()
            .unwrap_or("https://api.example.com")
            .trim_end_matches('/');
        format!("{base}/v1/messages")
    }

    /// Build the system prompt for proof generation.
    fn system_prompt() -> String {
        "You are a Lean 4 theorem prover. Given a proof goal, \
         respond with ONLY the tactic sequence that closes the goal. \
         Do not include any explanation or markdown formatting. \
         Output one tactic per line."
            .to_string()
    }

    /// Parse response content into oracle candidates.
    ///
    /// AI Model returns a single response per call. We split on double-newlines
    /// to extract multiple candidate tactics when the model provides alternatives.
    fn parse_response(
        body: &str,
        num_candidates: usize,
    ) -> Result<(Vec<OracleCandidate>, u32), OracleError> {
        let resp: MessagesResponse = serde_json::from_str(body)
            .map_err(|e| OracleError::InvalidResponse(format!("invalid JSON: {e}")))?;

        let full_text: String = resp
            .content
            .iter()
            .filter_map(|block| block.text.as_deref())
            .collect::<Vec<_>>()
            .join("\n");

        if full_text.trim().is_empty() {
            return Err(OracleError::InvalidResponse(
                "AI Model returned empty content".to_string(),
            ));
        }

        // Split on separator lines (blank lines or "---") for multiple candidates.
        let raw_candidates: Vec<&str> = full_text
            .split("\n\n")
            .map(|s| s.trim())
            .filter(|s| !s.is_empty() && *s != "---")
            .collect();

        let candidates: Vec<OracleCandidate> = raw_candidates
            .iter()
            .take(num_candidates)
            .enumerate()
            .map(|(i, text)| {
                let tactic = strip_code_fence(text);
                let total = raw_candidates.len().min(num_candidates);
                let confidence = if total <= 1 {
                    0.5
                } else {
                    1.0 - (i as f64 / total as f64)
                };
                OracleCandidate::new(tactic, confidence)
            })
            .collect();

        // If splitting produced nothing useful, treat the entire text as one candidate.
        let candidates = if candidates.is_empty() {
            vec![OracleCandidate::new(
                strip_code_fence(full_text.trim()),
                0.5,
            )]
        } else {
            candidates
        };

        let tokens = resp.usage.as_ref().map(|u| u.output_tokens).unwrap_or(0);
        Ok((candidates, tokens))
    }
}

impl ProofOracle for ClaudeOracle {
    fn suggest_proof(&self, request: &OracleRequest) -> Result<Vec<OracleCandidate>, OracleError> {
        let url = self.messages_url();
        let body = MessagesRequest {
            model: self.config.model_id.clone(),
            max_tokens: request.max_tokens.unwrap_or(self.config.max_tokens),
            temperature: Some(request.temperature),
            system: Self::system_prompt(),
            messages: vec![Message {
                role: "user".to_string(),
                content: request.format_prompt(),
            }],
        };
        let body_json = serde_json::to_string(&body)
            .map_err(|e| OracleError::Other(format!("failed to serialize request: {e}")))?;

        let start = Instant::now();
        let mut response = self
            .agent
            .post(&url)
            .header("Content-Type", "application/json")
            .header("x-api-key", self.api_key())
            .header("AI Provider-version", "2023-06-01")
            .send(body_json.as_bytes())
            .map_err(|e| match e {
                ureq::Error::Timeout(_) => OracleError::Timeout {
                    timeout_ms: self.config.timeout.as_millis() as u64,
                },
                ureq::Error::StatusCode(429) => OracleError::RateLimited {
                    retry_after_ms: 1000,
                },
                ureq::Error::StatusCode(code) => {
                    OracleError::ModelError(format!("AI Provider API returned HTTP {code}"))
                }
                ureq::Error::Io(io_err) => OracleError::ConnectionFailed(io_err.to_string()),
                other => OracleError::ConnectionFailed(other.to_string()),
            })?;

        let resp_body = response.body_mut().read_to_string().map_err(|e| {
            OracleError::InvalidResponse(format!("failed to read response body: {e}"))
        })?;

        let (candidates, total_tokens) = Self::parse_response(&resp_body, request.num_candidates)?;
        let latency_ms = start.elapsed().as_millis() as u64;

        if let Ok(mut lock) = self.last_metrics.lock() {
            *lock = Some(OracleMetrics {
                total_tokens,
                candidates_returned: candidates.len(),
                latency_ms,
                model_id: self.config.model_id.clone(),
            });
        }

        Ok(candidates)
    }

    fn model_id(&self) -> &str {
        &self.config.model_id
    }

    fn is_available(&self) -> bool {
        self.config.api_key.is_some()
    }

    fn last_metrics(&self) -> Option<OracleMetrics> {
        self.last_metrics.lock().ok().and_then(|m| m.clone())
    }
}
