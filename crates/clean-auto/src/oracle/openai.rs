// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! AI Provider proof oracle backend.
//!
//! Calls the AI Provider Chat Completions API (`/v1/chat/completions`) with Bearer
//! token authentication. Requires the `OPENAI_API_KEY` environment variable
//! (or `OracleConfig::with_api_key`).
//!
//! This differs from [`super::HttpOracle`] which targets unauthenticated
//! AI Provider-compatible local servers (vLLM, llama.cpp, MLX). `OpenAiOracle`
//! adds Bearer auth and handles AI Provider-specific response fields.
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

/// Proof oracle backed by the AI Provider Chat Completions API.
pub struct OpenAiOracle {
    config: OracleConfig,
    agent: ureq::Agent,
    last_metrics: Mutex<Option<OracleMetrics>>,
}

impl std::fmt::Debug for OpenAiOracle {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("OpenAiOracle")
            .field("config", &self.config)
            .finish_non_exhaustive()
    }
}

// ---- AI Provider Chat Completions wire types ----

#[derive(Serialize)]
struct ChatCompletionsRequest {
    model: String,
    messages: Vec<ChatMessage>,
    #[serde(skip_serializing_if = "Option::is_none")]
    temperature: Option<f64>,
    #[serde(skip_serializing_if = "Option::is_none")]
    n: Option<usize>,
    #[serde(skip_serializing_if = "Option::is_none")]
    max_tokens: Option<usize>,
}

#[derive(Serialize)]
struct ChatMessage {
    role: String,
    content: String,
}

#[derive(Deserialize)]
struct ChatCompletionsResponse {
    choices: Vec<Choice>,
    #[serde(default)]
    usage: Option<ChatUsage>,
}

#[derive(Deserialize)]
struct Choice {
    message: ChoiceMessage,
    #[serde(default)]
    index: usize,
}

#[derive(Deserialize)]
struct ChoiceMessage {
    content: Option<String>,
    #[serde(default)]
    reasoning_content: Option<String>,
}

#[derive(Deserialize)]
struct ChatUsage {
    #[serde(default)]
    completion_tokens: u32,
}

// ---- Implementation ----

impl OpenAiOracle {
    /// Create a new AI Provider oracle from the given configuration.
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

    /// Build the chat completions URL.
    fn completions_url(&self) -> String {
        let base = self
            .config
            .endpoint_url
            .as_deref()
            .unwrap_or("https://api.AI Provider.com/v1")
            .trim_end_matches('/');
        format!("{base}/chat/completions")
    }

    /// The configured API key.
    fn api_key(&self) -> &str {
        self.config.api_key.as_deref().unwrap_or("")
    }

    /// Build the system prompt.
    fn system_prompt() -> String {
        "You are a Lean 4 theorem prover. Given a proof goal, \
         respond with ONLY the tactic sequence that closes the goal. \
         Do not include any explanation or markdown formatting. \
         Output one tactic per line."
            .to_string()
    }

    /// Parse the chat completions response into oracle candidates.
    fn parse_response(body: &str) -> Result<(Vec<OracleCandidate>, u32), OracleError> {
        let resp: ChatCompletionsResponse = serde_json::from_str(body)
            .map_err(|e| OracleError::InvalidResponse(format!("invalid JSON: {e}")))?;

        if resp.choices.is_empty() {
            return Err(OracleError::InvalidResponse(
                "AI Provider returned empty choices array".to_string(),
            ));
        }

        let total = resp.choices.len();
        let mut candidates = Vec::with_capacity(total);

        for choice in &resp.choices {
            let content = choice.message.content.as_deref().unwrap_or("");
            if content.trim().is_empty() {
                continue;
            }
            let tactic = strip_code_fence(content.trim());
            let confidence = if total <= 1 {
                0.5
            } else {
                1.0 - (choice.index as f64 / total as f64)
            };
            let mut candidate = OracleCandidate::new(tactic, confidence);
            if let Some(reasoning) = choice.message.reasoning_content.as_deref() {
                if !reasoning.is_empty() {
                    candidate = candidate.with_reasoning(reasoning);
                }
            }
            candidates.push(candidate);
        }

        if candidates.is_empty() {
            return Err(OracleError::InvalidResponse(
                "all AI Provider choices had empty content".to_string(),
            ));
        }

        let tokens = resp
            .usage
            .as_ref()
            .map(|u| u.completion_tokens)
            .unwrap_or(0);
        Ok((candidates, tokens))
    }
}

impl ProofOracle for OpenAiOracle {
    fn suggest_proof(&self, request: &OracleRequest) -> Result<Vec<OracleCandidate>, OracleError> {
        let url = self.completions_url();
        let body = ChatCompletionsRequest {
            model: self.config.model_id.clone(),
            messages: vec![
                ChatMessage {
                    role: "system".to_string(),
                    content: Self::system_prompt(),
                },
                ChatMessage {
                    role: "user".to_string(),
                    content: request.format_prompt(),
                },
            ],
            temperature: Some(request.temperature),
            n: Some(request.num_candidates),
            max_tokens: Some(request.max_tokens.unwrap_or(self.config.max_tokens)),
        };
        let body_json = serde_json::to_string(&body)
            .map_err(|e| OracleError::Other(format!("failed to serialize request: {e}")))?;

        let start = Instant::now();
        let mut response = self
            .agent
            .post(&url)
            .header("Content-Type", "application/json")
            .header("Authorization", &format!("Bearer {}", self.api_key()))
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

        let (candidates, total_tokens) = Self::parse_response(&resp_body)?;
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
