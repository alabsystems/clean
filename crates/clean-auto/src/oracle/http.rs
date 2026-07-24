// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! HTTP-based neural proof oracle that speaks the AI Provider chat-completions wire
//! protocol.
//!
//! Connects to any AI Provider-compatible endpoint (vLLM, llama.cpp, MLX, hosted
//! APIs) and returns [`OracleCandidate`] values from the model's chat responses.
//!
//! # Feature gate
//!
//! This module is only available when the `oracle-http` feature is enabled:
//!
//! ```toml
//! clean-auto = { workspace = true, features = ["oracle-http"] }
//! ```

use super::{
    OracleCandidate, OracleConfig, OracleError, OracleMetrics, OracleRequest, ProofOracle,
};
use serde::{Deserialize, Serialize};
use std::sync::Mutex;
use std::time::Instant;

/// A hosted proof oracle that calls an AI Provider-compatible `/v1/chat/completions`
/// endpoint and parses assistant responses into [`OracleCandidate`] values.
pub struct HttpOracle {
    config: OracleConfig,
    agent: ureq::Agent,
    last_metrics: Mutex<Option<OracleMetrics>>,
}

/// AI Provider chat-completions request body.
#[derive(Serialize)]
struct ChatRequest {
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

/// AI Provider chat-completions response body.
#[derive(Deserialize)]
struct ChatResponse {
    choices: Vec<ChatChoice>,
    #[serde(default)]
    usage: Option<ChatUsage>,
}

#[derive(Deserialize)]
struct ChatChoice {
    message: ChatChoiceMessage,
    #[serde(default)]
    index: usize,
}

#[derive(Deserialize)]
struct ChatChoiceMessage {
    content: Option<String>,
    #[serde(default)]
    reasoning_content: Option<String>,
}

#[derive(Deserialize)]
struct ChatUsage {
    #[serde(default)]
    completion_tokens: u32,
}

impl HttpOracle {
    /// Create a new HTTP oracle from the given configuration.
    ///
    /// Returns [`OracleError::NotConfigured`] if `config.endpoint_url` is `None`.
    pub fn new(config: OracleConfig) -> Result<Self, OracleError> {
        if config.endpoint_url.is_none() {
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

    /// The configured endpoint URL.
    pub fn endpoint_url(&self) -> &str {
        self.config
            .endpoint_url
            .as_deref()
            .unwrap_or("<not configured>")
    }

    /// Build the chat completions URL from the configured endpoint.
    fn completions_url(&self) -> String {
        let base = self.endpoint_url().trim_end_matches('/');
        format!("{base}/chat/completions")
    }

    /// Build the list of chat messages from an oracle request.
    fn build_chat_messages(request: &OracleRequest) -> Vec<ChatMessage> {
        let system_prompt = "You are a Lean 4 theorem prover. Given a proof goal, \
            respond with ONLY the tactic sequence that closes the goal. \
            Do not include any explanation or markdown formatting.";

        vec![
            ChatMessage {
                role: "system".to_string(),
                content: system_prompt.to_string(),
            },
            ChatMessage {
                role: "user".to_string(),
                content: request.format_prompt(),
            },
        ]
    }

    /// Parse a single choice's content into an [`OracleCandidate`].
    ///
    /// Strips surrounding whitespace and one outer Markdown code fence if present.
    fn parse_candidate(
        content: &str,
        reasoning: Option<&str>,
        index: usize,
        total: usize,
    ) -> OracleCandidate {
        let trimmed = content.trim();
        let tactic_text = strip_code_fence(trimmed);
        // Assign linearly decreasing confidence based on position.
        let confidence = if total <= 1 {
            0.5
        } else {
            1.0 - (index as f64 / total as f64)
        };
        let mut candidate = OracleCandidate::new(tactic_text, confidence);
        if let Some(r) = reasoning {
            if !r.is_empty() {
                candidate = candidate.with_reasoning(r);
            }
        }
        candidate
    }
}

/// Strip one outer Markdown code fence (` ```lean ... ``` ` or ` ``` ... ``` `).
pub(super) fn strip_code_fence(s: &str) -> String {
    let lines: Vec<&str> = s.lines().collect();
    if lines.len() >= 2 {
        let first = lines[0].trim();
        let last = lines[lines.len() - 1].trim();
        if first.starts_with("```") && last == "```" {
            return lines[1..lines.len() - 1].join("\n");
        }
    }
    s.to_string()
}

/// Send a POST request and map transport errors to [`OracleError`].
fn send_chat_request(
    agent: &ureq::Agent,
    url: &str,
    body_json: &[u8],
    timeout: std::time::Duration,
) -> Result<String, OracleError> {
    let mut response = match agent
        .post(url)
        .header("Content-Type", "application/json")
        .send(body_json)
    {
        Ok(resp) => resp,
        Err(ureq::Error::Timeout(_)) => {
            return Err(OracleError::Timeout {
                timeout_ms: timeout.as_millis() as u64,
            });
        }
        Err(ureq::Error::StatusCode(429)) => {
            return Err(OracleError::RateLimited {
                retry_after_ms: 1000,
            });
        }
        Err(ureq::Error::StatusCode(code)) => {
            return Err(OracleError::ModelError(format!(
                "endpoint returned HTTP {code}"
            )));
        }
        Err(ureq::Error::Io(io_err)) => {
            return Err(OracleError::ConnectionFailed(io_err.to_string()));
        }
        Err(other) => {
            return Err(OracleError::ConnectionFailed(other.to_string()));
        }
    };
    response
        .body_mut()
        .read_to_string()
        .map_err(|e| OracleError::InvalidResponse(format!("failed to read response body: {e}")))
}

/// Parse a chat-completions JSON response into [`OracleCandidate`] values.
fn parse_chat_response(body: &str) -> Result<(Vec<OracleCandidate>, u32), OracleError> {
    let chat: ChatResponse = serde_json::from_str(body)
        .map_err(|e| OracleError::InvalidResponse(format!("invalid JSON: {e}")))?;

    if chat.choices.is_empty() {
        return Err(OracleError::InvalidResponse(
            "endpoint returned empty choices array".to_string(),
        ));
    }

    let total = chat.choices.len();
    let mut candidates = Vec::with_capacity(total);
    for choice in &chat.choices {
        let content = choice.message.content.as_deref().unwrap_or("");
        if content.is_empty() {
            continue;
        }
        candidates.push(HttpOracle::parse_candidate(
            content,
            choice.message.reasoning_content.as_deref(),
            choice.index,
            total,
        ));
    }

    if candidates.is_empty() {
        return Err(OracleError::InvalidResponse(
            "all choices had empty content".to_string(),
        ));
    }

    let tokens = chat
        .usage
        .as_ref()
        .map(|u| u.completion_tokens)
        .unwrap_or(0);
    Ok((candidates, tokens))
}

impl ProofOracle for HttpOracle {
    fn suggest_proof(&self, request: &OracleRequest) -> Result<Vec<OracleCandidate>, OracleError> {
        let url = self.completions_url();
        let body = ChatRequest {
            model: self.config.model_id.clone(),
            messages: Self::build_chat_messages(request),
            temperature: Some(request.temperature),
            n: Some(request.num_candidates),
            max_tokens: Some(request.max_tokens.unwrap_or(self.config.max_tokens)),
        };
        let body_json = serde_json::to_string(&body)
            .map_err(|e| OracleError::Other(format!("failed to serialize request: {e}")))?;

        let start = Instant::now();
        let resp_body =
            send_chat_request(&self.agent, &url, body_json.as_bytes(), self.config.timeout)?;
        let (candidates, total_tokens) = parse_chat_response(&resp_body)?;
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
        let url = self.completions_url();
        // Fast check: POST with an empty body and short timeout. We only care
        // whether the endpoint is reachable, not whether the response is valid.
        let check_agent = ureq::Agent::new_with_config(
            ureq::config::Config::builder()
                .timeout_global(Some(std::time::Duration::from_secs(2)))
                .build(),
        );
        let result = check_agent
            .post(&url)
            .header("Content-Type", "application/json")
            .send(b"{}".as_slice());
        // Any HTTP response (even 4xx) means the endpoint is reachable.
        match result {
            Ok(_) => true,
            Err(ureq::Error::StatusCode(_)) => true,
            Err(_) => false,
        }
    }

    fn last_metrics(&self) -> Option<OracleMetrics> {
        self.last_metrics.lock().ok().and_then(|m| m.clone())
    }
}
