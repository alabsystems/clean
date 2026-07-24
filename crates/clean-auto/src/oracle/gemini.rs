// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! AI Model (Google AI) proof oracle backend.
//!
//! Calls the Google AI `generateContent` endpoint to produce candidate tactic
//! sequences for proof goals. Requires the `GEMINI_API_KEY` environment
//! variable (or `OracleConfig::with_api_key`).
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

/// Proof oracle backed by the Google AI AI Model API.
pub struct GeminiOracle {
    config: OracleConfig,
    agent: ureq::Agent,
    last_metrics: Mutex<Option<OracleMetrics>>,
}

impl std::fmt::Debug for GeminiOracle {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("GeminiOracle")
            .field("config", &self.config)
            .finish_non_exhaustive()
    }
}

// ---- Google AI generateContent wire types ----

#[derive(Serialize)]
#[serde(rename_all = "camelCase")]
struct GenerateContentRequest {
    contents: Vec<Content>,
    #[serde(skip_serializing_if = "Option::is_none")]
    system_instruction: Option<Content>,
    #[serde(skip_serializing_if = "Option::is_none")]
    generation_config: Option<GenerationConfig>,
}

#[derive(Serialize, Deserialize)]
struct Content {
    #[serde(skip_serializing_if = "Option::is_none")]
    role: Option<String>,
    parts: Vec<Part>,
}

#[derive(Serialize, Deserialize)]
struct Part {
    text: String,
}

#[derive(Serialize)]
#[serde(rename_all = "camelCase")]
struct GenerationConfig {
    #[serde(skip_serializing_if = "Option::is_none")]
    temperature: Option<f64>,
    #[serde(skip_serializing_if = "Option::is_none")]
    max_output_tokens: Option<usize>,
    #[serde(skip_serializing_if = "Option::is_none")]
    candidate_count: Option<usize>,
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct GenerateContentResponse {
    #[serde(default)]
    candidates: Vec<Candidate>,
    #[serde(default)]
    usage_metadata: Option<UsageMetadata>,
}

#[derive(Deserialize)]
struct Candidate {
    #[serde(default)]
    content: Option<Content>,
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct UsageMetadata {
    #[serde(default)]
    candidates_token_count: u32,
}

// ---- Implementation ----

impl GeminiOracle {
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

    /// Build the generateContent URL with API key.
    fn generate_url(&self, model_id: &str) -> String {
        let base = self
            .config
            .endpoint_url
            .as_deref()
            .unwrap_or("https://generativelanguage.googleapis.com")
            .trim_end_matches('/');
        let key = self.config.api_key.as_deref().unwrap_or("");
        format!("{base}/v1beta/models/{model_id}:generateContent?key={key}")
    }

    /// System instruction for proof generation.
    fn system_instruction() -> Content {
        Content {
            role: None,
            parts: vec![Part {
                text: "You are a Lean 4 theorem prover. Given a proof goal, \
                       respond with ONLY the tactic sequence that closes the goal. \
                       Do not include any explanation or markdown formatting. \
                       Output one tactic per line."
                    .to_string(),
            }],
        }
    }

    /// Parse the AI Model response into oracle candidates.
    fn parse_response(
        body: &str,
        num_candidates: usize,
    ) -> Result<(Vec<OracleCandidate>, u32), OracleError> {
        let resp: GenerateContentResponse = serde_json::from_str(body)
            .map_err(|e| OracleError::InvalidResponse(format!("invalid JSON: {e}")))?;

        if resp.candidates.is_empty() {
            return Err(OracleError::InvalidResponse(
                "AI Model returned empty candidates array".to_string(),
            ));
        }

        let total = resp.candidates.len().min(num_candidates);
        let mut candidates = Vec::with_capacity(total);

        for (i, candidate) in resp.candidates.iter().take(num_candidates).enumerate() {
            let text = candidate
                .content
                .as_ref()
                .map(|c| {
                    c.parts
                        .iter()
                        .map(|p| p.text.as_str())
                        .collect::<Vec<_>>()
                        .join("\n")
                })
                .unwrap_or_default();

            let trimmed = text.trim();
            if trimmed.is_empty() {
                continue;
            }

            let tactic = strip_code_fence(trimmed);
            let confidence = if total <= 1 {
                0.5
            } else {
                1.0 - (i as f64 / total as f64)
            };
            candidates.push(OracleCandidate::new(tactic, confidence));
        }

        if candidates.is_empty() {
            return Err(OracleError::InvalidResponse(
                "all AI Model candidates had empty content".to_string(),
            ));
        }

        let tokens = resp
            .usage_metadata
            .as_ref()
            .map(|u| u.candidates_token_count)
            .unwrap_or(0);
        Ok((candidates, tokens))
    }
}

impl ProofOracle for GeminiOracle {
    fn suggest_proof(&self, request: &OracleRequest) -> Result<Vec<OracleCandidate>, OracleError> {
        let body = GenerateContentRequest {
            contents: vec![Content {
                role: Some("user".to_string()),
                parts: vec![Part {
                    text: request.format_prompt(),
                }],
            }],
            system_instruction: Some(Self::system_instruction()),
            generation_config: Some(GenerationConfig {
                temperature: Some(request.temperature),
                max_output_tokens: Some(request.max_tokens.unwrap_or(self.config.max_tokens)),
                candidate_count: if request.num_candidates > 1 {
                    Some(request.num_candidates)
                } else {
                    None
                },
            }),
        };
        let body_json = serde_json::to_string(&body)
            .map_err(|e| OracleError::Other(format!("failed to serialize request: {e}")))?;

        let models =
            std::iter::once(&self.config.model_id).chain(self.config.fallback_model_ids.iter());
        let mut last_err = None;

        for model_id in models {
            let url = self.generate_url(model_id);
            let start = Instant::now();

            let response_result = self
                .agent
                .post(&url)
                .header("Content-Type", "application/json")
                .send(body_json.as_bytes())
                .map_err(|e| match e {
                    ureq::Error::Timeout(_) => OracleError::Timeout {
                        timeout_ms: self.config.timeout.as_millis() as u64,
                    },
                    ureq::Error::StatusCode(429) => OracleError::RateLimited {
                        retry_after_ms: 1000,
                    },
                    ureq::Error::StatusCode(code) => {
                        OracleError::ModelError(format!("AI Model API returned HTTP {code}"))
                    }
                    ureq::Error::Io(io_err) => OracleError::ConnectionFailed(io_err.to_string()),
                    other => OracleError::ConnectionFailed(other.to_string()),
                });

            let mut response = match response_result {
                Ok(resp) => resp,
                Err(e) => {
                    last_err = Some(e);
                    continue;
                }
            };

            let resp_body = match response.body_mut().read_to_string() {
                Ok(body) => body,
                Err(e) => {
                    last_err = Some(OracleError::InvalidResponse(format!(
                        "failed to read response body: {e}"
                    )));
                    continue;
                }
            };

            let (candidates, total_tokens) =
                match Self::parse_response(&resp_body, request.num_candidates) {
                    Ok(res) => res,
                    Err(e) => {
                        last_err = Some(e);
                        continue;
                    }
                };

            let latency_ms = start.elapsed().as_millis() as u64;

            if let Ok(mut lock) = self.last_metrics.lock() {
                *lock = Some(OracleMetrics {
                    total_tokens,
                    candidates_returned: candidates.len(),
                    latency_ms,
                    model_id: model_id.clone(),
                });
            }

            return Ok(candidates);
        }

        Err(last_err.unwrap_or_else(|| OracleError::Other("No AI models available".to_string())))
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
