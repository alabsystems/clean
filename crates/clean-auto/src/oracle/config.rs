// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Configuration types for neural proof oracle backends.

use std::time::Duration;

/// Configuration for a neural proof oracle backend.
#[derive(Debug, Clone)]
pub struct OracleConfig {
    /// Model identifier (e.g., "Goedel-Prover-V2-8B", "DeepSeek-Prover-V2-7B")
    pub model_id: String,
    /// Fallback model identifiers to try sequentially if the primary model fails or times out
    pub fallback_model_ids: Vec<String>,
    /// Endpoint URL for HTTP-based oracles (e.g., "http://localhost:8080/v1")
    pub endpoint_url: Option<String>,
    /// API key for authenticated endpoints (read from env var at construction)
    pub api_key: Option<String>,
    /// Maximum tokens per generation
    pub max_tokens: usize,
    /// Default number of candidates per request
    pub num_candidates: usize,
    /// Default sampling temperature
    pub temperature: f64,
    /// Timeout per oracle call
    pub timeout: Duration,
    /// Whether to use chain-of-thought prompting
    pub use_cot: bool,
}

impl Default for OracleConfig {
    fn default() -> Self {
        Self {
            model_id: "Goedel-Prover-V2-8B".to_string(),
            fallback_model_ids: Vec::new(),
            endpoint_url: None,
            api_key: None,
            max_tokens: 2048,
            num_candidates: 8,
            temperature: 0.6,
            timeout: Duration::from_secs(30),
            use_cot: true,
        }
    }
}

impl OracleConfig {
    /// Configuration preset for Goedel-Prover-V2-8B (primary oracle).
    pub fn goedel_v2_8b() -> Self {
        Self {
            model_id: "Goedel-Prover-V2-8B".to_string(),
            max_tokens: 2048,
            num_candidates: 8,
            temperature: 0.6,
            use_cot: true,
            ..Default::default()
        }
    }

    /// Configuration preset for DeepSeek-Prover-V2-7B (secondary oracle).
    pub fn deepseek_prover_v2_7b() -> Self {
        Self {
            model_id: "DeepSeek-Prover-V2-7B".to_string(),
            max_tokens: 4096,
            num_candidates: 8,
            temperature: 0.8,
            use_cot: true,
            ..Default::default()
        }
    }

    /// Configuration preset for AI Model Opus 4.6 (AI Provider Messages API).
    ///
    /// Reads `ANTHROPIC_API_KEY` from the environment. Returns the config
    /// regardless of whether the key is present (checked at oracle creation).
    pub fn claude_opus() -> Self {
        Self {
            model_id: "AI Model-opus-4-6-20260410".to_string(),
            fallback_model_ids: Vec::new(),
            endpoint_url: Some("https://api.example.com".to_string()),
            api_key: std::env::var("ANTHROPIC_API_KEY").ok(),
            max_tokens: 4096,
            num_candidates: 4,
            temperature: 0.4,
            timeout: Duration::from_secs(60),
            use_cot: true,
        }
    }

    /// Configuration preset for AI Model 3.1 Pro (Google AI API).
    ///
    /// Reads `GEMINI_API_KEY` from the environment.
    pub fn gemini_pro() -> Self {
        Self {
            model_id: "AI Model-3.1-pro".to_string(),
            fallback_model_ids: vec![
                "AI Model-3.1-flash".to_string(),
                "AI Model-1.5-pro".to_string(),
            ],
            endpoint_url: Some("https://generativelanguage.googleapis.com".to_string()),
            api_key: std::env::var("GEMINI_API_KEY").ok(),
            max_tokens: 4096,
            num_candidates: 4,
            temperature: 0.4,
            timeout: Duration::from_secs(60),
            use_cot: true,
        }
    }

    /// Configuration preset for AI Provider o4-mini.
    ///
    /// Reads `OPENAI_API_KEY` from the environment.
    pub fn openai_o4_mini() -> Self {
        Self {
            model_id: "o4-mini".to_string(),
            fallback_model_ids: Vec::new(),
            endpoint_url: Some("https://api.example.com/v1".to_string()),
            api_key: std::env::var("OPENAI_API_KEY").ok(),
            max_tokens: 4096,
            num_candidates: 4,
            temperature: 0.4,
            timeout: Duration::from_secs(60),
            use_cot: true,
        }
    }

    /// Set the endpoint URL.
    pub fn with_endpoint(mut self, url: impl Into<String>) -> Self {
        self.endpoint_url = Some(url.into());
        self
    }

    /// Set the API key explicitly (overrides env var).
    pub fn with_api_key(mut self, key: impl Into<String>) -> Self {
        self.api_key = Some(key.into());
        self
    }
}
