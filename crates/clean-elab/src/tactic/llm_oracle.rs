// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Lightweight LLM proof-oracle types and response parsing helpers.

use super::parse_tactic_script;
use serde::{Deserialize, Serialize};
use std::iter::Peekable;
use std::str::Lines;
use thiserror::Error;

/// A named hypothesis included in an LLM proof request.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct LlmHypothesis {
    pub name: String,
    pub ty: String,
}

impl LlmHypothesis {
    pub fn new(name: impl Into<String>, ty: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            ty: ty.into(),
        }
    }
}

/// Request payload for LLM-based proof generation.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct LlmProofRequest {
    pub goal: String,
    #[serde(default)]
    pub hypotheses: Vec<LlmHypothesis>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub context: Option<String>,
}

impl LlmProofRequest {
    pub fn new(goal: impl Into<String>) -> Self {
        Self {
            goal: goal.into(),
            hypotheses: Vec::new(),
            context: None,
        }
    }

    pub fn with_hypothesis(mut self, name: impl Into<String>, ty: impl Into<String>) -> Self {
        self.hypotheses.push(LlmHypothesis::new(name, ty));
        self
    }

    pub fn with_context(mut self, context: impl Into<String>) -> Self {
        self.context = Some(context.into());
        self
    }
}

/// Normalized response returned by an LLM proof backend.
#[derive(Debug, Clone, Default, PartialEq, Serialize, Deserialize)]
pub struct LlmProofResponse {
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub tactic_script: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub proof_term: Option<String>,
    #[serde(default)]
    pub confidence: f64,
}

impl LlmProofResponse {
    pub fn from_raw(raw: &str) -> Result<Self, LlmOracleError> {
        let trimmed = raw.trim();
        if trimmed.is_empty() {
            return Err(LlmOracleError::InvalidResponse(
                "empty LLM response".to_string(),
            ));
        }

        if let Ok(response) = serde_json::from_str::<Self>(trimmed) {
            if response.tactic_script.is_some() || response.proof_term.is_some() {
                return Ok(response);
            }
        }

        if let Some(response) = parse_labeled_response(trimmed) {
            return Ok(response);
        }

        let tactic_script = extract_fenced_block(trimmed).unwrap_or_else(|| trimmed.to_string());

        Ok(Self {
            tactic_script: Some(normalize_script_body(&tactic_script)),
            proof_term: None,
            confidence: 0.0,
        })
    }

    pub fn tactic_steps(&self) -> Result<Vec<String>, LlmOracleError> {
        let source = self
            .tactic_script
            .as_deref()
            .filter(|s| !s.trim().is_empty())
            .map(normalize_script_body)
            .or_else(|| {
                self.proof_term
                    .as_deref()
                    .filter(|s| !s.trim().is_empty())
                    .map(|proof_term| format!("exact {}", proof_term.trim()))
            })
            .ok_or_else(|| {
                LlmOracleError::InvalidResponse(
                    "response missing both tactic_script and proof_term".to_string(),
                )
            })?;

        let tactics = parse_tactic_script(&source);
        if tactics.is_empty() {
            return Err(LlmOracleError::InvalidResponse(
                "response did not contain any executable tactic steps".to_string(),
            ));
        }

        Ok(tactics)
    }
}

/// Errors raised by LLM proof backends or response parsing.
#[derive(Debug, Clone, PartialEq, Eq, Error)]
pub enum LlmOracleError {
    #[error("llm backend is unavailable")]
    Unavailable,
    #[error("invalid llm response: {0}")]
    InvalidResponse(String),
    #[error("llm backend failed: {0}")]
    Backend(String),
}

/// Parse raw LLM output into executable tactic steps.
pub fn extract_proof_from_response(raw: &str) -> Result<Vec<String>, LlmOracleError> {
    LlmProofResponse::from_raw(raw)?.tactic_steps()
}

/// Trait for pluggable LLM proof backends.
pub trait LlmOracle: Send + Sync {
    fn request_proof(&self, request: &LlmProofRequest) -> Result<LlmProofResponse, LlmOracleError>;

    fn backend_name(&self) -> &str;

    fn is_available(&self) -> bool {
        true
    }

    fn request_tactic_steps(
        &self,
        request: &LlmProofRequest,
    ) -> Result<Vec<String>, LlmOracleError> {
        self.request_proof(request)?.tactic_steps()
    }
}

/// Deterministic in-memory backend for unit tests.
#[derive(Debug, Clone)]
pub struct MockLlmOracle {
    response: Result<LlmProofResponse, LlmOracleError>,
    backend_name: String,
    available: bool,
}

impl MockLlmOracle {
    pub fn new(response: LlmProofResponse) -> Self {
        Self {
            response: Ok(response),
            backend_name: "mock-llm-oracle".to_string(),
            available: true,
        }
    }

    pub fn from_tactic_script(script: impl Into<String>) -> Self {
        Self::new(LlmProofResponse {
            tactic_script: Some(script.into()),
            proof_term: None,
            confidence: 1.0,
        })
    }

    pub fn with_error(error: LlmOracleError) -> Self {
        Self {
            response: Err(error),
            backend_name: "mock-llm-oracle".to_string(),
            available: true,
        }
    }

    pub fn unavailable() -> Self {
        Self {
            response: Err(LlmOracleError::Unavailable),
            backend_name: "mock-llm-oracle".to_string(),
            available: false,
        }
    }
}

impl LlmOracle for MockLlmOracle {
    fn request_proof(
        &self,
        _request: &LlmProofRequest,
    ) -> Result<LlmProofResponse, LlmOracleError> {
        if !self.available {
            return Err(LlmOracleError::Unavailable);
        }
        self.response.clone()
    }

    fn backend_name(&self) -> &str {
        &self.backend_name
    }

    fn is_available(&self) -> bool {
        self.available
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum ResponseField {
    TacticScript,
    ProofTerm,
    Confidence,
}

fn parse_labeled_response(raw: &str) -> Option<LlmProofResponse> {
    let mut lines = raw.lines().peekable();
    let mut tactic_script = None;
    let mut proof_term = None;
    let mut confidence = 0.0;
    let mut saw_field = false;

    while let Some(line) = lines.next() {
        let trimmed = line.trim();
        let Some((field, rest)) = parse_label_line(trimmed) else {
            continue;
        };

        saw_field = true;
        match field {
            ResponseField::TacticScript => {
                let value = collect_labeled_value(rest, &mut lines);
                if !value.is_empty() {
                    tactic_script = Some(normalize_script_body(&value));
                }
            }
            ResponseField::ProofTerm => {
                let value = collect_labeled_value(rest, &mut lines);
                if !value.is_empty() {
                    proof_term = Some(trim_matching_quotes(value.trim()).to_string());
                }
            }
            ResponseField::Confidence => {
                if let Ok(value) = rest.trim().trim_end_matches(',').parse::<f64>() {
                    confidence = value;
                }
            }
        }
    }

    saw_field.then_some(LlmProofResponse {
        tactic_script,
        proof_term,
        confidence,
    })
}

fn parse_label_line(line: &str) -> Option<(ResponseField, &str)> {
    let (label, rest) = line.split_once(':')?;
    let normalized = label.trim().to_ascii_lowercase();
    let field = match normalized.as_str() {
        "tactic_script" | "tactic script" | "script" => ResponseField::TacticScript,
        "proof_term" | "proof term" | "term" => ResponseField::ProofTerm,
        "confidence" => ResponseField::Confidence,
        _ => return None,
    };
    Some((field, rest))
}

fn collect_labeled_value(rest: &str, lines: &mut Peekable<Lines<'_>>) -> String {
    let inline = trim_matching_quotes(rest.trim());
    if !inline.is_empty() && !matches!(inline, "|" | "|-" | ">" | ">-") {
        return inline.to_string();
    }

    let mut collected = String::new();
    while let Some(next) = lines.peek().copied() {
        if parse_label_line(next.trim()).is_some() {
            break;
        }
        let line = lines.next().unwrap_or_default();
        if !collected.is_empty() {
            collected.push('\n');
        }
        collected.push_str(line);
    }

    extract_fenced_block(&collected).unwrap_or_else(|| collected.trim().to_string())
}

fn extract_fenced_block(raw: &str) -> Option<String> {
    let mut rest = raw;
    let mut preferred = None;
    let mut fallback = None;

    while let Some(start) = rest.find("```") {
        let after_tick = &rest[start + 3..];
        let Some(lang_end) = after_tick.find('\n') else {
            break;
        };
        let lang = after_tick[..lang_end].trim().to_ascii_lowercase();
        let after_header = &after_tick[lang_end + 1..];
        let Some(end) = after_header.find("```") else {
            break;
        };
        let body = after_header[..end].trim();
        if !body.is_empty() {
            if fallback.is_none() {
                fallback = Some(body.to_string());
            }
            if preferred.is_none() && matches!(lang.as_str(), "lean" | "lean4" | "tactic") {
                preferred = Some(body.to_string());
            }
        }
        rest = &after_header[end + 3..];
    }

    preferred.or(fallback)
}

fn normalize_script_body(raw: &str) -> String {
    let mut text = trim_matching_quotes(raw.trim()).to_string();

    if let Some(body) = text.split_once(":= by").map(|(_, rhs)| rhs) {
        text = body.trim().to_string();
    } else if let Some(stripped) = strip_leading_by(&text) {
        text = stripped.to_string();
    }

    text.lines()
        .map(|line| {
            let trimmed = line.trim();
            let trimmed = trimmed.trim_start_matches('·').trim_start();
            let trimmed = trimmed.trim_start_matches('|').trim_start();
            trimmed
        })
        .collect::<Vec<_>>()
        .join("\n")
        .trim()
        .to_string()
}

fn strip_leading_by(text: &str) -> Option<&str> {
    let stripped = text.strip_prefix("by")?;
    match stripped.chars().next() {
        None => Some(""),
        Some(c) if c.is_whitespace() => Some(stripped.trim_start()),
        Some(_) => None,
    }
}

fn trim_matching_quotes(text: &str) -> &str {
    text.strip_prefix('"')
        .and_then(|s| s.strip_suffix('"'))
        .or_else(|| text.strip_prefix('\'').and_then(|s| s.strip_suffix('\'')))
        .unwrap_or(text)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_extract_proof_from_plain_script() {
        let steps = extract_proof_from_response("intro h; exact h").expect("should parse");
        assert_eq!(steps, vec!["intro h", "exact h"]);
    }

    #[test]
    fn test_extract_proof_from_fenced_block_strips_by() {
        let raw = r#"
Here is a proof:
```lean
by
  intro h
  exact h
```
"#;
        let steps = extract_proof_from_response(raw).expect("should parse");
        assert_eq!(steps, vec!["intro h", "exact h"]);
    }

    #[test]
    fn test_extract_proof_from_json_response() {
        let raw = r#"{
  "tactic_script": "intro h\nexact h",
  "confidence": 0.82
}"#;
        let response = LlmProofResponse::from_raw(raw).expect("json should parse");
        assert!((response.confidence - 0.82).abs() < f64::EPSILON);
        assert_eq!(
            response.tactic_steps().expect("should extract"),
            vec!["intro h", "exact h"]
        );
    }

    #[test]
    fn test_extract_proof_from_labeled_proof_term() {
        let steps = extract_proof_from_response("proof_term: h")
            .expect("proof_term should fall back to exact");
        assert_eq!(steps, vec!["exact h"]);
    }

    #[test]
    fn test_extract_proof_from_theorem_wrapper() {
        let steps = extract_proof_from_response("theorem goal : P := by\n  intro h\n  exact h")
            .expect("wrapped theorem should parse");
        assert_eq!(steps, vec!["intro h", "exact h"]);
    }

    #[test]
    fn test_mock_llm_oracle_returns_tactic_steps() {
        let oracle = MockLlmOracle::from_tactic_script("intro h\nexact h");
        let request = LlmProofRequest::new("P -> P").with_hypothesis("h", "P");
        let steps = oracle
            .request_tactic_steps(&request)
            .expect("mock oracle should succeed");
        assert_eq!(steps, vec!["intro h", "exact h"]);
        assert!(oracle.is_available());
        assert_eq!(oracle.backend_name(), "mock-llm-oracle");
    }

    #[test]
    fn test_mock_llm_oracle_unavailable() {
        let oracle = MockLlmOracle::unavailable();
        let request = LlmProofRequest::new("True");
        let result = oracle.request_proof(&request);
        assert_eq!(result, Err(LlmOracleError::Unavailable));
    }
}
