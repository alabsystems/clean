// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Machine-readable diagnostics for automation agents.
//!
//! These records are intentionally independent of the human-facing
//! `Display` output for elaboration and tactic errors. Callers can keep
//! presenting the existing strings while exposing these stable codes and
//! fields over JSON/RPC or proof-state serialization.

use std::collections::BTreeMap;
use std::fmt;

use serde::{Deserialize, Serialize};

/// Source span in byte offsets plus 1-based line/column when available.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct AgentSourceSpan {
    /// Start byte offset.
    pub start: usize,
    /// End byte offset.
    pub end: usize,
    /// 1-based source line.
    pub line: u32,
    /// 1-based source column.
    pub column: u32,
}

/// A concrete edit or candidate an agent can try.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct AgentDiagnosticSuggestion {
    /// Human-readable suggestion text.
    pub message: String,
    /// Replacement text, when this is a direct edit.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub replacement: Option<String>,
}

/// Related location or context for a diagnostic.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct AgentRelatedInfo {
    /// Description of the related context.
    pub message: String,
    /// Optional related source span.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub span: Option<AgentSourceSpan>,
}

/// Stable diagnostic payload for repair-oriented tools and agents.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct AgentDiagnostic {
    /// Stable dot-separated code, such as `rewrite.no_match`.
    pub code: String,
    /// Diagnostic severity.
    pub severity: AgentDiagnosticSeverity,
    /// Concise human-facing summary.
    pub message: String,
    /// Optional primary source span.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub primary_span: Option<AgentSourceSpan>,
    /// Machine-readable facts for the diagnostic.
    #[serde(default, skip_serializing_if = "BTreeMap::is_empty")]
    pub facts: BTreeMap<String, String>,
    /// Ordered suggestions, if any.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub suggestions: Vec<AgentDiagnosticSuggestion>,
    /// Related context, if any.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub related: Vec<AgentRelatedInfo>,
}

/// Severity levels for machine-readable agent diagnostics.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum AgentDiagnosticSeverity {
    /// The operation failed.
    Error,
    /// The operation recovered, but the caller should inspect the result.
    Warning,
    /// Informational context.
    Info,
    /// Repair hint or low-priority suggestion.
    Hint,
}

impl fmt::Display for AgentDiagnosticSeverity {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let text = match self {
            Self::Error => "error",
            Self::Warning => "warning",
            Self::Info => "info",
            Self::Hint => "hint",
        };
        f.write_str(text)
    }
}

impl AgentDiagnostic {
    /// Create a diagnostic with no span.
    #[must_use]
    pub fn new(
        severity: AgentDiagnosticSeverity,
        code: impl Into<String>,
        message: impl Into<String>,
    ) -> Self {
        Self {
            code: code.into(),
            severity,
            message: message.into(),
            primary_span: None,
            facts: BTreeMap::new(),
            suggestions: Vec::new(),
            related: Vec::new(),
        }
    }

    /// Create an error diagnostic with no span.
    #[must_use]
    pub fn error(code: impl Into<String>, message: impl Into<String>) -> Self {
        Self::new(AgentDiagnosticSeverity::Error, code, message)
    }

    /// Create a warning diagnostic with no span.
    #[must_use]
    pub fn warning(code: impl Into<String>, message: impl Into<String>) -> Self {
        Self::new(AgentDiagnosticSeverity::Warning, code, message)
    }

    /// Create an info diagnostic with no span.
    #[must_use]
    pub fn info(code: impl Into<String>, message: impl Into<String>) -> Self {
        Self::new(AgentDiagnosticSeverity::Info, code, message)
    }

    /// Create a hint diagnostic with no span.
    #[must_use]
    pub fn hint(code: impl Into<String>, message: impl Into<String>) -> Self {
        Self::new(AgentDiagnosticSeverity::Hint, code, message)
    }

    /// Attach the primary source span.
    #[must_use]
    pub fn with_primary_span(mut self, span: AgentSourceSpan) -> Self {
        self.primary_span = Some(span);
        self
    }

    /// Add a machine-readable fact.
    #[must_use]
    pub fn with_fact(mut self, key: impl Into<String>, value: impl Into<String>) -> Self {
        self.facts.insert(key.into(), value.into());
        self
    }

    /// Add several string facts.
    #[must_use]
    pub fn with_facts<I, K, V>(mut self, facts: I) -> Self
    where
        I: IntoIterator<Item = (K, V)>,
        K: Into<String>,
        V: Into<String>,
    {
        for (key, value) in facts {
            self.facts.insert(key.into(), value.into());
        }
        self
    }

    /// Add a replacement/candidate suggestion.
    #[must_use]
    pub fn with_suggestion(
        mut self,
        message: impl Into<String>,
        replacement: Option<String>,
    ) -> Self {
        self.suggestions.push(AgentDiagnosticSuggestion {
            message: message.into(),
            replacement,
        });
        self
    }

    /// Add related context.
    #[must_use]
    pub fn with_related(
        mut self,
        message: impl Into<String>,
        span: Option<AgentSourceSpan>,
    ) -> Self {
        self.related.push(AgentRelatedInfo {
            message: message.into(),
            span,
        });
        self
    }
}

/// Return a small, deterministic list of nearest string candidates.
#[must_use]
pub(crate) fn nearest_string_candidates<'a, I>(
    query: &str,
    candidates: I,
    limit: usize,
) -> Vec<String>
where
    I: IntoIterator<Item = &'a str>,
{
    let mut scored: Vec<(usize, usize, String)> = candidates
        .into_iter()
        .filter(|candidate| !candidate.is_empty())
        .map(|candidate| {
            let score = similarity_distance(query, candidate);
            (score, candidate.len(), candidate.to_owned())
        })
        .collect();
    scored.sort_by(|a, b| a.0.cmp(&b.0).then(a.1.cmp(&b.1)).then(a.2.cmp(&b.2)));
    scored
        .into_iter()
        .take(limit)
        .filter_map(|(score, _, name)| {
            let cutoff = (query.len().max(name.len()) / 2).max(2);
            (score <= cutoff || name.contains(query) || query.contains(&name)).then_some(name)
        })
        .collect()
}

fn similarity_distance(query: &str, candidate: &str) -> usize {
    let suffix_query = query.rsplit('.').next().unwrap_or(query);
    let suffix_candidate = candidate.rsplit('.').next().unwrap_or(candidate);
    levenshtein(query, candidate).min(levenshtein(suffix_query, suffix_candidate))
}

fn levenshtein(a: &str, b: &str) -> usize {
    let a: Vec<char> = a.chars().collect();
    let b: Vec<char> = b.chars().collect();
    if a.is_empty() {
        return b.len();
    }
    if b.is_empty() {
        return a.len();
    }

    let mut prev: Vec<usize> = (0..=b.len()).collect();
    let mut curr = vec![0; b.len() + 1];
    for (i, ca) in a.iter().enumerate() {
        curr[0] = i + 1;
        for (j, cb) in b.iter().enumerate() {
            let substitution = prev[j] + usize::from(ca != cb);
            let insertion = curr[j] + 1;
            let deletion = prev[j + 1] + 1;
            curr[j + 1] = substitution.min(insertion).min(deletion);
        }
        std::mem::swap(&mut prev, &mut curr);
    }
    prev[b.len()]
}
