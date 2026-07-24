// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Error categorization for formalization failures.
//!
//! Classifies error messages from the formalization pipeline into actionable
//! categories to guide retry strategy and aggregate diagnostics.

use std::collections::HashMap;

use serde::{Deserialize, Serialize};

/// Category of formalization error for diagnostics and retry strategy.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum ErrorCategory {
    /// LaTeX parser failed to extract statement.
    ParseError,
    /// Lean code fails type-checking in the kernel.
    TypeError,
    /// Code references a type that doesn't exist in Init/Mathlib.
    UnknownType,
    /// Tactic application failed.
    TacticFailure,
    /// LLM produced malformed or empty output.
    MalformedOutput,
    /// Structural validation failed (wrong keyword, unbalanced parens, etc.).
    StructuralError,
    /// Uncategorized error.
    Other,
}

impl ErrorCategory {
    /// Classify an error message string into a category.
    #[must_use]
    pub fn classify(error_msg: &str) -> Self {
        let lower = error_msg.to_lowercase();
        if lower.contains("unknown identifier")
            || lower.contains("unknown constant")
            || lower.contains("unknown namespace")
        {
            return Self::UnknownType;
        }
        if lower.contains("type mismatch") || lower.contains("has type") {
            return Self::TypeError;
        }
        if lower.contains("tactic") || lower.contains("unsolved goals") {
            return Self::TacticFailure;
        }
        if lower.contains("parse") || lower.contains("expected") || lower.contains("syntax") {
            return Self::ParseError;
        }
        if lower.contains("unbalanced")
            || lower.contains("doesn't start with")
            || lower.contains("sorry")
        {
            return Self::StructuralError;
        }
        if lower.contains("empty") || lower.contains("malformed") {
            return Self::MalformedOutput;
        }
        Self::Other
    }
}

/// Error distribution across categories.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct ErrorDistribution {
    /// Count per error category.
    pub counts: HashMap<String, usize>,
    /// Total errors.
    pub total: usize,
}

impl ErrorDistribution {
    /// Record a categorized error.
    pub fn record(&mut self, category: &ErrorCategory) {
        let key = format!("{category:?}");
        *self.counts.entry(key).or_insert(0) += 1;
        self.total += 1;
    }

    /// Get the most common error category.
    #[must_use]
    pub fn most_common(&self) -> Option<String> {
        self.counts
            .iter()
            .max_by_key(|(_, count)| *count)
            .map(|(cat, _)| cat.clone())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_pipeline_error_categorization() {
        assert_eq!(
            ErrorCategory::classify("unknown identifier 'Foo'"),
            ErrorCategory::UnknownType,
        );
        assert_eq!(
            ErrorCategory::classify("type mismatch: expected Nat, got Bool"),
            ErrorCategory::TypeError,
        );
        assert_eq!(
            ErrorCategory::classify("tactic 'simp' failed, unsolved goals remain"),
            ErrorCategory::TacticFailure,
        );
        assert_eq!(
            ErrorCategory::classify("expected ':' at column 15"),
            ErrorCategory::ParseError,
        );
        assert_eq!(
            ErrorCategory::classify("unbalanced parentheses: 3 open, 2 close"),
            ErrorCategory::StructuralError,
        );
        assert_eq!(
            ErrorCategory::classify("empty response from LLM"),
            ErrorCategory::MalformedOutput,
        );
        assert_eq!(
            ErrorCategory::classify("a random unrelated problem occurred"),
            ErrorCategory::Other,
        );
    }

    #[test]
    fn test_error_distribution_tracking() {
        let mut dist = ErrorDistribution::default();

        dist.record(&ErrorCategory::TypeError);
        dist.record(&ErrorCategory::TypeError);
        dist.record(&ErrorCategory::UnknownType);
        dist.record(&ErrorCategory::TacticFailure);

        assert_eq!(dist.total, 4);
        assert_eq!(dist.counts.get("TypeError"), Some(&2));
        assert_eq!(dist.counts.get("UnknownType"), Some(&1));
        assert_eq!(
            dist.most_common().as_deref(),
            Some("TypeError"),
            "TypeError should be most common"
        );
    }
}
