// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Feedback classification for kernel rejection reasons.
//!
//! When the kernel rejects a candidate theorem, the `FeedbackAnalyzer`
//! classifies the error to guide search. This enables the discovery loop
//! to prune unpromising parameter regions and focus on likely-valid areas.
//!
//! Part of #3272.

use std::collections::HashMap;

use crate::candidate::{CandidateId, VerificationOutcome};

/// Classification of why the kernel rejected a candidate.
///
/// Each category maps to a structural reason for failure, enabling
/// the search strategy to adapt (e.g., avoid regions that always
/// produce type mismatches).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum FeedbackCategory {
    /// Proof type doesn't match the claimed statement type.
    TypeMismatch,
    /// Universe level inconsistency or constraint violation.
    UniverseError,
    /// Referenced a constant not registered in the environment.
    UnknownConst(String),
    /// Expected a Sort (Type/Prop) but got something else.
    SortError,
    /// Definitional equality check failed during type checking.
    DefEqFailure,
    /// Catch-all for unclassified errors.
    Other(String),
}

impl std::fmt::Display for FeedbackCategory {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::TypeMismatch => write!(f, "TypeMismatch"),
            Self::UniverseError => write!(f, "UniverseError"),
            Self::UnknownConst(name) => write!(f, "UnknownConst({name})"),
            Self::SortError => write!(f, "SortError"),
            Self::DefEqFailure => write!(f, "DefEqFailure"),
            Self::Other(msg) => write!(f, "Other({msg})"),
        }
    }
}

/// A single feedback entry from a failed verification attempt.
#[derive(Debug, Clone)]
pub struct FeedbackEntry {
    /// The candidate that was rejected.
    pub candidate_id: CandidateId,
    /// Classified reason for rejection.
    pub category: FeedbackCategory,
    /// Raw error string from the kernel.
    pub raw_error: String,
    /// Optional hint about which parameter might be causing the failure.
    pub param_hint: Option<String>,
}

/// Aggregate summary of feedback across many candidates.
#[derive(Debug, Clone)]
pub struct FeedbackSummary {
    /// Count of rejections per category.
    pub category_counts: HashMap<FeedbackCategory, u64>,
    /// The most common rejection category (if any).
    pub most_common: Option<FeedbackCategory>,
    /// Total number of feedback entries analyzed.
    pub total_entries: u64,
    /// Number of distinct categories observed.
    pub distinct_categories: usize,
}

/// Classifies kernel rejection errors to guide the discovery search.
pub struct FeedbackAnalyzer;

impl FeedbackAnalyzer {
    /// Create a new feedback analyzer.
    #[must_use]
    pub fn new() -> Self {
        Self
    }

    /// Classify a verification outcome into a feedback entry.
    ///
    /// Returns `None` if the outcome was successful (no error to classify).
    #[must_use]
    pub fn classify(&self, outcome: &VerificationOutcome) -> Option<FeedbackEntry> {
        if outcome.verified {
            return None;
        }

        let raw_error = outcome.error.as_deref().unwrap_or("unknown error");
        let category = classify_error(raw_error);
        let param_hint = extract_param_hint(raw_error, &category);

        Some(FeedbackEntry {
            candidate_id: outcome.candidate_id,
            category,
            raw_error: raw_error.to_owned(),
            param_hint,
        })
    }

    /// Aggregate feedback entries into a summary.
    #[must_use]
    pub fn aggregate(&self, entries: &[FeedbackEntry]) -> FeedbackSummary {
        let mut category_counts: HashMap<FeedbackCategory, u64> = HashMap::new();

        for entry in entries {
            *category_counts.entry(entry.category.clone()).or_insert(0) += 1;
        }

        let most_common = category_counts
            .iter()
            .max_by_key(|(_, &count)| count)
            .map(|(cat, _)| cat.clone());

        let distinct_categories = category_counts.len();

        FeedbackSummary {
            category_counts,
            most_common,
            total_entries: entries.len() as u64,
            distinct_categories,
        }
    }
}

impl Default for FeedbackAnalyzer {
    fn default() -> Self {
        Self::new()
    }
}

/// Classify an error string into a `FeedbackCategory`.
///
/// Parses the error message looking for known patterns from the kernel's
/// `TypeError` and `EnvError` variants.
fn classify_error(error: &str) -> FeedbackCategory {
    let lower = error.to_lowercase();

    // Order matters: check more specific patterns first.
    if lower.contains("unknown constant") || lower.contains("unknown const") {
        // Extract the constant name if present.
        let name = extract_const_name(error);
        return FeedbackCategory::UnknownConst(name);
    }

    if lower.contains("type mismatch") {
        return FeedbackCategory::TypeMismatch;
    }

    if lower.contains("universe") || lower.contains("level") {
        return FeedbackCategory::UniverseError;
    }

    if lower.contains("expected sort") || lower.contains("sort error") {
        return FeedbackCategory::SortError;
    }

    if lower.contains("def_eq") || lower.contains("definitional equality") {
        return FeedbackCategory::DefEqFailure;
    }

    // Fall through to catch-all.
    let truncated = if error.len() > 80 {
        format!("{}...", &error[..80])
    } else {
        error.to_owned()
    };
    FeedbackCategory::Other(truncated)
}

/// Try to extract a constant name from an "Unknown constant" error message.
fn extract_const_name(error: &str) -> String {
    // Pattern: "Unknown constant: <name>"
    if let Some(idx) = error.find(": ") {
        let after_colon = &error[idx + 2..];
        // Take up to the next whitespace or end of string.
        let name = after_colon.split_whitespace().next().unwrap_or(after_colon);
        return name.to_owned();
    }
    "unknown".to_owned()
}

/// Try to extract a parameter hint from the error and category.
fn extract_param_hint(error: &str, category: &FeedbackCategory) -> Option<String> {
    match category {
        FeedbackCategory::UnknownConst(name) => {
            Some(format!("constant '{name}' not registered in environment"))
        }
        FeedbackCategory::TypeMismatch => {
            // If the error contains "expected" and "got", extract both.
            if error.contains("expected") && (error.contains("got") || error.contains("inferred")) {
                Some("check that proof term matches statement type".to_owned())
            } else {
                None
            }
        }
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::candidate::CandidateId;

    fn make_failed_outcome(error: &str) -> VerificationOutcome {
        VerificationOutcome {
            candidate_id: CandidateId(0),
            verified: false,
            inferred_type: None,
            error: Some(error.to_owned()),
            time_ns: 100,
        }
    }

    fn make_verified_outcome() -> VerificationOutcome {
        VerificationOutcome {
            candidate_id: CandidateId(1),
            verified: true,
            inferred_type: None,
            error: None,
            time_ns: 50,
        }
    }

    #[test]
    fn test_classify_verified_returns_none() {
        let analyzer = FeedbackAnalyzer::new();
        let outcome = make_verified_outcome();
        assert!(
            analyzer.classify(&outcome).is_none(),
            "verified outcomes should not produce feedback"
        );
    }

    #[test]
    fn test_classify_type_mismatch() {
        let analyzer = FeedbackAnalyzer::new();
        let outcome = make_failed_outcome("Type mismatch: expected Nat, got Bool");
        let entry = analyzer
            .classify(&outcome)
            .expect("should classify failed outcome");
        assert_eq!(entry.category, FeedbackCategory::TypeMismatch);
        assert_eq!(entry.candidate_id, CandidateId(0));
    }

    #[test]
    fn test_classify_unknown_constant() {
        let analyzer = FeedbackAnalyzer::new();
        let outcome = make_failed_outcome("Unknown constant: Foo.bar");
        let entry = analyzer
            .classify(&outcome)
            .expect("should classify failed outcome");
        assert_eq!(
            entry.category,
            FeedbackCategory::UnknownConst("Foo.bar".to_owned())
        );
        assert!(entry.param_hint.is_some());
    }

    #[test]
    fn test_classify_universe_error() {
        let analyzer = FeedbackAnalyzer::new();
        let outcome = make_failed_outcome("universe level mismatch in application");
        let entry = analyzer
            .classify(&outcome)
            .expect("should classify failed outcome");
        assert_eq!(entry.category, FeedbackCategory::UniverseError);
    }

    #[test]
    fn test_classify_sort_error() {
        let analyzer = FeedbackAnalyzer::new();
        let outcome = make_failed_outcome("Expected sort, got: App(...)");
        let entry = analyzer
            .classify(&outcome)
            .expect("should classify failed outcome");
        assert_eq!(entry.category, FeedbackCategory::SortError);
    }

    #[test]
    fn test_classify_def_eq_failure() {
        let analyzer = FeedbackAnalyzer::new();
        let outcome = make_failed_outcome("def_eq check failed between terms");
        let entry = analyzer
            .classify(&outcome)
            .expect("should classify failed outcome");
        assert_eq!(entry.category, FeedbackCategory::DefEqFailure);
    }

    #[test]
    fn test_classify_other() {
        let analyzer = FeedbackAnalyzer::new();
        let outcome = make_failed_outcome("something completely unexpected happened");
        let entry = analyzer
            .classify(&outcome)
            .expect("should classify failed outcome");
        match &entry.category {
            FeedbackCategory::Other(_) => {} // expected
            other => panic!("expected Other, got {other:?}"),
        }
    }

    #[test]
    fn test_classify_no_error_string() {
        let analyzer = FeedbackAnalyzer::new();
        let outcome = VerificationOutcome {
            candidate_id: CandidateId(5),
            verified: false,
            inferred_type: None,
            error: None,
            time_ns: 100,
        };
        let entry = analyzer
            .classify(&outcome)
            .expect("should classify failed outcome even without error string");
        match &entry.category {
            FeedbackCategory::Other(_) => {} // expected
            other => panic!("expected Other for missing error, got {other:?}"),
        }
    }

    #[test]
    fn test_aggregate_empty() {
        let analyzer = FeedbackAnalyzer::new();
        let summary = analyzer.aggregate(&[]);
        assert_eq!(summary.total_entries, 0);
        assert_eq!(summary.distinct_categories, 0);
        assert!(summary.most_common.is_none());
    }

    #[test]
    fn test_aggregate_mixed_errors() {
        let analyzer = FeedbackAnalyzer::new();
        let entries = vec![
            FeedbackEntry {
                candidate_id: CandidateId(0),
                category: FeedbackCategory::TypeMismatch,
                raw_error: "Type mismatch".to_owned(),
                param_hint: None,
            },
            FeedbackEntry {
                candidate_id: CandidateId(1),
                category: FeedbackCategory::TypeMismatch,
                raw_error: "Type mismatch".to_owned(),
                param_hint: None,
            },
            FeedbackEntry {
                candidate_id: CandidateId(2),
                category: FeedbackCategory::UnknownConst("X".to_owned()),
                raw_error: "Unknown constant: X".to_owned(),
                param_hint: None,
            },
        ];

        let summary = analyzer.aggregate(&entries);
        assert_eq!(summary.total_entries, 3);
        assert_eq!(summary.distinct_categories, 2);
        assert_eq!(summary.most_common, Some(FeedbackCategory::TypeMismatch));
        assert_eq!(summary.category_counts[&FeedbackCategory::TypeMismatch], 2);
        assert_eq!(
            summary.category_counts[&FeedbackCategory::UnknownConst("X".to_owned())],
            1
        );
    }

    #[test]
    fn test_aggregate_single_category() {
        let analyzer = FeedbackAnalyzer::new();
        let entries = vec![
            FeedbackEntry {
                candidate_id: CandidateId(0),
                category: FeedbackCategory::SortError,
                raw_error: "Expected sort".to_owned(),
                param_hint: None,
            },
            FeedbackEntry {
                candidate_id: CandidateId(1),
                category: FeedbackCategory::SortError,
                raw_error: "Expected sort".to_owned(),
                param_hint: None,
            },
        ];

        let summary = analyzer.aggregate(&entries);
        assert_eq!(summary.total_entries, 2);
        assert_eq!(summary.distinct_categories, 1);
        assert_eq!(summary.most_common, Some(FeedbackCategory::SortError));
    }

    #[test]
    fn test_type_mismatch_param_hint() {
        let analyzer = FeedbackAnalyzer::new();
        let outcome =
            make_failed_outcome("Type mismatch: expected Nat, got something inferred wrong");
        let entry = analyzer.classify(&outcome).expect("should classify");
        assert!(
            entry.param_hint.is_some(),
            "type mismatch with expected/inferred should produce a param hint"
        );
    }

    #[test]
    fn test_feedback_category_display() {
        assert_eq!(FeedbackCategory::TypeMismatch.to_string(), "TypeMismatch");
        assert_eq!(FeedbackCategory::UniverseError.to_string(), "UniverseError");
        assert_eq!(
            FeedbackCategory::UnknownConst("Foo".to_owned()).to_string(),
            "UnknownConst(Foo)"
        );
        assert_eq!(FeedbackCategory::SortError.to_string(), "SortError");
        assert_eq!(FeedbackCategory::DefEqFailure.to_string(), "DefEqFailure");
    }

    #[test]
    fn test_long_error_truncated_in_other() {
        let long_error = "a".repeat(200);
        let category = classify_error(&long_error);
        match category {
            FeedbackCategory::Other(msg) => {
                assert!(
                    msg.len() < 100,
                    "Other category should truncate long messages"
                );
                assert!(msg.ends_with("..."));
            }
            other => panic!("expected Other, got {other:?}"),
        }
    }
}
