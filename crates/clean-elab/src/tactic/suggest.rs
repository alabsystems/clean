// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Suggestion tactics backed by `library_search`.
//!
//! Provides the `exact?` and `apply?` style ranked suggestion tactics. These
//! return ranked `Suggestion` values without modifying the proof state.

use clean_kernel::name::Name;

use super::library_search::{
    library_search_with_config, LibrarySearchConfig, LibrarySearchMatchKind, LibrarySearchResult,
};
use super::{ProofState, TacticError};

const DEFAULT_MAX_SUGGESTIONS: usize = 20;
const SEARCH_RESULT_BUDGET: usize = DEFAULT_MAX_SUGGESTIONS * 3;

/// A ranked tactic suggestion produced by library search.
#[derive(Debug, Clone)]
pub(crate) struct Suggestion {
    /// The tactic text to present to the user.
    pub(crate) tactic_text: String,
    /// The lemma or hypothesis name behind the suggestion.
    pub(crate) lemma_name: Name,
    /// Confidence score copied from `LibrarySearchResult::relevance`.
    pub(crate) confidence: f64,
}

/// Evaluate `exact?` suggestions for the current goal.
///
/// Returns only exact matches, ranked by library-search relevance.
pub(crate) fn eval_exact_question(state: &mut ProofState) -> Result<Vec<Suggestion>, TacticError> {
    let config = LibrarySearchConfig {
        max_results: SEARCH_RESULT_BUDGET,
        include_partial: false,
        search_instances: false,
        ..LibrarySearchConfig::default()
    };
    let results = library_search_with_config(state, config)?;
    Ok(collect_suggestions(results, |kind| {
        kind == LibrarySearchMatchKind::Exact
    }))
}

/// Evaluate `apply?` suggestions for the current goal.
///
/// Returns exact and apply matches, ranked by library-search relevance.
pub(crate) fn eval_apply_question(state: &mut ProofState) -> Result<Vec<Suggestion>, TacticError> {
    let config = LibrarySearchConfig {
        max_results: SEARCH_RESULT_BUDGET,
        include_partial: true,
        search_instances: false,
        ..LibrarySearchConfig::default()
    };
    let results = library_search_with_config(state, config)?;
    Ok(collect_suggestions(results, |kind| {
        matches!(
            kind,
            LibrarySearchMatchKind::Exact | LibrarySearchMatchKind::Apply
        )
    }))
}

/// Format a list of suggestions for user-facing display.
pub(crate) fn format_suggestions(suggestions: &[Suggestion]) -> String {
    if suggestions.is_empty() {
        return "No suggestions found.".to_string();
    }

    let mut output = String::new();
    output.push_str("Suggestions:\n");

    for (idx, suggestion) in suggestions.iter().enumerate() {
        output.push_str(&(idx + 1).to_string());
        output.push_str(". ");
        output.push_str(&suggestion.tactic_text);
        output.push_str(" (confidence: ");
        output.push_str(&format!("{:.2}", suggestion.confidence));
        output.push(')');

        if idx + 1 < suggestions.len() {
            output.push('\n');
        }
    }

    output
}

fn collect_suggestions(
    results: Vec<LibrarySearchResult>,
    keep: impl Fn(LibrarySearchMatchKind) -> bool,
) -> Vec<Suggestion> {
    let mut suggestions = Vec::new();

    for result in results {
        if !keep(result.match_kind) {
            continue;
        }

        suggestions.push(Suggestion {
            tactic_text: suggestion_text(&result),
            lemma_name: result.name,
            confidence: result.relevance,
        });

        if suggestions.len() >= DEFAULT_MAX_SUGGESTIONS {
            break;
        }
    }

    suggestions
}

fn suggestion_text(result: &LibrarySearchResult) -> String {
    if !result.suggestion.is_empty() {
        return result.suggestion.clone();
    }

    match result.match_kind {
        LibrarySearchMatchKind::Exact => format!("exact {}", result.name),
        LibrarySearchMatchKind::Apply => format!("apply {}", result.name),
        _ => result.name.to_string(),
    }
}
