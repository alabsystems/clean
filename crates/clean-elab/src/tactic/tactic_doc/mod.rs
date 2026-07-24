// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tactic documentation extraction and registry.
//!
//! Provides [`TacticDocRegistry`] for looking up tactic documentation by name,
//! category, or free-text search. Used by the JSON-RPC server for IDE hover
//! information and by `#help tactic` interactive queries.
//!
//! # Architecture
//!
//! This module is documentation-only and does not participate in tactic
//! dispatch. It complements [`super::registry::TacticRegistry`] (dispatch)
//! and [`super::tactic_registry::UserTacticRegistry`] (extensibility) by
//! providing rich human-readable content: signatures, descriptions, examples,
//! and cross-references.
//!
//! Documentation entries are defined in the sibling `tactic_doc_entries`
//! module, split by category to stay within function-size limits.

mod entries;

use std::collections::HashMap;

/// Category of a tactic, used for grouping in documentation and search.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum TacticCategory {
    /// Core introduction and elimination tactics: intro, apply, exact, assumption
    Basic,
    /// Rewriting and simplification: rw, simp, unfold, dsimp
    Rewriting,
    /// Logical connectives and case analysis: cases, contradiction, by_contra, split
    Logic,
    /// Arithmetic decision procedures: mathverse, norm_num, ring, linarith
    Arithmetic,
    /// Automated proof search: aesop, decide, library_search
    Search,
    /// Tactic combinators: repeat, try, all_goals, focus
    Combinator,
    /// Goal-closing tactics: rfl, trivial, done, sorry
    Closing,
    /// Advanced structural tactics: conv, calc, induction, generalize
    Advanced,
}

impl TacticCategory {
    /// Human-readable label for the category.
    #[must_use]
    pub(crate) fn label(self) -> &'static str {
        match self {
            Self::Basic => "Basic",
            Self::Rewriting => "Rewriting",
            Self::Logic => "Logic",
            Self::Arithmetic => "Arithmetic",
            Self::Search => "Search",
            Self::Combinator => "Combinator",
            Self::Closing => "Closing",
            Self::Advanced => "Advanced",
        }
    }
}

/// Documentation entry for a single tactic.
#[derive(Debug, Clone)]
pub(crate) struct TacticDoc {
    /// Tactic name as written in Lean syntax.
    pub(crate) name: String,
    /// Classification for grouping.
    pub(crate) category: TacticCategory,
    /// Type-like signature showing expected arguments.
    pub(crate) signature: String,
    /// Human-readable description of what the tactic does.
    pub(crate) description: String,
    /// Example usages (Lean 4 syntax snippets).
    pub(crate) examples: Vec<String>,
    /// Names of related tactics for cross-reference.
    pub(crate) see_also: Vec<String>,
}

/// Registry of tactic documentation entries.
///
/// Provides lookup by name, category filtering, and free-text search across
/// names and descriptions. Populated with documentation for all major
/// implemented tactics on construction.
pub(crate) struct TacticDocRegistry {
    docs: HashMap<String, TacticDoc>,
}

impl TacticDocRegistry {
    /// Create a new registry populated with documentation for all known tactics.
    ///
    /// ENSURES: `get("intro")` and all other core tactics return `Some`.
    /// ENSURES: `all_names().len() >= 30`.
    #[must_use]
    pub(crate) fn new() -> Self {
        let mut docs = HashMap::new();
        for doc in entries::all_tactic_docs() {
            docs.insert(doc.name.clone(), doc);
        }
        Self { docs }
    }

    /// Look up documentation for a tactic by exact name.
    #[must_use]
    pub(crate) fn get(&self, name: &str) -> Option<&TacticDoc> {
        self.docs.get(name)
    }

    /// Return all documented tactics in the given category.
    #[must_use]
    pub(crate) fn by_category(&self, cat: TacticCategory) -> Vec<&TacticDoc> {
        self.docs.values().filter(|d| d.category == cat).collect()
    }

    /// Free-text search across tactic names and descriptions.
    ///
    /// Returns all entries where `query` appears as a case-insensitive
    /// substring of the name or description.
    #[must_use]
    pub(crate) fn search(&self, query: &str) -> Vec<&TacticDoc> {
        let q = query.to_lowercase();
        self.docs
            .values()
            .filter(|d| {
                d.name.to_lowercase().contains(&q) || d.description.to_lowercase().contains(&q)
            })
            .collect()
    }

    /// All registered tactic names, sorted alphabetically.
    #[must_use]
    pub(crate) fn all_names(&self) -> Vec<&str> {
        let mut names: Vec<&str> = self.docs.keys().map(|s| s.as_str()).collect();
        names.sort_unstable();
        names
    }

    /// Format a tactic's documentation as a human-readable string.
    ///
    /// Returns `None` if the tactic is not documented. The output format is
    /// suitable for IDE hover panels and `#help tactic` output.
    #[must_use]
    pub(crate) fn format_doc(&self, name: &str) -> Option<String> {
        let doc = self.docs.get(name)?;
        let mut out = String::with_capacity(256);

        out.push_str(&format!("## {}\n", doc.name));
        out.push_str(&format!("**Category:** {}\n", doc.category.label()));
        out.push_str(&format!("**Signature:** `{}`\n\n", doc.signature));
        out.push_str(&doc.description);
        out.push('\n');

        if !doc.examples.is_empty() {
            out.push_str("\n### Examples\n");
            for ex in &doc.examples {
                out.push_str(&format!("```lean\n{ex}\n```\n"));
            }
        }

        if !doc.see_also.is_empty() {
            out.push_str("\n**See also:** ");
            out.push_str(&doc.see_also.join(", "));
            out.push('\n');
        }

        Some(out)
    }

    /// Number of documented tactics.
    #[must_use]
    pub(crate) fn len(&self) -> usize {
        self.docs.len()
    }
}

#[cfg(test)]
#[path = "../tactic_doc_tests.rs"]
mod tests;
