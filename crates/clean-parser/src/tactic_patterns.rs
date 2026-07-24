// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tactic argument patterns for parser-level argument parsing.
//!
//! Defines [`TacticArgPattern`] which describes how the parser should parse
//! arguments for a named tactic. Used by `_with_tactics` parse APIs to enable
//! pattern-aware argument parsing for registry-dispatched tactics.

use std::collections::HashMap;

/// Argument pattern for a named tactic, controlling how the parser
/// consumes tokens after the tactic name.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TacticArgPattern {
    /// No arguments: `symm`, `contradiction`, `ring`
    Nullary,
    /// Single term argument: `exact e`, `apply e`
    TermArg,
    /// Zero or more identifiers: `intro x y z`, `ext`
    IdentList,
    /// One or more identifiers: `subst h1 h2`, `revert x`
    NonemptyIdentList,
    /// Exactly two space-separated term arguments: `absurd h hn`.
    ///
    /// Each argument is parsed at argument (atom) precedence — `absurd (f x)
    /// (g y)` yields two terms `(f x)` and `(g y)`, NOT a single application
    /// `f x (g y)`. This is the pattern `absurd` needs: `h : a` and `hn : ¬a`
    /// must reach the handler as two distinct, separately-elaborated terms.
    TwoTerms,
    /// Custom compound parsing (rewrite rules, simp lemmas, etc.)
    /// Falls back to generic expression-list parsing.
    ExprList,
}

/// A map of tactic names to their argument patterns.
///
/// Passed to `_with_tactics` parse APIs so the parser can use
/// pattern-aware argument parsing for registry-known tactic names.
pub type TacticPatterns = HashMap<String, TacticArgPattern>;
