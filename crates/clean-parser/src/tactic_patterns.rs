// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tactic argument patterns for parser-level argument parsing.
//!
//! Defines [`TacticArgPattern`] which describes how the parser should parse
//! arguments for a named tactic. Used by `_with_tactics` parse APIs to enable
//! pattern-aware argument parsing for registry-dispatched tactics.

use std::collections::HashMap;

/// The name the `only` of `grind only` travels under.
///
/// [`TacticArgPattern::BracketedParamList`] records `only` as a leading
/// argument rather than dropping it, because Lean's `grind only` suppresses
/// the ambient `@[grind]` set. The name is built with
/// `SurfaceName::generated_path`, so its single component's origin is
/// `Generated` and `SurfaceName::same_syntax` distinguishes it from a user
/// lemma spelled the same way — structural equality alone would not.
pub const GRIND_ONLY_MARKER: &str = "_grind_only";

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
    /// Lean's `grind`-shaped argument list: an optional `only`, then an
    /// optional bracketed, comma-separated parameter list — `grind`,
    /// `grind only`, `grind [f, g]`, `grind only [f]`.
    ///
    /// Distinct from [`Self::ExprList`], which reads a BARE comma list and so
    /// would read `grind [f, g]` as the single list-literal term `[f, g]`, and
    /// from [`Self::IdentList`], which cannot see the brackets at all. The
    /// per-parameter `←`/`→`/`=`/`-` modifiers Lean allows are consumed and
    /// dropped here exactly as `parse_simp_lemmas` drops simp's — the tactic
    /// applies its parameters left to right and does not model a direction.
    ///
    /// `only` is NOT dropped: it is recorded as a leading argument named
    /// [`GRIND_ONLY_MARKER`], because Lean's `grind only` suppresses the
    /// ambient `@[grind]` set (measured on v4.30.0-rc2) and a tactic that
    /// ignored it would close goals Lean rejects.
    BracketedParamList,
}

/// A map of tactic names to their argument patterns.
///
/// Passed to `_with_tactics` parse APIs so the parser can use
/// pattern-aware argument parsing for registry-known tactic names.
pub type TacticPatterns = HashMap<String, TacticArgPattern>;
