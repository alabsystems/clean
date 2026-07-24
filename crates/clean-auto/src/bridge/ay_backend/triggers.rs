// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Quantifier trigger types for E-matching instantiation.
//!
//! These types model SMT-LIB trigger patterns for controlling E-matching
//! instantiation in quantified formulas. See ay-dpll `forall_with_triggers`.

#[cfg(test)]
use super::AyTerm;

/// A single trigger pattern for quantifier instantiation
///
/// A trigger is a term (or set of terms for multi-patterns) that guides
/// E-matching instantiation. When the E-graph contains a ground instance
/// matching the trigger pattern, the quantifier is instantiated.
///
/// # Example
///
/// For `forall x. f(x) > 0 => g(x) < 10`, trigger `f(x)` means:
/// - When `f(a)` appears in the E-graph for some ground term `a`
/// - Instantiate the quantifier with `x := a`
///
/// # Contract
///
/// INVARIANT: All terms in `terms` must be from the same solver context
/// INVARIANT: For multi-patterns, `terms.len() >= 2`
/// ENSURES: `is_empty()` iff `terms.is_empty()`
#[derive(Debug, Clone, Default)]
#[cfg(test)]
pub struct AyTriggerPattern {
    /// Terms forming the trigger pattern
    ///
    /// For a single-pattern trigger, this contains one term.
    /// For a multi-pattern trigger, this contains multiple terms that
    /// must all match simultaneously.
    pub terms: Vec<AyTerm>,
}

#[cfg(test)]
impl AyTriggerPattern {
    /// Create a single-term trigger pattern
    ///
    /// # Contract
    ///
    /// REQUIRES: `term` is a valid ay term from an active solver context
    /// ENSURES: `result.terms.len() == 1`
    /// ENSURES: `!result.is_empty()`
    pub fn single(term: AyTerm) -> Self {
        Self { terms: vec![term] }
    }

    /// Create a multi-term trigger pattern
    ///
    /// Multi-patterns require all terms to match simultaneously,
    /// which can be more restrictive but prevents matching loops.
    ///
    /// # Contract
    ///
    /// REQUIRES: `terms.len() >= 2` for meaningful multi-pattern
    /// REQUIRES: All terms are from the same solver context
    /// ENSURES: `result.terms.len() == terms.len()`
    pub fn multi(terms: Vec<AyTerm>) -> Self {
        Self { terms }
    }

    /// Check if this is an empty (default) pattern
    ///
    /// # Contract
    ///
    /// ENSURES: Returns `true` iff `self.terms.is_empty()`
    /// ENSURES: Pure function, no side effects
    pub fn is_empty(&self) -> bool {
        self.terms.is_empty()
    }

    /// Get the number of terms in this trigger pattern
    ///
    /// # Contract
    ///
    /// ENSURES: Returns `self.terms.len()`
    /// ENSURES: `self.len() == 0` iff `self.is_empty()`
    pub fn len(&self) -> usize {
        self.terms.len()
    }
}

/// Policy for handling user-provided triggers vs solver-inferred triggers
///
/// Models cvc5's `--user-pat` option family for controlling trigger selection.
///
/// # Current Status
///
/// **Note:** This enum defines the policy variants but full policy enforcement
/// is not yet implemented. Currently:
/// - `forall`/`exists` always use solver auto-selection
/// - `forall_with_triggers`/`exists_with_triggers` always use provided triggers
///
/// The policy config is stored for future use when ay's Solver API supports
/// policy-based trigger selection. See #849 for tracking.
///
/// # Contract
///
/// INVARIANT: Default variant is `Auto` (preserves existing behavior)
/// ENSURES: All variants are Copy and can be compared for equality
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
#[non_exhaustive]
pub enum TriggerPolicy {
    /// Use solver's automatic trigger selection (default)
    ///
    /// The solver analyzes the quantifier body and selects appropriate triggers.
    /// This is the safest option and preserves existing behavior.
    #[default]
    Auto,

    /// Trust user-provided triggers exclusively (not yet enforced)
    ///
    /// Intended: Only use triggers explicitly provided by the user. If no triggers
    /// are provided, no instantiation occurs (quantifier is essentially ignored).
    ///
    /// **Status:** Stored in config but not yet enforced by quantifier methods.
    UserOnly,

    /// Prefer user triggers, fall back to auto (not yet enforced)
    ///
    /// Intended: Use user-provided triggers if available, otherwise fall back to
    /// solver's automatic selection.
    ///
    /// **Status:** Stored in config but not yet enforced by quantifier methods.
    UserFirst,

    /// Merge user triggers with auto-selected triggers (not yet enforced)
    ///
    /// Intended: Combine user-provided triggers with solver-inferred triggers.
    /// This may increase instantiation but ensures all relevant patterns are tried.
    ///
    /// **Status:** Stored in config but not yet enforced by quantifier methods.
    Merge,
}

/// SMT-LIB trigger pattern for AyProofBackend quantifiers.
///
/// This mirrors [`AyTriggerPattern`] but stores SMT-LIB term strings instead of solver terms.
#[cfg(test)]
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct SmtlibTriggerPattern {
    /// SMT-LIB terms forming the trigger pattern.
    ///
    /// Each term should be a valid SMT-LIB term string, e.g. "(f x)".
    terms: Vec<String>,
}

#[cfg(test)]
impl SmtlibTriggerPattern {
    /// Create a single-term SMT-LIB trigger pattern.
    pub fn single(term: impl Into<String>) -> Self {
        Self {
            terms: vec![term.into()],
        }
    }

    /// Create a multi-term SMT-LIB trigger pattern.
    pub fn multi(terms: Vec<String>) -> Self {
        Self { terms }
    }

    /// Check if this pattern is empty (no terms).
    pub fn is_empty(&self) -> bool {
        self.terms.is_empty()
    }

    pub(super) fn to_smtlib_terms(&self) -> String {
        self.terms.join(" ")
    }
}
