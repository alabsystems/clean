// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Bridge error types for proof construction failures.

use crate::smt::TermId;
use std::fmt;
use thiserror::Error;

/// Errors from bridge proof construction.
///
/// Replaces silent `Option<T>` returns with typed errors so callers know
/// *why* proof construction failed, not just *that* it failed.
#[must_use = "bridge errors should be handled or propagated"]
#[derive(Debug, Clone, Error, PartialEq)]
#[non_exhaustive]
pub enum BridgeError {
    /// Sort inference failed for a type expression.
    /// Indicates `TypeChecker::infer_sort` returned an error.
    #[error("sort inference failed: {context}")]
    InferSortFailed { context: String },

    /// Function type inference failed during congruence proof construction.
    #[error("congruence universe inference failed: {context}")]
    CongruenceInferFailed { context: String },

    /// Required SMT term → kernel Expr mapping is missing.
    #[error("missing term-to-expr mapping for term {0}")]
    MissingTermMapping(TermId),

    /// Required SMT term → type mapping is missing.
    #[error("missing term-to-type mapping for term {0}")]
    MissingTypeMapping(TermId),

    /// E-graph or proof trace lookup failed.
    #[error("proof trace lookup failed: {0}")]
    ProofTraceFailed(String),

    /// Hypothesis lookup failed.
    #[error("hypothesis not found for terms ({0}, {1})")]
    HypothesisNotFound(TermId, TermId),

    /// Expression could not be translated to SMT terms.
    #[error("translation failed: {context}")]
    TranslationFailed { context: String },

    /// Expression classification did not match any known logical form.
    #[error("unsupported expression: {context}")]
    UnsupportedExpr { context: String },

    /// `prove()` called more than once on the same bridge instance.
    /// The bridge accumulates solver state (clauses, lossy atoms) across calls,
    /// making reuse unsound. Create a new bridge per proof attempt. (#2836)
    #[error("bridge reuse: prove() already called on this instance")]
    BridgeReuse,
}

/// Result type for bridge proof construction.
pub type BridgeResult<T> = Result<T, BridgeError>;

impl fmt::Display for TermId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "t{}", self.0)
    }
}
