// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Specification error types

/// Specification error
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum SpecError {
    /// Definition name not found in the specification
    #[error("Unknown definition: {0}")]
    UnknownDefinition(String),
    /// Failed to parse the specification source
    #[error("Parse error: {0}")]
    ParseError(String),
    /// Type elaboration failed for a definition
    #[error("Elaboration error: {0}")]
    ElabError(String),
    /// Type checking failed for a definition
    #[error("Type error: {0}")]
    TypeError(String),
    /// Environment operation failed (e.g., duplicate name)
    #[error("Environment error: {0}")]
    EnvError(String),
    /// Definition exists but has no elaborated form
    #[error("Missing elaboration for definition {0}")]
    MissingElaboration(String),
    /// One declaration spent the whole ambient per-declaration budget.
    ///
    /// **Not a verdict about the declaration.** It says the work was cut short
    /// — neither "it was rejected" nor "it was accepted". It exists so that a
    /// runaway spec declaration is a NAMED failure instead of a silent hang;
    /// see `crates/clean-verify/src/spec/decl_budget.rs` for the measured
    /// incident this replaces and for how to raise or disable the bound.
    #[error(
        "{declaration}: did not finish — spent the whole per-declaration budget of \
         {limit} kernel operations. This is a RUNAWAY GUARD, not a type error: the \
         declaration was cut short, so its verdict is unknown. Raise the bound with \
         CLEAN_SPEC_DECL_BUDGET=<n> (0 = unlimited), or measure what it really costs \
         with CLEAN_SPEC_DECL_BUDGET_TRACE=1."
    )]
    DeclarationBudgetExhausted {
        /// The declaration that did not finish.
        declaration: String,
        /// The tick budget it spent.
        limit: u64,
    },
}
