// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Superposition calculus (ported from E prover)
//!
//! This module implements the superposition calculus, a complete and refutationally
//! complete calculus for first-order logic with equality. It is based on the work
//! of Bachmair & Ganzinger and implemented in provers like E, Vampire, and SPASS.
//!
//! # Overview
//!
//! Superposition is a saturation-based theorem prover that:
//! 1. Takes a set of clauses (CNF)
//! 2. Applies inference rules until contradiction or saturation
//! 3. Uses term orderings to restrict inferences (completeness-preserving)
//!
//! # Inference Rules
//!
//! ## Generating inferences:
//! - **Superposition Left**: Rewrites into negative literals
//! - **Superposition Right**: Rewrites into positive literals
//! - **Equality Resolution**: Resolves reflexive equalities
//! - **Equality Factoring**: Factors equal positive literals
//!
//! ## Simplification rules:
//! - **Demodulation**: Simplifies terms using oriented equations
//! - **Subsumption**: Removes redundant clauses
//! - **Tautology deletion**: Removes trivially true clauses
//!
//! # Term Orderings
//!
//! The implementation supports:
//! - **KBO** (Knuth-Bendix Ordering): Weight-based, efficient
//! - **LPO** (Lexicographic Path Ordering): Symbol precedence-based
//!
//! # Given Clause Loop
//!
//! Uses the DISCOUNT loop variant:
//! 1. Select a clause from the set of unprocessed clauses
//! 2. Simplify it with processed clauses
//! 3. Generate new clauses by inference with processed clauses
//! 4. Add to processed set

mod clause;
mod inference;
mod ordering;
mod prover;
mod terms;

pub use clause::*;
pub use ordering::*;
pub use prover::*;
pub use terms::*;

#[cfg(test)]
mod tests;
