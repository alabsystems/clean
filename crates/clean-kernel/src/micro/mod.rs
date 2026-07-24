// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Micro-Checker: A Minimal Verified Certificate Checker
//!
//! This module provides a minimal, self-contained certificate checker that can
//! verify proof certificates independently of the main kernel. It is designed
//! to be:
//!
//! 1. **Small**: ~1200 lines (implementation), auditable by humans
//! 2. **Self-contained**: Minimal dependencies
//! 3. **Verifiable**: Simple enough to prove correct in clean itself
//! 4. **Correct**: Conservative checking - rejects anything suspicious
//!
//! ## Design Philosophy
//!
//! The micro-checker trades off performance for simplicity and correctness.
//! It only implements the absolute minimum needed to verify certificates:
//!
//! - Basic expression types (no metadata, spans, etc.)
//! - Substitution with de Bruijn indices
//! - Simple WHNF (beta + let only, no delta)
//! - Structural equality after WHNF
//!
//! ## Trust Model
//!
//! If the micro-checker accepts a certificate, the typing derivation is correct.
//! The micro-checker can be verified by:
//! 1. Human auditing (~1200 lines implementation)
//! 2. Formal verification in clean (future)
//! 3. Cross-validation with the main kernel
//!
//! ## Certificate Format
//!
//! Certificates are self-contained: they include all type information needed
//! for verification. The checker doesn't need access to an environment.

mod checker;
mod env;
mod native;
#[cfg(test)]
mod tests;
mod translate;
mod types;

pub use checker::MicroChecker;
pub use env::{MicroConst, MicroEnv};
pub use translate::{
    cross_validate_with_micro, diversity_check_rfl, DiversityOutcome, TranslateError,
};
pub use types::{
    CrossValidationError, MicroCert, MicroError, MicroExpr, MicroLevel, MicroLiteral, MicroResult,
};
