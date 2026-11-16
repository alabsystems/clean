// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! TLA+ Encoding and Tactics for Clean
//!
//! This crate provides the TLA+ to Clean translation layer for TLAPS integration.
//! It enables Clean to serve as a higher-order logic backend for TLA+ proof
//! obligations that SMT solvers cannot handle.
//!
//! ## Architecture
//!
//! ```text
//! ┌────────────┐     ┌─────────────────┐     ┌──────────────┐
//! │ TLAPS      │     │ clean-tla       │     │ clean        │
//! │ (ty repo)│────▶│ (this crate)    │────▶│ kernel       │
//! │            │     │                 │     │              │
//! │ Obligations│     │ TLA+ encoding   │     │ Type checker │
//! │ (sequents) │     │ Automation      │     │ Proof certs  │
//! └────────────┘     └─────────────────┘     └──────────────┘
//! ```
//!
//! ## TLA+ Encoding Strategy
//!
//! TLA+ uses untyped set theory where everything is a "constant" type.
//! We embed TLA+ into clean's dependent type theory using:
//!
//! 1. **TLA Universe**: A universe type containing all TLA+ values
//! 2. **Membership**: Set membership relation
//! 3. **Bounded quantification**: ∀x ∈ S and ∃x ∈ S
//! 4. **Function application**: DOMAIN and function apply
//!
//! ## References
//!
//! - Issue #12: TLAPS backend requirements for TY
//! - Design: `designs/2026-01-15-tlaps-backend-design.md`
//! - TLAPM source: <https://github.com/tlaplus/tlapm>

pub mod bench;
#[cfg(feature = "cli")]
pub mod cli;
mod core_ast;
pub mod encoding;
pub mod finite;
pub mod obligation;
pub mod refine;
pub mod semantics;
pub mod tactic;
pub mod ty_cert;

pub use encoding::{TlaExpr, TlaFormula, TlaOperator};
pub use obligation::{TlaDeclare, TlaHypothesis, TlaObligation};
pub use tactic::TlaAutoResult;
pub use tla_core;

use thiserror::Error;

/// Errors from TLA+ processing
#[derive(Error, Debug, Clone)]
#[non_exhaustive]
pub enum TlaError {
    /// TLA+ expression syntax is invalid or malformed
    #[error("Invalid TLA+ expression: {0}")]
    InvalidExpr(String),

    /// TLA+ operator not recognized (not in standard library or user-defined)
    #[error("Unknown TLA+ operator: {0}")]
    UnknownOperator(String),

    /// Type mismatch during TLA+ to Lean encoding
    #[error("Type mismatch in TLA+ encoding: expected {expected}, got {actual}")]
    TypeMismatch {
        /// The expected type in the Lean encoding
        expected: String,
        /// The actual type found
        actual: String,
    },

    /// Proof obligation could not be discharged
    #[error("Failed to prove obligation: {0}")]
    ProofFailed(String),

    /// Error from the underlying clean-kernel
    #[error("Kernel error: {0}")]
    KernelError(String),

    /// Error during tactic execution
    #[error("Tactic error: {0}")]
    TacticError(String),

    /// `tla-core` AST shape is valid TLA+ but is not yet representable in the
    /// current clean wire layer.
    #[error("Unsupported tla-core AST: {0}")]
    UnsupportedCoreAst(String),
}

impl From<clean_kernel::env::EnvError> for TlaError {
    fn from(e: clean_kernel::env::EnvError) -> Self {
        TlaError::KernelError(e.to_string())
    }
}
