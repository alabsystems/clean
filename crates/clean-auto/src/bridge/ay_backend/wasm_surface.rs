// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! wasm32 mirror of the pure-data pieces of `surface.rs`.
//!
//! The native `surface.rs` owns the `ay::Solver` handle and cannot compile
//! without the ay crates, which have no wasm32 port. `AyError`, `AyLogic`,
//! and `AyResult` carry no solver state, so downstream crates (`clean-elab`'s
//! default build names all three) keep compiling against these definitions.
//! Kept variant-for-variant identical to `surface.rs`; the solver-side
//! `to_ay_logic` conversion is native-only and deliberately absent here.

use std::fmt;
use thiserror::Error;

/// Errors from Ay backend operations
#[derive(Debug, Error)]
#[must_use]
#[non_exhaustive]
pub enum AyError {
    /// Expression cannot be translated to SMT
    #[error("unsupported expression: {0}")]
    UnsupportedExpr(String),

    /// Type mismatch during translation
    #[error("type mismatch: expected {expected}, got {got}")]
    TypeMismatch { expected: String, got: String },

    /// Solver returned unknown
    #[error("solver returned unknown")]
    Unknown,

    /// Proof verification failed
    #[error("proof verification failed: {0}")]
    VerificationFailed(String),

    /// Theory not accepted by the configured proof profile
    #[error("theory rejected: {0}")]
    TheoryRejected(String),

    /// Invalid input to a solver API boundary such as quantifier construction
    #[error("invalid input to {operation}: {message}")]
    InvalidInput {
        operation: &'static str,
        message: String,
    },

    /// SMT-LIB script parse or execution error
    #[error("script error: {0}")]
    ScriptError(String),

    /// Solver or required solver-side verification feature is unavailable
    #[error("solver disabled: {0}")]
    SolverDisabled(String),

    /// Ay solver panicked during execution
    #[error("ay solver panicked: {0}")]
    SolverPanic(String),
}

/// Result type for Ay backend operations
pub type AyResult<T> = Result<T, AyError>;

/// SMT logic to use
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum AyLogic {
    /// Auto-detect theories from terms (SMT-LIB `ALL` logic)
    All,
    /// Quantifier-free linear integer arithmetic (mathverse, linarith)
    QfLia,
    /// Quantifier-free linear real arithmetic (linarith with reals)
    QfLra,
    /// Quantifier-free uninterpreted functions (equality reasoning)
    QfUf,
    /// Quantifier-free uninterpreted functions with linear integer arithmetic
    QfUflia,
    /// Quantifier-free bitvectors (bv_mathverse, bv_decide)
    QfBv,
    /// Quantifier-free arrays with UF and LIA (array reasoning)
    QfAuflia,
    /// Quantifier-free IEEE 754 floating-point arithmetic
    QfFp,
    /// Uninterpreted functions with quantifiers (E-matching)
    Uf,
    /// UF + linear integer arithmetic with quantifiers
    Uflia,
}

impl fmt::Display for AyLogic {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            AyLogic::All => write!(f, "ALL"),
            AyLogic::QfLia => write!(f, "QF_LIA"),
            AyLogic::QfLra => write!(f, "QF_LRA"),
            AyLogic::QfUf => write!(f, "QF_UF"),
            AyLogic::QfUflia => write!(f, "QF_UFLIA"),
            AyLogic::QfBv => write!(f, "QF_BV"),
            AyLogic::QfAuflia => write!(f, "QF_AUFLIA"),
            AyLogic::QfFp => write!(f, "QF_FP"),
            AyLogic::Uf => write!(f, "UF"),
            AyLogic::Uflia => write!(f, "UFLIA"),
        }
    }
}

/// clean-owned handle to a solver term. On wasm32 no solver exists, so the
/// handle is an opaque token that is never minted — `translate_expr` refuses
/// before one could be produced.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct AyTerm(());

impl fmt::Display for AyTerm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "t<unavailable>")
    }
}

/// Fast-path backend stub: keeps the curated `AyBackend` surface compiling on
/// wasm32 while every translation or solve entry point reports the solver as
/// unavailable.
pub struct AyBackend {
    config: super::AyBackendConfig,
}

impl AyBackend {
    /// Create a backend stub from full configuration.
    pub fn with_config(config: super::AyBackendConfig) -> Self {
        Self { config }
    }

    /// Get the configuration. pub(crate): the native twin is `pub`, but no
    /// crate outside clean-auto calls it on the wasm surface (only native-only
    /// tests do), and stub internals carry no wider visibility than their
    /// callers require.
    pub(crate) fn config(&self) -> &super::AyBackendConfig {
        &self.config
    }

    fn unavailable() -> AyError {
        AyError::SolverDisabled("SMT automation is native-only (no wasm32 ay solver)".to_string())
    }

    /// Translate a kernel expression: always refuses — the solver is
    /// native-only.
    pub fn translate_expr(&mut self, _expr: &clean_kernel::Expr) -> AyResult<AyTerm> {
        Err(Self::unavailable())
    }

    /// Assert a translated term. Unreachable on wasm32 (no `AyTerm` is ever
    /// minted); kept for signature parity.
    pub fn assert_term(&mut self, _term: AyTerm) {}

    /// Register an FVar with its Lean type: always refuses — the solver is
    /// native-only.
    pub fn register_fvar_from_lean_type(
        &mut self,
        _fvar_id: clean_kernel::FVarId,
        _lean_type: &clean_kernel::Expr,
    ) -> AyResult<AyTerm> {
        Err(Self::unavailable())
    }

    /// Prove a proposition: always refuses — the solver is native-only.
    pub fn prove_with_report(
        &mut self,
        _prop: &clean_kernel::Expr,
    ) -> AyResult<super::solve_types::AySolveEnvelope> {
        Err(Self::unavailable())
    }
}
