// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Public root/backend/error/logic surface types for the Ay backend.
//!
//! Moved from `mod.rs` as part of the root surface split (#2867).
//! All types remain re-exported from the parent module for import stability.

use ay::{Logic, Solver};
use ay_translate::{TranslationSession, TranslationState};
use clean_kernel::FVarId;
use std::fmt;
use thiserror::Error;

use super::translator::LeanExprTranslator;

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
    ///
    /// Wraps ay DPLL(T) panics (known paths: ay#1654, ay#3475, ay#3484)
    /// so they produce a graceful error instead of unwinding through clean.
    #[error("ay solver panicked: {0}")]
    SolverPanic(String),
}

/// Result type for Ay backend operations
pub type AyResult<T> = Result<T, AyError>;

/// Ay SMT solver backend for clean
///
/// Wraps ay's native Rust API and provides translation from kernel expressions
/// to SMT terms. Uses ay-translate for unified term translation.
///
/// Owns a `Solver` and `TranslationState` separately, creating
/// `TranslationSession` borrows on demand. This replaces the deprecated
/// `TranslationContext` which bundled both together.
pub struct AyBackend {
    /// ay solver instance
    pub(crate) solver: Solver,
    /// Translation state: variable/function caches (independent of solver lifetime)
    pub(crate) state: TranslationState<FVarId>,
    /// The logic this solver is configured for
    pub(crate) logic: AyLogic,
    /// Tracks whether the last consumer-facing solve result was SAT, which is
    /// the only state where exposing a model remains sound.
    pub(crate) last_consumer_sat: bool,
    /// clean-local translator implementing ay-translate consumer traits.
    /// Owns all clean-specific translation caches (expr_to_term, registered_fvars,
    /// fvar_func_decls, string_constants) behind interior mutability.
    pub(crate) translator: LeanExprTranslator,
}

impl AyBackend {
    /// Create a borrowed translation session from the owned solver + state.
    ///
    /// This is the session-based replacement for the deprecated `TranslationContext`.
    /// All ay-translate ops and `TermTranslator` methods accept `&mut impl TranslationHost`,
    /// which `TranslationSession` implements.
    pub(crate) fn session(&mut self) -> TranslationSession<'_, FVarId> {
        TranslationSession::new(&mut self.solver, &mut self.state)
    }
}

/// SMT logic to use
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum AyLogic {
    /// Auto-detect theories from terms (SMT-LIB `ALL` logic)
    ///
    /// Sets logic to `ALL` and lets the solver auto-detect the actual
    /// theories used at check-sat time. Useful when the formula may
    /// include datatypes (DT) or when the caller does not want to
    /// manually pick a specific QF_* logic upfront.
    All,

    // =========================================================================
    // Quantifier-free logics
    // =========================================================================
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

    // =========================================================================
    // Quantified logics (support forall/exists with E-matching)
    // =========================================================================
    /// Uninterpreted functions with quantifiers (E-matching)
    Uf,
    /// UF + linear integer arithmetic with quantifiers
    Uflia,
}

impl AyLogic {
    pub(crate) fn to_ay_logic(self) -> Logic {
        match self {
            AyLogic::All => Logic::All,
            AyLogic::QfLia => Logic::QfLia,
            AyLogic::QfLra => Logic::QfLra,
            AyLogic::QfUf => Logic::QfUf,
            AyLogic::QfUflia => Logic::QfUflia,
            AyLogic::QfBv => Logic::QfBv,
            AyLogic::QfAuflia => Logic::QfAuflia,
            AyLogic::QfFp => Logic::QfFp,
            AyLogic::Uf => Logic::Uf,
            AyLogic::Uflia => Logic::Uflia,
        }
    }
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

/// Extract a human-readable message from a panic payload.
///
/// Handles the two common payload types: `&str` and `String`.
/// Falls back to a generic message for other payload types.
pub(crate) fn panic_payload_to_string(payload: &Box<dyn std::any::Any + Send>) -> String {
    if let Some(s) = payload.downcast_ref::<&str>() {
        (*s).to_string()
    } else if let Some(s) = payload.downcast_ref::<String>() {
        s.clone()
    } else {
        "unknown panic payload".to_string()
    }
}
