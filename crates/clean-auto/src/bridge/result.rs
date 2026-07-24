// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Proof result types returned by the SMT bridge.

use crate::proof::ProofStep;
use crate::smt::SmtModel;
use clean_kernel::Expr;

use super::BridgeError;

/// Result of SMT-based proving with a kernel-verifiable proof term.
///
/// Every `SmtProofResult` carries a proof term and proof step trace.
/// Cases where the solver proved UNSAT but reconstruction failed are
/// represented by [`SmtVerificationResult::Unverified`], not by this type
/// with a missing proof. (#2393, #2387 TB2)
///
/// Use [`SmtProofResult::new`] to construct. Accessor methods are preferred
/// over direct field access to allow future field additions (#2608).
#[derive(Debug)]
#[must_use]
#[non_exhaustive]
pub struct SmtProofResult {
    /// Method used to find the proof
    pub method: ProofMethod,
    /// Human-readable proof sketch
    pub proof_sketch: String,
    /// The kernel proof term and proof step trace.
    /// Always co-present: both are produced during reconstruction (#2391).
    /// Narrowed to `pub(crate)` so `ProofStep` stays crate-private (#2882).
    pub(crate) proof: (Expr, ProofStep),
}

impl SmtProofResult {
    /// Create a proof result with a kernel proof term and proof step.
    pub fn new(
        method: ProofMethod,
        sketch: impl Into<String>,
        proof: Expr,
        step: ProofStep,
    ) -> Self {
        SmtProofResult {
            method,
            proof_sketch: sketch.into(),
            proof: (proof, step),
        }
    }

    /// The proof method that established this result.
    pub fn method(&self) -> ProofMethod {
        self.method
    }

    /// Human-readable proof sketch.
    pub fn proof_sketch(&self) -> &str {
        &self.proof_sketch
    }

    /// Get the proof term.
    pub fn proof_term(&self) -> &Expr {
        &self.proof.0
    }

    /// Get the proof step.
    #[allow(dead_code)] // called from 50+ bridge test modules; not reachable from lib public surface
    pub(crate) fn proof_step(&self) -> &ProofStep {
        &self.proof.1
    }
}

/// Method used for the proof
#[derive(Debug, Clone, Copy)]
#[must_use]
#[non_exhaustive]
pub enum ProofMethod {
    /// Proved by SMT showing negation is unsatisfiable
    SmtUnsat,
}

/// Tri-state verification result from SMT-based proving.
///
/// Distinguishes between "disproved" (solver found a counterexample) and
/// "inconclusive" (solver couldn't determine), which binary `Option<SmtProofResult>`
/// conflated into `None`. Adopts the tri-state pattern from trust-wp's
/// `VerificationResult` (#1303).
#[derive(Debug)]
#[must_use]
#[non_exhaustive]
pub enum SmtVerificationResult {
    /// SMT proved the goal: negated goal is unsatisfiable.
    /// Boxed to reduce enum size variance (SmtProofResult is ~336 bytes
    /// due to carrying Expr + ProofStep proof terms, vs ~72 bytes for other variants).
    Verified(Box<SmtProofResult>),
    /// SMT proved the goal (negation is UNSAT) but proof reconstruction failed
    /// or is not yet available for this goal class. The solver result is correct
    /// but there is no kernel-verifiable proof term. The caller (tactic layer)
    /// decides whether to fall back to a trust axiom. (#2387 TB2)
    Unverified {
        /// Why reconstruction failed or is unavailable.
        reason: BridgeError,
        /// The proof method that established UNSAT.
        method: ProofMethod,
    },
    /// SMT found a counterexample: negated goal is satisfiable.
    Refuted(SmtModel),
    /// SMT solver could not determine satisfiability (timeout, resource limit,
    /// lossy translation, or incomplete decision procedure).
    Unknown(String),
}

impl SmtVerificationResult {
    /// Extract the proof result if verification succeeded.
    pub fn verified(self) -> Option<SmtProofResult> {
        match self {
            Self::Verified(proof) => Some(*proof),
            _ => None,
        }
    }

    /// Check if the result is a successful verification.
    pub fn is_verified(&self) -> bool {
        matches!(self, Self::Verified(_))
    }

    /// Check if the result is a refutation (counterexample found).
    pub fn is_refuted(&self) -> bool {
        matches!(self, Self::Refuted(_))
    }

    /// Check if the solver proved UNSAT but no kernel proof term is available.
    pub fn is_unverified(&self) -> bool {
        matches!(self, Self::Unverified { .. })
    }

    /// Check if the result is unknown/inconclusive.
    pub fn is_unknown(&self) -> bool {
        matches!(self, Self::Unknown(_))
    }

    /// Extract a human-readable summary if the result is a refutation.
    ///
    /// Returns `None` for non-refutation results. This is the public read
    /// surface for the `Refuted` variant since `SmtModel` stays crate-private (#2882).
    pub fn refutation_summary(&self) -> Option<String> {
        match self {
            Self::Refuted(model) => Some(model.display_summary()),
            _ => None,
        }
    }
}
