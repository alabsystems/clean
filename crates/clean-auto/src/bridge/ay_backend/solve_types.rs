// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Solve-result types for the Ay backend.

use ay::{SolveResult, UnknownReason, VerifiedSolveResult};
use std::fmt;

/// clean-local mirror of ay solve verification counters.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
#[must_use]
pub struct AyVerificationSummary {
    /// True when ay validated the SAT model on this solve call.
    pub sat_model_validated: bool,
    /// True when ay produced an UNSAT proof artifact for this solve call.
    pub unsat_proof_available: bool,
    /// Number of proof-checker failures recorded by the solver.
    pub unsat_proof_checker_failures: u64,
    /// Number of assertions independently checked by the model validator.
    pub sat_independent_checks: u64,
    /// Number of assertions accepted through theory-side delegation.
    pub sat_delegated_checks: u64,
    /// Number of assertions whose SAT evidence stayed incomplete.
    pub sat_incomplete_checks: u64,
}

impl From<ay_dpll::api::VerificationSummary> for AyVerificationSummary {
    fn from(summary: ay_dpll::api::VerificationSummary) -> Self {
        Self {
            sat_model_validated: summary.sat_model_validated,
            unsat_proof_available: summary.unsat_proof_available,
            unsat_proof_checker_failures: summary.unsat_proof_checker_failures,
            sat_independent_checks: summary.sat_independent_checks,
            sat_delegated_checks: summary.sat_delegated_checks,
            sat_incomplete_checks: summary.sat_incomplete_checks,
        }
    }
}

/// clean-local mirror of ay's runtime verification level.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[must_use]
#[non_exhaustive]
pub enum AyVerificationLevel {
    /// No additional runtime verification beyond trusting solver correctness.
    Trusted,
    /// Debug assertions were active during solving.
    DebugChecked,
    /// Proof production or SAT model checking was active during solving.
    ProofChecked,
    /// Both debug checks and proof production were active during solving.
    FullyVerified,
}

impl From<ay_dpll::api::VerificationLevel> for AyVerificationLevel {
    fn from(level: ay_dpll::api::VerificationLevel) -> Self {
        if level.is_trusted_only() {
            Self::Trusted
        } else if level.has_debug_checks() && level.has_proof_checking() {
            Self::FullyVerified
        } else if level.has_debug_checks() {
            Self::DebugChecked
        } else if level.has_proof_checking() {
            Self::ProofChecked
        } else {
            Self::Trusted
        }
    }
}

/// clean-owned verification metadata retained from a ay solve call.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[must_use]
pub struct AySolveVerification {
    /// Solver-side verification counters for the solve call.
    pub summary: AyVerificationSummary,
    /// Runtime verification mode used for the solve call.
    pub level: AyVerificationLevel,
}

/// clean-owned mirror of ay's structured Unknown reasons.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[must_use]
#[non_exhaustive]
pub enum AyUnknownReason {
    Timeout,
    ResourceLimit,
    MemoryLimit,
    Interrupted,
    Incomplete,
    QuantifierRoundLimit,
    QuantifierDeferred,
    QuantifierUnhandled,
    QuantifierCegqiIncomplete,
    QuantifierEmatchingExistsIncomplete,
    SplitLimit,
    ExpressionSplit,
    Unsupported,
    InternalError,
    Unknown,
}

impl From<UnknownReason> for AyUnknownReason {
    fn from(reason: UnknownReason) -> Self {
        match reason {
            UnknownReason::Timeout => Self::Timeout,
            UnknownReason::ResourceLimit => Self::ResourceLimit,
            UnknownReason::MemoryLimit => Self::MemoryLimit,
            UnknownReason::Interrupted => Self::Interrupted,
            UnknownReason::Incomplete => Self::Incomplete,
            UnknownReason::QuantifierRoundLimit => Self::QuantifierRoundLimit,
            UnknownReason::QuantifierDeferred => Self::QuantifierDeferred,
            UnknownReason::QuantifierUnhandled => Self::QuantifierUnhandled,
            UnknownReason::QuantifierCegqiIncomplete => Self::QuantifierCegqiIncomplete,
            UnknownReason::QuantifierEmatchingExistsIncomplete => {
                Self::QuantifierEmatchingExistsIncomplete
            }
            UnknownReason::SplitLimit => Self::SplitLimit,
            UnknownReason::ExpressionSplit => Self::ExpressionSplit,
            UnknownReason::Unsupported => Self::Unsupported,
            UnknownReason::InternalError => Self::InternalError,
            UnknownReason::Unknown => Self::Unknown,
            _ => Self::Unknown,
        }
    }
}

impl AyUnknownReason {
    /// Returns `true` when the reason comes from quantifier-side incompleteness.
    pub fn is_quantifier(&self) -> bool {
        matches!(
            self,
            Self::QuantifierRoundLimit
                | Self::QuantifierDeferred
                | Self::QuantifierUnhandled
                | Self::QuantifierCegqiIncomplete
                | Self::QuantifierEmatchingExistsIncomplete
        )
    }
}

impl fmt::Display for AyUnknownReason {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Timeout => write!(f, "timeout"),
            Self::ResourceLimit => write!(f, "resourceout"),
            Self::MemoryLimit => write!(f, "memout"),
            Self::Interrupted => write!(f, "interrupted"),
            Self::Incomplete => write!(f, "incomplete"),
            Self::QuantifierRoundLimit => write!(f, "(incomplete quantifier-round-limit)"),
            Self::QuantifierDeferred => write!(f, "(incomplete quantifier-deferred)"),
            Self::QuantifierUnhandled => write!(f, "(incomplete quantifier-unhandled)"),
            Self::QuantifierCegqiIncomplete => write!(f, "(incomplete quantifier-cegqi)"),
            Self::QuantifierEmatchingExistsIncomplete => {
                write!(f, "(incomplete quantifier-ematching-exists)")
            }
            Self::SplitLimit => write!(f, "incomplete"),
            Self::ExpressionSplit => write!(f, "incomplete"),
            Self::Unsupported => write!(f, "unsupported"),
            Self::InternalError => write!(f, "internal-error"),
            Self::Unknown => write!(f, "unknown"),
        }
    }
}

/// clean-local summary of a ay `SmtProofCertificate` carried on `SolveResult::Unsat`.
///
/// The actual certificate (which wraps an LRAT SAT proof) is lazily materialized
/// inside ay and not retained by clean. We capture lightweight metadata so
/// downstream code can decide whether to request the full certificate via the
/// proof backend.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[must_use]
pub struct AyProofCertificateInfo {
    /// Whether the LRAT certificate covers all solver-derived clauses.
    pub is_complete: bool,
}

/// Primary satisfiability report preserving ay solve provenance.
#[derive(Debug, Clone)]
#[must_use]
#[non_exhaustive]
pub enum AySolveEnvelope {
    /// ay returned a consumer-accepted solve result and any structured unknown
    /// reason.
    Solved {
        result: AySolveResult,
        unknown_reason: Option<AyUnknownReason>,
        verification: AySolveVerification,
        /// Proof certificate metadata when the result is UNSAT.
        /// Present only when ay attached an `SmtProofCertificate` to the
        /// UNSAT result (always the case for ay >= #8019).
        proof_certificate: Option<AyProofCertificateInfo>,
    },
    /// clean caught a solver panic and degrades it to Unknown for compatibility.
    PanicUnknown { panic_reason: String },
}

impl AySolveEnvelope {
    /// Get the underlying SAT/UNSAT/UNKNOWN result.
    pub fn solve_result(&self) -> AySolveResult {
        match self {
            Self::Solved { result, .. } => *result,
            Self::PanicUnknown { .. } => AySolveResult::Unknown,
        }
    }

    /// Get the legacy clean tri-state compatibility view.
    pub fn kind(&self) -> AySolveResult {
        self.solve_result()
    }

    /// Returns true if the result is satisfiable.
    pub fn is_sat(&self) -> bool {
        self.solve_result().is_sat()
    }

    /// Returns true if the result is unsatisfiable.
    pub fn is_unsat(&self) -> bool {
        self.solve_result().is_unsat()
    }

    /// Returns true if the result is unknown.
    pub fn is_unknown(&self) -> bool {
        self.solve_result().is_unknown()
    }

    /// Whether ay validated the SAT model on this solve path.
    pub fn was_model_validated(&self) -> bool {
        match self {
            Self::Solved { verification, .. } => verification.summary.sat_model_validated,
            Self::PanicUnknown { .. } => false,
        }
    }

    /// Structured reason for Unknown, when ay provided one.
    pub fn unknown_reason(&self) -> Option<AyUnknownReason> {
        match self {
            Self::Solved { unknown_reason, .. } => *unknown_reason,
            Self::PanicUnknown { .. } => None,
        }
    }

    /// Panic payload captured from the solver, when clean downgraded a panic.
    pub fn panic_reason(&self) -> Option<&str> {
        match self {
            Self::PanicUnknown { panic_reason } => Some(panic_reason.as_str()),
            Self::Solved { .. } => None,
        }
    }

    /// Solver verification metadata preserved from the solve call.
    pub fn verification(&self) -> Option<AySolveVerification> {
        match self {
            Self::Solved { verification, .. } => Some(*verification),
            Self::PanicUnknown { .. } => None,
        }
    }

    /// Solver verification counters preserved from the solve call.
    pub fn verification_summary(&self) -> Option<AyVerificationSummary> {
        self.verification().map(|verification| verification.summary)
    }

    /// Runtime verification level preserved from the solve call.
    pub fn verification_level(&self) -> Option<AyVerificationLevel> {
        self.verification().map(|verification| verification.level)
    }

    /// Proof certificate metadata from the UNSAT result, when available.
    pub fn proof_certificate(&self) -> Option<AyProofCertificateInfo> {
        match self {
            Self::Solved {
                proof_certificate, ..
            } => *proof_certificate,
            Self::PanicUnknown { .. } => None,
        }
    }
}

impl From<&AySolveEnvelope> for AySolveResult {
    fn from(report: &AySolveEnvelope) -> Self {
        report.kind()
    }
}

impl PartialEq<AySolveResult> for AySolveEnvelope {
    fn eq(&self, other: &AySolveResult) -> bool {
        self.kind() == *other
    }
}

impl PartialEq<AySolveEnvelope> for AySolveResult {
    fn eq(&self, other: &AySolveEnvelope) -> bool {
        *self == other.kind()
    }
}

/// Derived compatibility view of a satisfiability check.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[must_use]
#[non_exhaustive]
pub enum AySolveResult {
    /// The constraints are satisfiable
    Sat,
    /// The constraints are unsatisfiable
    Unsat,
    /// The solver could not determine satisfiability
    Unknown,
}

impl AySolveResult {
    #[inline]
    pub fn is_sat(&self) -> bool {
        matches!(self, Self::Sat)
    }

    #[inline]
    pub fn is_unsat(&self) -> bool {
        matches!(self, Self::Unsat)
    }

    #[inline]
    pub fn is_unknown(&self) -> bool {
        matches!(self, Self::Unknown)
    }
}

impl From<SolveResult> for AySolveResult {
    fn from(r: SolveResult) -> Self {
        match r {
            SolveResult::Sat => AySolveResult::Sat,
            SolveResult::Unsat(_) => AySolveResult::Unsat,
            SolveResult::Unknown => AySolveResult::Unknown,
            _ => AySolveResult::Unknown,
        }
    }
}

impl From<&SolveResult> for AySolveResult {
    fn from(r: &SolveResult) -> Self {
        match r {
            SolveResult::Sat => AySolveResult::Sat,
            SolveResult::Unsat(_) => AySolveResult::Unsat,
            SolveResult::Unknown => AySolveResult::Unknown,
            _ => AySolveResult::Unknown,
        }
    }
}

impl From<VerifiedSolveResult> for AySolveResult {
    fn from(r: VerifiedSolveResult) -> Self {
        r.result().into()
    }
}
