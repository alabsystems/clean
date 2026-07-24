// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Error types for external certificate verification.

use std::fmt;

/// Error returned when verification of an external proof certificate fails.
///
/// External certificates (Farkas lemma proofs, entailment proofs) are generated
/// by external tools and must be verified before being trusted. This error
/// indicates what went wrong during verification.
#[derive(Debug, Clone)]
pub struct ExternalCertError {
    /// The category of verification failure.
    pub code: ExternalCertErrorCode,
    /// Human-readable details about the failure.
    pub detail: String,
}

impl ExternalCertError {
    pub fn invalid_schema(detail: String) -> Self {
        ExternalCertError {
            code: ExternalCertErrorCode::InvalidSchema,
            detail,
        }
    }

    pub fn multiplier_negative(detail: String) -> Self {
        ExternalCertError {
            code: ExternalCertErrorCode::MultiplierNegative,
            detail,
        }
    }

    pub fn no_contradiction(detail: String) -> Self {
        ExternalCertError {
            code: ExternalCertErrorCode::NoContradiction,
            detail,
        }
    }

    pub fn entailment_failed(detail: String) -> Self {
        ExternalCertError {
            code: ExternalCertErrorCode::EntailmentFailed,
            detail,
        }
    }

    pub fn length_mismatch(detail: String) -> Self {
        ExternalCertError {
            code: ExternalCertErrorCode::LengthMismatch,
            detail,
        }
    }

    pub fn unsupported_constraint_kind(detail: String) -> Self {
        ExternalCertError {
            code: ExternalCertErrorCode::UnsupportedConstraintKind,
            detail,
        }
    }

    pub fn rational_overflow() -> Self {
        ExternalCertError {
            code: ExternalCertErrorCode::RationalOverflow,
            detail: "rational arithmetic overflow".to_string(),
        }
    }

    pub fn proof_verification_failed(detail: String) -> Self {
        ExternalCertError {
            code: ExternalCertErrorCode::ProofVerificationFailed,
            detail,
        }
    }

    pub fn verifier_not_available(detail: String) -> Self {
        ExternalCertError {
            code: ExternalCertErrorCode::VerifierNotAvailable,
            detail,
        }
    }
}

impl fmt::Display for ExternalCertError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}: {}", self.code.as_str(), self.detail)
    }
}

impl std::error::Error for ExternalCertError {}

/// Categories of external certificate verification failures.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum ExternalCertErrorCode {
    /// Certificate structure does not match the expected schema.
    InvalidSchema,
    /// A Farkas multiplier was negative when it should be non-negative.
    MultiplierNegative,
    /// Linear combination did not produce a contradiction (for infeasibility proofs).
    NoContradiction,
    /// Entailment certificate failed to establish the claimed implication.
    EntailmentFailed,
    /// Rational arithmetic overflowed during verification.
    RationalOverflow,
    /// Number of constraints or variables does not match certificate dimensions.
    LengthMismatch,
    /// Constraint kind is not supported by the verifier.
    UnsupportedConstraintKind,
    /// Alethe proof verification failed (Carcara rejected the proof).
    ProofVerificationFailed,
    /// Required proof verifier (e.g. Carcara) is not available.
    VerifierNotAvailable,
}

impl ExternalCertErrorCode {
    pub fn as_str(self) -> &'static str {
        match self {
            ExternalCertErrorCode::InvalidSchema => "invalid_schema",
            ExternalCertErrorCode::MultiplierNegative => "multiplier_negative",
            ExternalCertErrorCode::NoContradiction => "no_contradiction",
            ExternalCertErrorCode::EntailmentFailed => "entailment_failed",
            ExternalCertErrorCode::RationalOverflow => "rational_overflow",
            ExternalCertErrorCode::LengthMismatch => "length_mismatch",
            ExternalCertErrorCode::UnsupportedConstraintKind => "unsupported_constraint_kind",
            ExternalCertErrorCode::ProofVerificationFailed => "proof_verification_failed",
            ExternalCertErrorCode::VerifierNotAvailable => "verifier_not_available",
        }
    }
}
