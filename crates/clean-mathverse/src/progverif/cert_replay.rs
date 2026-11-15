// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Shared certificate replay trait and helpers for program verification importers.
//!
//! All 7 program verification tool importers (Dafny, Why3, PVS, ACL2, Nuprl,
//! LiquidHaskell, KeY/Frama-C/SPARK) share this common infrastructure for:
//! - Representing external proof certificates in various formats
//! - Dispatching certificate replay requests (Alethe and DRAT/LRAT are unavailable)
//! - Tracking axiom profiles through the replay pipeline

use hashbrown::HashMap;
use serde::{Deserialize, Serialize};

use crate::types::{AxiomProfile, TrustLevel};

// ---------------------------------------------------------------------------
// Errors
// ---------------------------------------------------------------------------

/// Errors arising from certificate replay operations.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum CertReplayError {
    /// The certificate data is malformed or could not be parsed.
    #[error("invalid certificate: {reason}")]
    InvalidCert { reason: String },

    /// The certificate format is not supported by this replay strategy.
    #[error("unsupported certificate format: {format}")]
    UnsupportedFormat { format: String },

    /// No statement-bound checker is implemented for this format.
    #[error("certificate replay unavailable for {format}: no statement-bound proof checker")]
    ReplayUnavailable { format: String },

    /// The certificate replay failed verification.
    #[error("certificate verification failed: {reason}")]
    VerificationFailed { reason: String },

    /// The replay operation exceeded the timeout budget.
    #[error("certificate replay timed out after {timeout_us}us")]
    ReplayTimeout { timeout_us: u64 },
}

// ---------------------------------------------------------------------------
// Certificate format and data
// ---------------------------------------------------------------------------

/// Format of an external proof certificate.
///
/// Proof certificates from different verification tools use different formats.
/// This enum identifies the format so the correct replay strategy can be
/// dispatched.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum CertificateFormat {
    /// SMT-LIB 2 proof format.
    SmtLib2,
    /// DRAT (Deletion Resolution Asymmetric Tautology) — SAT proof format.
    Drat,
    /// LRAT (Linear RAT) — verified SAT proof format.
    Lrat,
    /// Alethe-LF proof format (used by cvc5, veriT).
    AletheLF,
    /// LFSC proof format (legacy cvc4/5).
    Lfsc,
    /// Tool-specific custom certificate format.
    Custom(String),
}

impl CertificateFormat {
    /// Human-readable name for this format.
    #[must_use]
    pub fn name(&self) -> &str {
        match self {
            Self::SmtLib2 => "SMT-LIB2",
            Self::Drat => "DRAT",
            Self::Lrat => "LRAT",
            Self::AletheLF => "Alethe-LF",
            Self::Lfsc => "LFSC",
            Self::Custom(name) => name,
        }
    }
}

/// An external proof certificate produced by a verification tool.
///
/// Carries the raw certificate bytes together with provenance metadata.
/// The `source_tool` identifies which verification tool produced the
/// certificate (e.g. "z3", "cvc5", "drat-trim").
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Certificate {
    /// Certificate wire format.
    pub format: CertificateFormat,
    /// Raw certificate bytes (may be binary for DRAT/LRAT or text for SMT-LIB2).
    pub raw_bytes: Vec<u8>,
    /// Name of the tool that produced this certificate.
    pub source_tool: String,
    /// Arbitrary key-value metadata (solver version, flags, etc.).
    pub metadata: HashMap<String, String>,
}

impl Certificate {
    /// Create a new certificate with the given format and raw data.
    #[must_use]
    pub fn new(
        format: CertificateFormat,
        raw_bytes: Vec<u8>,
        source_tool: impl Into<String>,
    ) -> Self {
        Self {
            format,
            raw_bytes,
            source_tool: source_tool.into(),
            metadata: HashMap::new(),
        }
    }

    /// Builder: insert a metadata key-value pair.
    #[must_use]
    pub fn with_metadata(mut self, key: impl Into<String>, value: impl Into<String>) -> Self {
        self.metadata.insert(key.into(), value.into());
        self
    }

    /// Whether the certificate carries any raw data.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.raw_bytes.is_empty()
    }

    /// Size of the raw certificate in bytes.
    #[must_use]
    pub fn byte_len(&self) -> usize {
        self.raw_bytes.len()
    }
}

// ---------------------------------------------------------------------------
// Replay result
// ---------------------------------------------------------------------------

/// Result of replaying a proof certificate.
///
/// Contains the trust judgment (verified/unverified, axiom profile, trust level)
/// and diagnostic information from the replay process.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct CertReplayResult {
    /// Whether the certificate was successfully verified.
    pub verified: bool,
    /// Axiom profile accumulated during replay.
    pub axiom_profile: AxiomProfile,
    /// Trust level assigned by the replay strategy.
    pub trust_level: TrustLevel,
    /// Wall-clock replay time in microseconds.
    pub replay_time_us: u64,
    /// Diagnostic messages from the replay process.
    pub diagnostics: Vec<String>,
}

impl CertReplayResult {
    /// Create a result for a successful verification at the given trust level.
    #[must_use]
    pub fn verified(
        axiom_profile: AxiomProfile,
        trust_level: TrustLevel,
        replay_time_us: u64,
    ) -> Self {
        Self {
            verified: true,
            axiom_profile,
            trust_level,
            replay_time_us,
            diagnostics: Vec::new(),
        }
    }

    /// Create a result for a failed verification.
    #[must_use]
    pub fn failed(reason: impl Into<String>, replay_time_us: u64) -> Self {
        Self {
            verified: false,
            axiom_profile: AxiomProfile::NONE,
            trust_level: TrustLevel::TrustedOracle,
            replay_time_us,
            diagnostics: vec![reason.into()],
        }
    }
}

// ---------------------------------------------------------------------------
// Replay strategy trait
// ---------------------------------------------------------------------------

/// Strategy for replaying external proof certificates.
///
/// Each verification tool backend implements this trait to translate its
/// native certificates into clean trust-level judgments. Strategies must be
/// `Send + Sync` so they can be shared across importer threads.
pub trait CertReplayStrategy: Send + Sync {
    /// Human-readable name of this replay strategy.
    fn name(&self) -> &str;

    /// Certificate formats supported by this strategy.
    fn supported_formats(&self) -> &[CertificateFormat];

    /// Replay the given certificate, returning a trust-level judgment.
    ///
    /// # Errors
    ///
    /// Returns `CertReplayError` if the certificate is invalid, uses an
    /// unsupported format, or fails verification.
    fn replay(&self, cert: &Certificate) -> Result<CertReplayResult, CertReplayError>;
}

// ---------------------------------------------------------------------------
// Null replay strategy (trusted oracle fallback)
// ---------------------------------------------------------------------------

/// A no-op replay strategy that accepts all certificates as trusted oracles.
///
/// Used as a fallback when no certificate checker is available for a given
/// tool, or during development/testing. Always returns `TrustedOracle`
/// trust level with the `SMT_ORACLE` axiom bit.
#[derive(Clone, Debug, Default)]
pub struct NullReplayStrategy;

impl CertReplayStrategy for NullReplayStrategy {
    fn name(&self) -> &str {
        "null"
    }

    fn supported_formats(&self) -> &[CertificateFormat] {
        &[]
    }

    fn replay(&self, _cert: &Certificate) -> Result<CertReplayResult, CertReplayError> {
        Ok(CertReplayResult::verified(
            AxiomProfile::SMT_ORACLE,
            TrustLevel::TrustedOracle,
            0,
        ))
    }
}

// ---------------------------------------------------------------------------
// Unavailable replay backends
// ---------------------------------------------------------------------------

/// Alethe-LF replay entry, currently unavailable.
///
/// This API receives certificate bytes but no problem statement and has no
/// proof-step checker. It therefore advertises no supported formats and refuses
/// every replay request. A marker or an assumption is not checked evidence.
#[derive(Clone, Debug, Default)]
pub struct AletheLfReplayStrategy;

impl AletheLfReplayStrategy {
    /// Create an entry that reports Alethe-LF replay as unavailable.
    #[must_use]
    pub fn new() -> Self {
        Self
    }
}

impl CertReplayStrategy for AletheLfReplayStrategy {
    fn name(&self) -> &str {
        "alethe-lf"
    }

    fn supported_formats(&self) -> &[CertificateFormat] {
        &[]
    }

    fn replay(&self, cert: &Certificate) -> Result<CertReplayResult, CertReplayError> {
        if cert.format != CertificateFormat::AletheLF {
            return Err(CertReplayError::UnsupportedFormat {
                format: cert.format.name().to_string(),
            });
        }
        Err(CertReplayError::ReplayUnavailable {
            format: cert.format.name().to_string(),
        })
    }
}

/// DRAT/LRAT replay entry, currently unavailable.
///
/// Certificate bytes alone do not bind a SAT problem, and this backend has no
/// proof-step checker. It advertises no supported formats and refuses every
/// replay request; clause counts and byte thresholds establish no proof.
#[derive(Clone, Debug, Default)]
pub struct DratReplayStrategy;

impl DratReplayStrategy {
    /// Create an entry that reports DRAT/LRAT replay as unavailable.
    #[must_use]
    pub fn new() -> Self {
        Self
    }
}

impl CertReplayStrategy for DratReplayStrategy {
    fn name(&self) -> &str {
        "drat-lrat"
    }

    fn supported_formats(&self) -> &[CertificateFormat] {
        &[]
    }

    fn replay(&self, cert: &Certificate) -> Result<CertReplayResult, CertReplayError> {
        if cert.format != CertificateFormat::Drat && cert.format != CertificateFormat::Lrat {
            return Err(CertReplayError::UnsupportedFormat {
                format: cert.format.name().to_string(),
            });
        }
        Err(CertReplayError::ReplayUnavailable {
            format: cert.format.name().to_string(),
        })
    }
}

#[cfg(test)]
#[path = "cert_replay_refusal_tests.rs"]
mod refusal_tests;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_certificate_new_creates_empty_metadata() {
        let cert = Certificate::new(CertificateFormat::SmtLib2, vec![1, 2, 3], "z3");
        assert_eq!(cert.format, CertificateFormat::SmtLib2);
        assert_eq!(cert.raw_bytes, vec![1, 2, 3]);
        assert_eq!(cert.source_tool, "z3");
        assert!(cert.metadata.is_empty());
        assert!(!cert.is_empty());
        assert_eq!(cert.byte_len(), 3);
    }

    #[test]
    fn test_certificate_with_metadata_builder() {
        let cert = Certificate::new(CertificateFormat::Drat, vec![], "drat-trim")
            .with_metadata("version", "2.0")
            .with_metadata("solver", "cadical");
        assert_eq!(
            cert.metadata.get("version").map(String::as_str),
            Some("2.0")
        );
        assert_eq!(
            cert.metadata.get("solver").map(String::as_str),
            Some("cadical")
        );
        assert!(cert.is_empty());
    }

    #[test]
    fn test_certificate_format_name() {
        assert_eq!(CertificateFormat::SmtLib2.name(), "SMT-LIB2");
        assert_eq!(CertificateFormat::Drat.name(), "DRAT");
        assert_eq!(CertificateFormat::Lrat.name(), "LRAT");
        assert_eq!(CertificateFormat::AletheLF.name(), "Alethe-LF");
        assert_eq!(CertificateFormat::Lfsc.name(), "LFSC");
        assert_eq!(
            CertificateFormat::Custom("boogie-cert".into()).name(),
            "boogie-cert"
        );
    }

    #[test]
    fn test_null_replay_strategy_returns_trusted_oracle() {
        let strategy = NullReplayStrategy;
        assert_eq!(strategy.name(), "null");
        assert!(strategy.supported_formats().is_empty());

        let cert = Certificate::new(CertificateFormat::SmtLib2, b"(proof ...)".to_vec(), "z3");
        let result = strategy
            .replay(&cert)
            .expect("null strategy should always succeed");
        assert!(result.verified);
        assert_eq!(result.trust_level, TrustLevel::TrustedOracle);
        assert!(result.axiom_profile.contains(AxiomProfile::SMT_ORACLE));
        assert_eq!(result.replay_time_us, 0);
        assert!(result.diagnostics.is_empty());
    }

    #[test]
    fn test_cert_replay_result_verified_constructor() {
        let result =
            CertReplayResult::verified(AxiomProfile::SAT_CERT, TrustLevel::CertificateReplayed, 42);
        assert!(result.verified);
        assert!(result.axiom_profile.contains(AxiomProfile::SAT_CERT));
        assert_eq!(result.trust_level, TrustLevel::CertificateReplayed);
        assert_eq!(result.replay_time_us, 42);
        assert!(result.diagnostics.is_empty());
    }

    #[test]
    fn test_cert_replay_result_failed_constructor() {
        let result = CertReplayResult::failed("bad proof step at index 7", 100);
        assert!(!result.verified);
        assert_eq!(result.trust_level, TrustLevel::TrustedOracle);
        assert_eq!(result.replay_time_us, 100);
        assert_eq!(result.diagnostics, vec!["bad proof step at index 7"]);
    }

    #[test]
    fn test_certificate_serde_round_trip() {
        let cert = Certificate::new(
            CertificateFormat::Custom("alethe".into()),
            b"(step t1 ...)\n".to_vec(),
            "cvc5",
        )
        .with_metadata("logic", "QF_LIA");

        let json = serde_json::to_string(&cert).expect("serialize certificate");
        let restored: Certificate = serde_json::from_str(&json).expect("deserialize certificate");
        assert_eq!(restored.format, cert.format);
        assert_eq!(restored.raw_bytes, cert.raw_bytes);
        assert_eq!(restored.source_tool, cert.source_tool);
        assert_eq!(
            restored.metadata.get("logic").map(String::as_str),
            Some("QF_LIA")
        );
    }
}
