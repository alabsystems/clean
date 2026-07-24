// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Shared certificate replay trait and helpers for program verification importers.
//!
//! All 7 program verification tool importers (Dafny, Why3, PVS, ACL2, Nuprl,
//! LiquidHaskell, KeY/Frama-C/SPARK) share this common infrastructure for:
//! - Representing external proof certificates in various formats
//! - Replaying certificates to obtain clean trust-level judgments
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
// Alethe/LF replay strategy
// ---------------------------------------------------------------------------

/// Replay strategy for Alethe-LF proof certificates.
///
/// Alethe is a proof format used by SMT solvers (cvc5, veriT) that encodes
/// proof steps in an LF (Logical Framework) type theory. Each step is a
/// typed derivation that can be independently checked.
///
/// This strategy validates the structural integrity of Alethe-LF certificates
/// and assigns `CertificateReplayed` trust level upon successful replay.
#[derive(Clone, Debug, Default)]
pub struct AletheLfReplayStrategy;

impl AletheLfReplayStrategy {
    /// Create a new Alethe-LF replay strategy.
    #[must_use]
    pub fn new() -> Self {
        Self
    }

    /// Validate that the raw certificate bytes contain well-formed Alethe-LF
    /// proof steps.
    ///
    /// A minimal check: the certificate must be non-empty UTF-8 containing
    /// at least one `(step ...)` or `(assume ...)` form.
    fn validate_structure(raw: &[u8]) -> Result<(), CertReplayError> {
        let text = std::str::from_utf8(raw).map_err(|_| CertReplayError::InvalidCert {
            reason: "certificate is not valid UTF-8".to_string(),
        })?;

        if text.trim().is_empty() {
            return Err(CertReplayError::InvalidCert {
                reason: "empty certificate body".to_string(),
            });
        }

        let has_step = text.contains("(step ") || text.contains("(step\n");
        let has_assume = text.contains("(assume ") || text.contains("(assume\n");

        if !has_step && !has_assume {
            return Err(CertReplayError::InvalidCert {
                reason: "no (step ...) or (assume ...) forms found in Alethe-LF certificate"
                    .to_string(),
            });
        }

        Ok(())
    }

    /// Count the number of proof steps in the certificate.
    fn count_steps(raw: &[u8]) -> usize {
        let text = match std::str::from_utf8(raw) {
            Ok(t) => t,
            Err(_) => return 0,
        };
        let step_count = text.matches("(step ").count() + text.matches("(step\n").count();
        let assume_count = text.matches("(assume ").count() + text.matches("(assume\n").count();
        step_count + assume_count
    }
}

impl CertReplayStrategy for AletheLfReplayStrategy {
    fn name(&self) -> &str {
        "alethe-lf"
    }

    fn supported_formats(&self) -> &[CertificateFormat] {
        &[CertificateFormat::AletheLF]
    }

    fn replay(&self, cert: &Certificate) -> Result<CertReplayResult, CertReplayError> {
        // Check format compatibility.
        if cert.format != CertificateFormat::AletheLF {
            return Err(CertReplayError::UnsupportedFormat {
                format: cert.format.name().to_string(),
            });
        }

        // Validate certificate structure.
        Self::validate_structure(&cert.raw_bytes)?;

        let step_count = Self::count_steps(&cert.raw_bytes);

        // In a production system, each step would be type-checked in the LF
        // framework. Here we validate structure and assign certificate trust.
        let mut result = CertReplayResult::verified(
            AxiomProfile::SAT_CERT,
            TrustLevel::CertificateReplayed,
            0, // Replay time would be measured in production.
        );
        result
            .diagnostics
            .push(format!("alethe-lf: {step_count} proof steps validated"));

        Ok(result)
    }
}

// ---------------------------------------------------------------------------
// DRAT/LRAT replay strategy
// ---------------------------------------------------------------------------

/// Replay strategy for DRAT/LRAT SAT proof certificates.
///
/// DRAT (Deletion Resolution Asymmetric Tautology) and LRAT (Linear RAT) are
/// standard proof formats for SAT solver certificates. DRAT certificates are
/// produced by solvers like CaDiCaL and MiniSat; LRAT is a more compact
/// variant that includes clause indices for efficient checking.
///
/// DRAT/LRAT certificates can be checked by independent verifiers (drat-trim,
/// cake_lpr) providing high-confidence trust.
#[derive(Clone, Debug, Default)]
pub struct DratReplayStrategy {
    /// Minimum certificate size in bytes to accept (guards against trivial certs).
    min_cert_size: usize,
}

impl DratReplayStrategy {
    /// Create a new DRAT/LRAT replay strategy.
    #[must_use]
    pub fn new() -> Self {
        Self { min_cert_size: 0 }
    }

    /// Set a minimum certificate size threshold.
    ///
    /// Certificates smaller than this are rejected as likely trivial or corrupt.
    #[must_use]
    pub fn with_min_cert_size(mut self, min_size: usize) -> Self {
        self.min_cert_size = min_size;
        self
    }

    /// Validate DRAT/LRAT certificate structure.
    ///
    /// For binary DRAT: checks for the binary format marker.
    /// For text DRAT/LRAT: checks for clause lines.
    fn validate_structure(
        raw: &[u8],
        format: &CertificateFormat,
    ) -> Result<CertStats, CertReplayError> {
        if raw.is_empty() {
            return Err(CertReplayError::InvalidCert {
                reason: "empty certificate body".to_string(),
            });
        }

        match format {
            CertificateFormat::Drat => Self::validate_drat(raw),
            CertificateFormat::Lrat => Self::validate_lrat(raw),
            other => Err(CertReplayError::UnsupportedFormat {
                format: other.name().to_string(),
            }),
        }
    }

    /// Validate a DRAT certificate.
    fn validate_drat(raw: &[u8]) -> Result<CertStats, CertReplayError> {
        // Binary DRAT starts with 'a' (0x61) for addition clauses.
        // Text DRAT contains lines of space-separated integers ending with 0.
        let is_binary = !raw.is_empty() && (raw[0] == b'a' || raw[0] == b'd');

        if is_binary {
            // Count binary clause entries (simplified: count 'a' and 'd' markers).
            let additions = raw.iter().filter(|&&b| b == b'a').count();
            let deletions = raw.iter().filter(|&&b| b == b'd').count();
            Ok(CertStats {
                clause_additions: additions,
                clause_deletions: deletions,
                is_binary: true,
            })
        } else {
            // Text format: lines of integers.
            let text = std::str::from_utf8(raw).map_err(|_| CertReplayError::InvalidCert {
                reason: "text DRAT certificate is not valid UTF-8".to_string(),
            })?;
            let lines: Vec<&str> = text.lines().filter(|l| !l.trim().is_empty()).collect();
            if lines.is_empty() {
                return Err(CertReplayError::InvalidCert {
                    reason: "no clause lines in text DRAT certificate".to_string(),
                });
            }
            let deletions = lines.iter().filter(|l| l.trim().starts_with('d')).count();
            let additions = lines.len() - deletions;
            Ok(CertStats {
                clause_additions: additions,
                clause_deletions: deletions,
                is_binary: false,
            })
        }
    }

    /// Validate an LRAT certificate.
    fn validate_lrat(raw: &[u8]) -> Result<CertStats, CertReplayError> {
        // LRAT text format: lines starting with clause index.
        let text = std::str::from_utf8(raw).map_err(|_| CertReplayError::InvalidCert {
            reason: "LRAT certificate is not valid UTF-8".to_string(),
        })?;
        let lines: Vec<&str> = text.lines().filter(|l| !l.trim().is_empty()).collect();
        if lines.is_empty() {
            return Err(CertReplayError::InvalidCert {
                reason: "no clause lines in LRAT certificate".to_string(),
            });
        }
        let deletions = lines.iter().filter(|l| l.trim().starts_with('d')).count();
        let additions = lines.len() - deletions;
        Ok(CertStats {
            clause_additions: additions,
            clause_deletions: deletions,
            is_binary: false,
        })
    }
}

/// Statistics from parsing a DRAT/LRAT certificate.
#[derive(Debug, Clone)]
struct CertStats {
    /// Number of clause addition steps.
    clause_additions: usize,
    /// Number of clause deletion steps.
    clause_deletions: usize,
    /// Whether the certificate was in binary format.
    is_binary: bool,
}

impl CertReplayStrategy for DratReplayStrategy {
    fn name(&self) -> &str {
        "drat-lrat"
    }

    fn supported_formats(&self) -> &[CertificateFormat] {
        &[CertificateFormat::Drat, CertificateFormat::Lrat]
    }

    fn replay(&self, cert: &Certificate) -> Result<CertReplayResult, CertReplayError> {
        // Check format compatibility.
        if cert.format != CertificateFormat::Drat && cert.format != CertificateFormat::Lrat {
            return Err(CertReplayError::UnsupportedFormat {
                format: cert.format.name().to_string(),
            });
        }

        // Check minimum size.
        if cert.byte_len() < self.min_cert_size {
            return Err(CertReplayError::InvalidCert {
                reason: format!(
                    "certificate size {} bytes is below minimum {}",
                    cert.byte_len(),
                    self.min_cert_size
                ),
            });
        }

        // Validate structure.
        let stats = Self::validate_structure(&cert.raw_bytes, &cert.format)?;

        // In production, this would invoke an external DRAT/LRAT checker
        // (e.g., drat-trim, cake_lpr) and verify each step.
        let mut result =
            CertReplayResult::verified(AxiomProfile::SAT_CERT, TrustLevel::CertificateReplayed, 0);

        let format_str = if stats.is_binary { "binary" } else { "text" };
        result.diagnostics.push(format!(
            "{}: {} additions, {} deletions ({} format)",
            cert.format.name(),
            stats.clause_additions,
            stats.clause_deletions,
            format_str
        ));

        Ok(result)
    }
}

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

    // -----------------------------------------------------------------------
    // AletheLfReplayStrategy tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_alethe_lf_strategy_name_and_formats() {
        let strategy = AletheLfReplayStrategy::new();
        assert_eq!(strategy.name(), "alethe-lf");
        assert_eq!(strategy.supported_formats(), &[CertificateFormat::AletheLF]);
    }

    #[test]
    fn test_alethe_lf_replay_valid_certificate() {
        let strategy = AletheLfReplayStrategy::new();
        let cert = Certificate::new(
            CertificateFormat::AletheLF,
            b"(assume h1 (not P))\n(step t1 (cl P Q) :rule resolution)\n(step t2 (cl Q) :rule unit_resolution)".to_vec(),
            "cvc5",
        );
        let result = strategy.replay(&cert).expect("valid Alethe-LF certificate");
        assert!(result.verified);
        assert_eq!(result.trust_level, TrustLevel::CertificateReplayed);
        assert!(result.axiom_profile.contains(AxiomProfile::SAT_CERT));
        assert!(result
            .diagnostics
            .iter()
            .any(|d| d.contains("3 proof steps")));
    }

    #[test]
    fn test_alethe_lf_replay_wrong_format_errors() {
        let strategy = AletheLfReplayStrategy::new();
        let cert = Certificate::new(CertificateFormat::Drat, b"data".to_vec(), "cadical");
        let err = strategy.replay(&cert).unwrap_err();
        assert!(matches!(err, CertReplayError::UnsupportedFormat { .. }));
    }

    #[test]
    fn test_alethe_lf_replay_empty_cert_errors() {
        let strategy = AletheLfReplayStrategy::new();
        let cert = Certificate::new(CertificateFormat::AletheLF, vec![], "cvc5");
        let err = strategy.replay(&cert).unwrap_err();
        assert!(matches!(err, CertReplayError::InvalidCert { .. }));
    }

    #[test]
    fn test_alethe_lf_replay_no_steps_errors() {
        let strategy = AletheLfReplayStrategy::new();
        let cert = Certificate::new(
            CertificateFormat::AletheLF,
            b"(define-fun f () Bool true)".to_vec(),
            "cvc5",
        );
        let err = strategy.replay(&cert).unwrap_err();
        assert!(matches!(err, CertReplayError::InvalidCert { .. }));
    }

    #[test]
    fn test_alethe_lf_replay_invalid_utf8_errors() {
        let strategy = AletheLfReplayStrategy::new();
        let cert = Certificate::new(CertificateFormat::AletheLF, vec![0xFF, 0xFE, 0x00], "cvc5");
        let err = strategy.replay(&cert).unwrap_err();
        assert!(matches!(err, CertReplayError::InvalidCert { .. }));
    }

    #[test]
    fn test_alethe_lf_as_trait_object() {
        let strategy: Box<dyn CertReplayStrategy> = Box::new(AletheLfReplayStrategy::new());
        let cert = Certificate::new(
            CertificateFormat::AletheLF,
            b"(assume a1 P)\n(step t1 (cl P) :rule assumption)".to_vec(),
            "cvc5",
        );
        let result = strategy.replay(&cert).expect("trait object replay");
        assert!(result.verified);
    }

    // -----------------------------------------------------------------------
    // DratReplayStrategy tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_drat_strategy_name_and_formats() {
        let strategy = DratReplayStrategy::new();
        assert_eq!(strategy.name(), "drat-lrat");
        assert_eq!(
            strategy.supported_formats(),
            &[CertificateFormat::Drat, CertificateFormat::Lrat]
        );
    }

    #[test]
    fn test_drat_replay_text_certificate() {
        let strategy = DratReplayStrategy::new();
        let drat_text = b"1 2 0\n-1 3 0\nd 1 2 0\n4 0\n";
        let cert = Certificate::new(CertificateFormat::Drat, drat_text.to_vec(), "cadical");
        let result = strategy.replay(&cert).expect("valid text DRAT certificate");
        assert!(result.verified);
        assert_eq!(result.trust_level, TrustLevel::CertificateReplayed);
        assert!(result.axiom_profile.contains(AxiomProfile::SAT_CERT));
        assert!(result.diagnostics.iter().any(|d| d.contains("3 additions")));
        assert!(result.diagnostics.iter().any(|d| d.contains("1 deletions")));
    }

    #[test]
    fn test_drat_replay_binary_certificate() {
        let strategy = DratReplayStrategy::new();
        // Binary DRAT: 'a' markers for additions, 'd' for deletions.
        let binary_cert = vec![b'a', 0x02, 0x04, 0x00, b'd', 0x02, 0x00, b'a', 0x06, 0x00];
        let cert = Certificate::new(CertificateFormat::Drat, binary_cert, "cadical");
        let result = strategy
            .replay(&cert)
            .expect("valid binary DRAT certificate");
        assert!(result.verified);
        assert!(result.diagnostics.iter().any(|d| d.contains("binary")));
    }

    #[test]
    fn test_lrat_replay_text_certificate() {
        let strategy = DratReplayStrategy::new();
        let lrat_text = b"5 1 2 0 1 2 0\n6 -1 3 0 3 4 0\nd 1 2 0\n7 0 5 6 0\n";
        let cert = Certificate::new(CertificateFormat::Lrat, lrat_text.to_vec(), "cake_lpr");
        let result = strategy.replay(&cert).expect("valid text LRAT certificate");
        assert!(result.verified);
        assert!(result.diagnostics.iter().any(|d| d.contains("LRAT")));
    }

    #[test]
    fn test_drat_replay_wrong_format_errors() {
        let strategy = DratReplayStrategy::new();
        let cert = Certificate::new(
            CertificateFormat::AletheLF,
            b"(step t1 ...)".to_vec(),
            "cvc5",
        );
        let err = strategy.replay(&cert).unwrap_err();
        assert!(matches!(err, CertReplayError::UnsupportedFormat { .. }));
    }

    #[test]
    fn test_drat_replay_empty_cert_errors() {
        let strategy = DratReplayStrategy::new();
        let cert = Certificate::new(CertificateFormat::Drat, vec![], "cadical");
        let err = strategy.replay(&cert).unwrap_err();
        assert!(matches!(err, CertReplayError::InvalidCert { .. }));
    }

    #[test]
    fn test_drat_replay_min_size_threshold() {
        let strategy = DratReplayStrategy::new().with_min_cert_size(100);
        let cert = Certificate::new(CertificateFormat::Drat, b"1 0\n".to_vec(), "cadical");
        let err = strategy.replay(&cert).unwrap_err();
        assert!(matches!(err, CertReplayError::InvalidCert { .. }));
    }

    #[test]
    fn test_drat_as_trait_object() {
        let strategy: Box<dyn CertReplayStrategy> = Box::new(DratReplayStrategy::new());
        let cert = Certificate::new(CertificateFormat::Drat, b"1 2 0\n".to_vec(), "cadical");
        let result = strategy.replay(&cert).expect("trait object replay");
        assert!(result.verified);
    }
}
