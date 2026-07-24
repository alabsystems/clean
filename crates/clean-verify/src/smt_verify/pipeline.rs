// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! SMT proof verification pipeline with format auto-detection.
//!
//! Mirrors the SAT pipeline pattern ([`crate::sat_verify::pipeline`]) for SMT
//! proofs: a single entry point that auto-detects the proof format (Alethe
//! text, SMT-LIB2), verifies, and returns a result with valid/holey/invalid
//! classification per SMT-COMP rules.
//!
//! ## Entry Points
//!
//! - [`verify_smt_proof_bytes`] — Auto-detect format and verify raw proof bytes.
//! - [`verify_smt_competition_entry`] — Competition wrapper returning
//!   [`SmtCompetitionResult`] with SMT-COMP verdict formatting.
//! - [`format_competition_output`] — Format a result as SMT-COMP stdout lines.
//!
//! ## SMT-COMP Classification
//!
//! SMT-COMP 2026 requires proof checkers to classify proofs:
//! - **valid**: every step kernel-verified or axiomatic; no structural holes.
//! - **holey**: structurally accepted steps exist, but no blindly trusted steps.
//! - **invalid**: at least one blindly trusted step, or proof does not derive
//!   the empty clause.
//! - **unknown**: checker could not determine validity (parse error, timeout).
//!
//! The classification maps directly to [`SmtVerifyStats::competition_verdict`]
//! from the trust module.
//!
//! ## Architecture
//!
//! ```text
//! verify_smt_proof_bytes(proof_bytes)
//!   ├─→ detect_smt_format(proof_bytes)
//!   ├─→ parse (Alethe or SMT-LIB2)
//!   ├─→ convert to SmtProofDag
//!   ├─→ verify_smt_proof(dag, mode)
//!   └─→ SmtPipelineResult { format, verdict, stats, timing }
//! ```
//!
//! ## References
//!
//! - SMT-COMP proof track: <https://smt-comp.github.io/>
//! - Alethe spec: <https://verit.loria.fr/documentation/alethe-spec.pdf>
//! - SMT-LIB 2.7: <https://smtlib.cs.uiowa.edu/papers/smt-lib-reference-v2.7-r2024-09-16.pdf>

use std::fmt;
use std::time::Instant;

use thiserror::Error;

use super::certificate::{self, SmtCertificate};
use super::smtlib2_proof;
use super::trust::SmtVerifyStats;
use super::{verify_alethe_proof_with_mode, verify_smt_proof, AletheVerifyError, VerifyMode};

// ---------------------------------------------------------------------------
// Types
// ---------------------------------------------------------------------------

/// Detected SMT proof format.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum SmtProofFormat {
    /// Alethe proof format (S-expression text).
    AletheText,
    /// SMT-LIB2 proof format (Z3-style `(proof ...)` blocks).
    SmtLib2,
    /// Unknown / unrecognised format.
    Unknown,
}

impl fmt::Display for SmtProofFormat {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SmtProofFormat::AletheText => write!(f, "Alethe"),
            SmtProofFormat::SmtLib2 => write!(f, "SMT-LIB2"),
            SmtProofFormat::Unknown => write!(f, "Unknown"),
        }
    }
}

/// SMT-COMP competition verdict.
///
/// Matches the four outcomes expected by SMT-COMP proof track judges.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum SmtCompVerdict {
    /// Every step was kernel-verified or axiomatic.
    Valid,
    /// Structurally accepted steps exist but no blindly trusted steps.
    Holey,
    /// Proof has trusted steps or does not derive the empty clause.
    Invalid,
    /// Checker could not determine validity (parse error, timeout, etc.).
    Unknown,
}

impl fmt::Display for SmtCompVerdict {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SmtCompVerdict::Valid => write!(f, "valid"),
            SmtCompVerdict::Holey => write!(f, "holey"),
            SmtCompVerdict::Invalid => write!(f, "invalid"),
            SmtCompVerdict::Unknown => write!(f, "unknown"),
        }
    }
}

/// Pipeline configuration for SMT proof verification.
#[derive(Debug, Clone)]
pub struct SmtPipelineConfig {
    /// Verification mode: strict rejects any trusted steps.
    pub mode: VerifyMode,
    /// If set, skip auto-detection and use this format.
    pub format_hint: Option<SmtProofFormat>,
    /// Generate an [`SmtCertificate`] on successful verification.
    pub generate_certificate: bool,
}

impl Default for SmtPipelineConfig {
    fn default() -> Self {
        Self {
            mode: VerifyMode::Permissive,
            format_hint: None,
            generate_certificate: false,
        }
    }
}

/// Result from the SMT proof verification pipeline.
#[derive(Debug, Clone)]
pub struct SmtPipelineResult {
    /// The detected proof format.
    pub format: SmtProofFormat,
    /// Whether the proof is a valid refutation (derives empty clause).
    pub valid: bool,
    /// SMT-COMP competition verdict.
    pub verdict: SmtCompVerdict,
    /// Verification statistics (step counts, trust breakdown).
    pub stats: SmtVerifyStats,
    /// Wall-clock verification time in microseconds.
    pub verification_time_us: u64,
    /// Number of structurally accepted holes.
    pub holes: u32,
    /// Certificate, if generation was requested and verification succeeded.
    pub certificate: Option<SmtCertificate>,
    /// Diagnostic messages (non-fatal warnings).
    pub diagnostics: Vec<String>,
}

/// Result wrapper for SMT-COMP competition output.
#[derive(Debug, Clone)]
pub struct SmtCompetitionResult {
    /// The SMT-COMP verdict line.
    pub verdict: SmtCompVerdict,
    /// Number of structurally accepted holes.
    pub holes: u32,
    /// Total verified steps.
    pub steps_verified: u32,
    /// Total trusted steps.
    pub steps_trusted: u32,
    /// Wall-clock verification time in microseconds.
    pub verification_time_us: u64,
    /// Error message, if verdict is Unknown.
    pub error: Option<String>,
}

/// Errors from the SMT pipeline.
#[derive(Debug, Error)]
#[non_exhaustive]
pub enum SmtPipelineError {
    /// Empty proof data.
    #[error("proof data is empty")]
    EmptyProof,

    /// Proof data is not valid UTF-8.
    #[error("proof is not valid UTF-8: {0}")]
    InvalidUtf8(String),

    /// Could not detect the proof format.
    #[error("unable to detect SMT proof format")]
    UnknownFormat,

    /// Alethe parse or verification error.
    #[error("Alethe error: {0}")]
    Alethe(#[from] AletheVerifyError),

    /// SMT-LIB2 parse error.
    #[error("SMT-LIB2 error: {0}")]
    SmtLib2(String),
}

// ---------------------------------------------------------------------------
// Format detection
// ---------------------------------------------------------------------------

/// Detect the SMT proof format from raw bytes.
///
/// Checks (in order):
/// 1. SMT-LIB2: uses `looks_like_smtlib2_proof` heuristic (has `(proof ...)`
///    block or `declare-fun`+`assert` preamble with proof rules).
/// 2. Alethe: starts with `(` (S-expression format) or contains `set-logic`
///    / `set-info` near the start.
/// 3. Unknown: nothing matched.
#[must_use]
pub fn detect_smt_format(data: &[u8]) -> SmtProofFormat {
    if data.is_empty() {
        return SmtProofFormat::Unknown;
    }

    // SMT-LIB2 check first (more specific than Alethe).
    if smtlib2_proof::looks_like_smtlib2_proof(data) {
        return SmtProofFormat::SmtLib2;
    }

    // Find first non-whitespace byte.
    let first_nonws = data.iter().position(|b| !b.is_ascii_whitespace());
    let Some(start) = first_nonws else {
        return SmtProofFormat::Unknown;
    };

    // Alethe: starts with `(`.
    if data[start] == b'(' {
        return SmtProofFormat::AletheText;
    }

    // Check text window for SMT-LIB keywords.
    let search_end = data.len().min(start + 256);
    if let Ok(window) = std::str::from_utf8(&data[start..search_end]) {
        if window.contains("set-logic")
            || window.contains("set-info")
            || window.contains("declare-const")
            || window.contains("assume")
        {
            return SmtProofFormat::AletheText;
        }
    }

    SmtProofFormat::Unknown
}

// ---------------------------------------------------------------------------
// Pipeline entry points
// ---------------------------------------------------------------------------

/// Verify an SMT proof from raw bytes with auto-detection.
///
/// This is the primary entry point for the SMT pipeline:
/// 1. Detects the proof format (or uses the configured hint).
/// 2. Parses the proof text.
/// 3. Runs the full SMT verification pipeline.
/// 4. Classifies the result as valid/holey/invalid per SMT-COMP rules.
///
/// # Errors
///
/// Returns [`SmtPipelineError`] if the proof cannot be parsed or verified.
pub fn verify_smt_proof_bytes(
    proof_bytes: &[u8],
    config: &SmtPipelineConfig,
) -> Result<SmtPipelineResult, SmtPipelineError> {
    if proof_bytes.is_empty() {
        return Err(SmtPipelineError::EmptyProof);
    }

    let format = config
        .format_hint
        .unwrap_or_else(|| detect_smt_format(proof_bytes));

    match format {
        SmtProofFormat::AletheText => verify_alethe_bytes(proof_bytes, config),
        SmtProofFormat::SmtLib2 => verify_smtlib2_bytes(proof_bytes, config),
        SmtProofFormat::Unknown => Err(SmtPipelineError::UnknownFormat),
    }
}

/// Verify an SMT proof and return a competition-formatted result.
///
/// Wraps [`verify_smt_proof_bytes`] and translates the output into
/// [`SmtCompetitionResult`] suitable for SMT-COMP judging.
///
/// Never returns an error -- errors are captured as `Unknown` verdict.
#[must_use]
pub fn verify_smt_competition_entry(
    proof_bytes: &[u8],
    config: &SmtPipelineConfig,
) -> SmtCompetitionResult {
    match verify_smt_proof_bytes(proof_bytes, config) {
        Ok(result) => SmtCompetitionResult {
            verdict: result.verdict,
            holes: result.holes,
            steps_verified: result.stats.kernel_verified
                + result.stats.structurally_accepted
                + result.stats.axiomatic,
            steps_trusted: result.stats.trusted,
            verification_time_us: result.verification_time_us,
            error: None,
        },
        Err(e) => SmtCompetitionResult {
            verdict: SmtCompVerdict::Unknown,
            holes: 0,
            steps_verified: 0,
            steps_trusted: 0,
            verification_time_us: 0,
            error: Some(e.to_string()),
        },
    }
}

/// Format a competition result as SMT-COMP stdout output.
///
/// Produces the exact output format expected by SMT-COMP judges:
/// ```text
/// valid
/// holes: 0
/// steps: 42, trusted: 0
/// ```
///
/// Or for errors:
/// ```text
/// unknown
/// error: <message>
/// ```
#[must_use]
pub fn format_competition_output(result: &SmtCompetitionResult) -> String {
    let mut out = String::with_capacity(128);

    // Line 1: verdict
    out.push_str(&result.verdict.to_string());
    out.push('\n');

    if result.verdict == SmtCompVerdict::Unknown {
        if let Some(ref err) = result.error {
            out.push_str(&format!("error: {err}\n"));
        }
    } else {
        // Line 2: hole count
        out.push_str(&format!("holes: {}\n", result.holes));
        // Line 3: step counts
        out.push_str(&format!(
            "steps: {}, trusted: {}\n",
            result.steps_verified, result.steps_trusted,
        ));
    }

    out
}

// ---------------------------------------------------------------------------
// Internal verification dispatch
// ---------------------------------------------------------------------------

/// Verify an Alethe proof from raw bytes.
fn verify_alethe_bytes(
    proof_bytes: &[u8],
    config: &SmtPipelineConfig,
) -> Result<SmtPipelineResult, SmtPipelineError> {
    let proof_text = std::str::from_utf8(proof_bytes)
        .map_err(|e| SmtPipelineError::InvalidUtf8(e.to_string()))?;

    let start = Instant::now();
    let result = verify_alethe_proof_with_mode(proof_text, config.mode)?;
    let elapsed_us = start.elapsed().as_micros() as u64;

    let verdict = stats_to_verdict(&result.stats, result.valid);
    let holes = result.stats.holes_count();

    let certificate = if config.generate_certificate && result.valid {
        Some(certificate::generate_certificate(
            // We need a DAG for certificate generation. Re-parse is acceptable
            // since this is the cold path (certificate generation).
            &reparse_alethe_to_dag(proof_text),
            &super::trust::SmtVerifyResult {
                valid: result.valid,
                verdicts: result.verdicts.clone(),
                stats: result.stats.clone(),
                first_error: result.first_error.clone(),
            },
            &[], // formula bytes (empty for self-contained proofs)
            proof_bytes,
            "alethe",
            config.mode,
        ))
    } else {
        None
    };

    Ok(SmtPipelineResult {
        format: SmtProofFormat::AletheText,
        valid: result.valid,
        verdict,
        stats: result.stats,
        verification_time_us: elapsed_us,
        holes,
        certificate,
        diagnostics: Vec::new(),
    })
}

/// Verify an SMT-LIB2 proof from raw bytes.
fn verify_smtlib2_bytes(
    proof_bytes: &[u8],
    config: &SmtPipelineConfig,
) -> Result<SmtPipelineResult, SmtPipelineError> {
    let proof_text = std::str::from_utf8(proof_bytes)
        .map_err(|e| SmtPipelineError::InvalidUtf8(e.to_string()))?;

    let start = Instant::now();

    let dag = smtlib2_proof::parse_and_convert(proof_text)
        .map_err(|e| SmtPipelineError::SmtLib2(e.to_string()))?;

    let result = verify_smt_proof(&dag, config.mode);
    let elapsed_us = start.elapsed().as_micros() as u64;

    let verdict = stats_to_verdict(&result.stats, result.valid);
    let holes = result.stats.holes_count();

    let certificate = if config.generate_certificate && result.valid {
        Some(certificate::generate_certificate(
            &dag,
            &result,
            &[], // formula bytes
            proof_bytes,
            "smtlib2",
            config.mode,
        ))
    } else {
        None
    };

    let diagnostics = result
        .first_error
        .as_ref()
        .map(|e| vec![e.to_string()])
        .unwrap_or_default();

    Ok(SmtPipelineResult {
        format: SmtProofFormat::SmtLib2,
        valid: result.valid,
        verdict,
        stats: result.stats,
        verification_time_us: elapsed_us,
        holes,
        certificate,
        diagnostics,
    })
}

/// Re-parse Alethe proof text into a DAG for certificate generation.
///
/// This is a convenience function used only in the certificate generation
/// path, where we need the DAG but only have the `SmtVerifyResult`.
fn reparse_alethe_to_dag(proof_text: &str) -> super::dag::SmtProofDag {
    // Best-effort: if parsing fails, return empty DAG.
    match super::alethe_parser::parse_alethe(proof_text) {
        Ok(parsed) => super::alethe_bridge::alethe_to_dag(parsed),
        Err(_) => super::dag::SmtProofDag::new(),
    }
}

/// Derive an [`SmtCompVerdict`] from verification stats and validity.
pub(crate) fn stats_to_verdict(stats: &SmtVerifyStats, valid: bool) -> SmtCompVerdict {
    if !valid {
        return SmtCompVerdict::Invalid;
    }
    match stats.competition_verdict() {
        "valid" => SmtCompVerdict::Valid,
        "holey" => SmtCompVerdict::Holey,
        _ => SmtCompVerdict::Invalid,
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    // ---- Format detection tests ----

    #[test]
    fn test_detect_smt_format_empty() {
        assert_eq!(detect_smt_format(b""), SmtProofFormat::Unknown);
    }

    #[test]
    fn test_detect_smt_format_whitespace_only() {
        assert_eq!(detect_smt_format(b"   \n  \t  "), SmtProofFormat::Unknown);
    }

    #[test]
    fn test_detect_smt_format_alethe_parens() {
        let data = b"(declare-const p Bool)\n(assume h1 p)\n";
        assert_eq!(detect_smt_format(data), SmtProofFormat::AletheText);
    }

    #[test]
    fn test_detect_smt_format_alethe_set_logic() {
        let data = b"  set-logic QF_UF\n(assume h1 p)\n";
        assert_eq!(detect_smt_format(data), SmtProofFormat::AletheText);
    }

    #[test]
    fn test_detect_smt_format_smtlib2_proof_block() {
        let data = b"(declare-fun p () Bool)\n(assert p)\n(proof (mp ...))";
        assert_eq!(detect_smt_format(data), SmtProofFormat::SmtLib2);
    }

    #[test]
    fn test_detect_smt_format_random_data() {
        assert_eq!(
            detect_smt_format(b"random garbage data 12345"),
            SmtProofFormat::Unknown
        );
    }

    // ---- SmtCompVerdict display tests ----

    #[test]
    fn test_verdict_display_valid() {
        assert_eq!(SmtCompVerdict::Valid.to_string(), "valid");
    }

    #[test]
    fn test_verdict_display_holey() {
        assert_eq!(SmtCompVerdict::Holey.to_string(), "holey");
    }

    #[test]
    fn test_verdict_display_invalid() {
        assert_eq!(SmtCompVerdict::Invalid.to_string(), "invalid");
    }

    #[test]
    fn test_verdict_display_unknown() {
        assert_eq!(SmtCompVerdict::Unknown.to_string(), "unknown");
    }

    // ---- SmtProofFormat display tests ----

    #[test]
    fn test_format_display_alethe() {
        assert_eq!(SmtProofFormat::AletheText.to_string(), "Alethe");
    }

    #[test]
    fn test_format_display_smtlib2() {
        assert_eq!(SmtProofFormat::SmtLib2.to_string(), "SMT-LIB2");
    }

    #[test]
    fn test_format_display_unknown() {
        assert_eq!(SmtProofFormat::Unknown.to_string(), "Unknown");
    }

    // ---- stats_to_verdict tests ----

    #[test]
    fn test_stats_to_verdict_valid() {
        let stats = SmtVerifyStats {
            total_steps: 3,
            kernel_verified: 2,
            axiomatic: 1,
            ..Default::default()
        };
        assert_eq!(stats_to_verdict(&stats, true), SmtCompVerdict::Valid);
    }

    #[test]
    fn test_stats_to_verdict_holey() {
        let stats = SmtVerifyStats {
            total_steps: 3,
            kernel_verified: 1,
            structurally_accepted: 2,
            ..Default::default()
        };
        assert_eq!(stats_to_verdict(&stats, true), SmtCompVerdict::Holey);
    }

    #[test]
    fn test_stats_to_verdict_invalid_trusted() {
        let stats = SmtVerifyStats {
            total_steps: 3,
            kernel_verified: 1,
            trusted: 2,
            ..Default::default()
        };
        assert_eq!(stats_to_verdict(&stats, true), SmtCompVerdict::Invalid);
    }

    #[test]
    fn test_stats_to_verdict_invalid_not_valid() {
        let stats = SmtVerifyStats {
            total_steps: 3,
            kernel_verified: 3,
            ..Default::default()
        };
        assert_eq!(stats_to_verdict(&stats, false), SmtCompVerdict::Invalid);
    }

    // ---- Pipeline config tests ----

    #[test]
    fn test_pipeline_config_default() {
        let config = SmtPipelineConfig::default();
        assert_eq!(config.mode, VerifyMode::Permissive);
        assert!(config.format_hint.is_none());
        assert!(!config.generate_certificate);
    }

    // ---- Competition output formatting tests ----

    #[test]
    fn test_format_competition_output_valid() {
        let result = SmtCompetitionResult {
            verdict: SmtCompVerdict::Valid,
            holes: 0,
            steps_verified: 42,
            steps_trusted: 0,
            verification_time_us: 1000,
            error: None,
        };
        let output = format_competition_output(&result);
        assert_eq!(output, "valid\nholes: 0\nsteps: 42, trusted: 0\n");
    }

    #[test]
    fn test_format_competition_output_holey() {
        let result = SmtCompetitionResult {
            verdict: SmtCompVerdict::Holey,
            holes: 5,
            steps_verified: 37,
            steps_trusted: 0,
            verification_time_us: 2000,
            error: None,
        };
        let output = format_competition_output(&result);
        assert_eq!(output, "holey\nholes: 5\nsteps: 37, trusted: 0\n");
    }

    #[test]
    fn test_format_competition_output_invalid() {
        let result = SmtCompetitionResult {
            verdict: SmtCompVerdict::Invalid,
            holes: 3,
            steps_verified: 20,
            steps_trusted: 5,
            verification_time_us: 500,
            error: None,
        };
        let output = format_competition_output(&result);
        assert_eq!(output, "invalid\nholes: 3\nsteps: 20, trusted: 5\n");
    }

    #[test]
    fn test_format_competition_output_unknown_with_error() {
        let result = SmtCompetitionResult {
            verdict: SmtCompVerdict::Unknown,
            holes: 0,
            steps_verified: 0,
            steps_trusted: 0,
            verification_time_us: 0,
            error: Some("parse error at offset 42".to_string()),
        };
        let output = format_competition_output(&result);
        assert_eq!(output, "unknown\nerror: parse error at offset 42\n");
    }

    #[test]
    fn test_format_competition_output_unknown_without_error() {
        let result = SmtCompetitionResult {
            verdict: SmtCompVerdict::Unknown,
            holes: 0,
            steps_verified: 0,
            steps_trusted: 0,
            verification_time_us: 0,
            error: None,
        };
        let output = format_competition_output(&result);
        assert_eq!(output, "unknown\n");
    }

    // ---- Pipeline end-to-end tests (Alethe) ----

    #[test]
    fn test_pipeline_alethe_valid_proof() {
        let proof = br#"
            (declare-const p Bool)
            (assume h1 p)
            (assume h2 (not p))
            (step t1 (cl) :rule resolution :premises (h1 h2))
        "#;

        let config = SmtPipelineConfig::default();
        let result =
            verify_smt_proof_bytes(proof, &config).expect("valid Alethe proof should verify");

        assert!(result.valid);
        assert_eq!(result.format, SmtProofFormat::AletheText);
        assert!(
            result.verdict == SmtCompVerdict::Valid || result.verdict == SmtCompVerdict::Holey,
            "verdict should be valid or holey, got {:?}",
            result.verdict,
        );
        assert!(result.stats.total_steps > 0);
        // verification_time_us is u64, so it is always non-negative by type; no runtime check needed.
    }

    #[test]
    fn test_pipeline_alethe_invalid_proof_no_empty_clause() {
        let proof = br#"
            (declare-const p Bool)
            (assume h1 p)
        "#;

        let config = SmtPipelineConfig::default();
        let result = verify_smt_proof_bytes(proof, &config);

        // Should either error or return invalid verdict.
        if let Ok(r) = result {
            assert!(!r.valid);
            assert_eq!(r.verdict, SmtCompVerdict::Invalid);
        } // Err is also acceptable
    }

    #[test]
    fn test_pipeline_alethe_strict_rejects_trust() {
        let proof = br#"
            (declare-const p Bool)
            (assume h1 p)
            (step t1 (cl (not p)) :rule trust)
            (step t2 (cl) :rule resolution :premises (h1 t1))
        "#;

        let config = SmtPipelineConfig {
            mode: VerifyMode::Strict,
            ..SmtPipelineConfig::default()
        };

        let result = verify_smt_proof_bytes(proof, &config);
        // Strict mode should reject the trust step.
        if let Ok(r) = result {
            assert!(!r.valid);
            assert_eq!(r.verdict, SmtCompVerdict::Invalid);
        } // Error is also acceptable in strict mode
    }

    #[test]
    fn test_pipeline_empty_proof_error() {
        let config = SmtPipelineConfig::default();
        let result = verify_smt_proof_bytes(b"", &config);
        assert!(matches!(result, Err(SmtPipelineError::EmptyProof)));
    }

    #[test]
    fn test_pipeline_unknown_format_error() {
        let config = SmtPipelineConfig::default();
        let result = verify_smt_proof_bytes(b"random garbage 12345", &config);
        assert!(matches!(result, Err(SmtPipelineError::UnknownFormat)));
    }

    #[test]
    fn test_pipeline_format_hint_overrides_detection() {
        // Pass Alethe proof but hint as SMT-LIB2 -- should fail parsing.
        let proof = br#"
            (declare-const p Bool)
            (assume h1 p)
            (assume h2 (not p))
            (step t1 (cl) :rule resolution :premises (h1 h2))
        "#;

        let config = SmtPipelineConfig {
            format_hint: Some(SmtProofFormat::SmtLib2),
            ..SmtPipelineConfig::default()
        };

        let result = verify_smt_proof_bytes(proof, &config);
        // SMT-LIB2 parser should fail on Alethe syntax.
        if let Ok(r) = result {
            // If it somehow parsed, it should be invalid or have diagnostics.
            assert!(!r.valid || !r.diagnostics.is_empty());
        } // Err is the expected path
    }

    // ---- Competition entry tests ----

    #[test]
    fn test_competition_entry_valid_proof() {
        let proof = br#"
            (declare-const p Bool)
            (assume h1 p)
            (assume h2 (not p))
            (step t1 (cl) :rule resolution :premises (h1 h2))
        "#;

        let config = SmtPipelineConfig::default();
        let result = verify_smt_competition_entry(proof, &config);

        assert!(
            result.verdict == SmtCompVerdict::Valid || result.verdict == SmtCompVerdict::Holey,
            "competition verdict should be valid or holey, got {:?}",
            result.verdict,
        );
        assert!(result.steps_verified > 0);
        assert!(result.error.is_none());
    }

    #[test]
    fn test_competition_entry_empty_proof_unknown() {
        let config = SmtPipelineConfig::default();
        let result = verify_smt_competition_entry(b"", &config);

        assert_eq!(result.verdict, SmtCompVerdict::Unknown);
        assert!(result.error.is_some());
    }

    #[test]
    fn test_competition_entry_garbage_unknown() {
        let config = SmtPipelineConfig::default();
        let result = verify_smt_competition_entry(b"not a proof", &config);

        assert_eq!(result.verdict, SmtCompVerdict::Unknown);
        assert!(result.error.is_some());
    }

    // ---- Round-trip: pipeline -> competition output -> parse verdict ----

    #[test]
    fn test_roundtrip_valid_proof_to_competition_output() {
        let proof = br#"
            (declare-const p Bool)
            (assume h1 p)
            (assume h2 (not p))
            (step t1 (cl) :rule resolution :premises (h1 h2))
        "#;

        let config = SmtPipelineConfig::default();
        let comp_result = verify_smt_competition_entry(proof, &config);
        let output = format_competition_output(&comp_result);

        // First line should be the verdict.
        let first_line = output.lines().next().expect("output should have lines");
        assert!(
            first_line == "valid" || first_line == "holey",
            "first line should be valid or holey, got '{first_line}'"
        );

        // Second line should be holes count.
        let second_line = output.lines().nth(1).expect("output should have 2+ lines");
        assert!(
            second_line.starts_with("holes: "),
            "second line should start with 'holes: ', got '{second_line}'"
        );

        // Third line should be step counts.
        let third_line = output.lines().nth(2).expect("output should have 3 lines");
        assert!(
            third_line.starts_with("steps: "),
            "third line should start with 'steps: ', got '{third_line}'"
        );
    }

    #[test]
    fn test_roundtrip_invalid_proof_to_competition_output() {
        let proof = br#"
            (declare-const p Bool)
            (assume h1 p)
        "#;

        let config = SmtPipelineConfig::default();
        let comp_result = verify_smt_competition_entry(proof, &config);
        let output = format_competition_output(&comp_result);

        let first_line = output.lines().next().expect("output should have lines");
        // Should be either "invalid" or "unknown" (depending on whether
        // the proof parses and verifies or fails during parsing).
        assert!(
            first_line == "invalid" || first_line == "unknown",
            "first line should be invalid or unknown, got '{first_line}'"
        );
    }

    // ---- Certificate generation test ----

    #[test]
    fn test_pipeline_certificate_generation() {
        let proof = br#"
            (declare-const p Bool)
            (assume h1 p)
            (assume h2 (not p))
            (step t1 (cl) :rule resolution :premises (h1 h2))
        "#;

        let config = SmtPipelineConfig {
            generate_certificate: true,
            ..SmtPipelineConfig::default()
        };

        let result = verify_smt_proof_bytes(proof, &config).expect("valid proof should verify");

        assert!(result.valid);
        let cert = result.certificate.expect("certificate should be generated");
        assert_eq!(cert.proof_format, "alethe");
        assert!(!cert.proof_hash.is_empty());
        assert!(cert.trust_summary.total > 0);
    }
}
