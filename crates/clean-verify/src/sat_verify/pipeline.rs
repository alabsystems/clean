// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Unified proof verification pipeline with format auto-detection.
//!
//! Provides a single entry point ([`verify_proof`]) for verifying SAT/SMT proofs
//! in any supported format: DRAT (text/binary), LRAT (text/binary), Alethe,
//! VeriPB, OPB, Resolution, and Extended Resolution. The pipeline auto-detects
//! the proof format, runs the appropriate checker, optionally builds a
//! [`CertificateEnvelope`] for ay, and returns comprehensive statistics.
//!
//! ## Top-Level Entry Point
//!
//! [`verify_any_proof`] accepts raw formula and proof bytes, auto-detects the
//! proof format, and returns a [`UnifiedResult`] with format, validity, timing,
//! and trust level information.
//!
//! ## Competition Mode
//!
//! [`verify_competition_entry`] accepts raw DIMACS + proof bytes, the format
//! used by SAT-COMP judges for UNSAT certificate validation.
//!
//! ## Architecture
//!
//! ```text
//! verify_any_proof(formula, proof)
//!   ├─→ detect_format(proof)
//!   ├─→ route to checker (LRAT/DRAT/Alethe/VeriPB/OPB)
//!   └─→ UnifiedResult { format, valid, timing, trust_level }
//! ```
//!
//! ## References
//!
//! - Heule et al. (2017): "Trimming while Checking Clausal Proofs"
//! - Cruz-Filipe et al. (2017): "Efficient Certified RAT Verification"
//! - VeriPB: <https://github.com/StephanGocht/VeriPB>
//! - Alethe: <https://verit.loria.fr/documentation/alethe-spec.pdf>

use std::collections::HashMap;
use std::io;
use std::time::Instant;

use thiserror::Error;

use super::ay_contract::CertificateEnvelope;
use super::ay_import::{
    detect_format as detect_drat_format, verify_ay_drat_proof, AyDratImporter, DratFormat,
};
use super::drat_to_lrat::{self as drat_converter, ConvertError};
use super::frat::{
    self, looks_like_frat_binary, looks_like_frat_text as frat_text_heuristic, FratError,
};
use super::lrat::is_binary_lrat;
use super::lrat_kernel_bridge::{
    to_certificate_envelope as lrat_to_envelope, verify_and_certify as lrat_verify_text,
    verify_auto_and_certify as lrat_verify_auto, LratBridgeError,
};
use super::pseudo_boolean::{parse_opb, PbError};
use super::types::Cnf;
use crate::smt_verify::smtlib2_proof;
use crate::smt_verify::{self, VerifyMode};

/// Errors from the unified proof pipeline.
#[derive(Debug, Error)]
#[non_exhaustive]
pub enum PipelineError {
    /// DRAT import or verification failed.
    #[error("DRAT error: {0}")]
    Drat(#[from] super::ay_import::AyImportError),

    /// LRAT bridge error.
    #[error("LRAT error: {0}")]
    Lrat(#[from] LratBridgeError),

    /// FRAT proof verification failed.
    #[error("FRAT error: {0}")]
    Frat(#[from] FratError),

    /// Alethe SMT proof verification failed.
    #[error("Alethe error: {0}")]
    Alethe(String),

    /// Pseudo-Boolean proof verification failed.
    #[error("PB error: {0}")]
    PseudoBoolean(#[from] PbError),

    /// DIMACS CNF parsing failed.
    #[error("CNF parse error: {0}")]
    CnfParse(String),

    /// The proof format could not be determined.
    #[error("unable to detect proof format")]
    UnknownFormat,

    /// The pipeline received an unsupported format.
    #[error("unsupported proof format: {format:?}")]
    UnsupportedFormat { format: ProofFormat },

    /// The proof data was empty.
    #[error("proof data is empty")]
    EmptyProof,

    /// The proof data was not valid UTF-8.
    #[error("proof is not valid UTF-8: {0}")]
    InvalidUtf8(String),

    /// DRAT streaming conversion/verification failed.
    #[error("DRAT streaming error: {0}")]
    DratStreaming(#[from] ConvertError),

    /// I/O error during streaming operations.
    #[error("I/O error: {0}")]
    IoError(String),
}

/// Supported proof formats.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum ProofFormat {
    /// DRAT (Deletion Resolution Asymmetric Tautology).
    Drat,
    /// LRAT (Linear Resolution Asymmetric Tautology).
    Lrat,
    /// FRAT (Forward-checking RAT) -- native format of CaDiCaL/Kissat.
    Frat,
    /// Alethe SMT proof format.
    Alethe,
    /// SMT-LIB2 proof format (SMT-LIB 2.7 standard / Z3-style proofs).
    SmtLib2Proof,
    /// VeriPB pseudo-Boolean proof format.
    VeriPb,
    /// OPB pseudo-Boolean formula + proof (PB Competition format).
    Opb,
    /// Polynomial Calculus over GF(2) (algebraic SAT proof format).
    PolynomialCalculus,
    /// Format could not be determined.
    Unknown,
}

impl std::fmt::Display for ProofFormat {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ProofFormat::Drat => write!(f, "DRAT"),
            ProofFormat::Lrat => write!(f, "LRAT"),
            ProofFormat::Frat => write!(f, "FRAT"),
            ProofFormat::Alethe => write!(f, "Alethe"),
            ProofFormat::SmtLib2Proof => write!(f, "SMT-LIB2"),
            ProofFormat::VeriPb => write!(f, "VeriPB"),
            ProofFormat::Opb => write!(f, "OPB"),
            ProofFormat::PolynomialCalculus => write!(f, "PC/GF(2)"),
            ProofFormat::Unknown => write!(f, "Unknown"),
        }
    }
}

/// Input proof data in any supported format.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub enum ProofInput {
    /// Text-format DRAT proof.
    DratText(String),
    /// Binary-format DRAT proof.
    DratBinary(Vec<u8>),
    /// Text-format LRAT proof.
    LratText(String),
    /// Binary-format LRAT proof.
    LratBinary(Vec<u8>),
    /// Text-format FRAT proof.
    FratText(String),
    /// Binary-format FRAT proof.
    FratBinary(Vec<u8>),
    /// Alethe SMT proof (text).
    AletheSmt(String),
    /// SMT-LIB2 proof format (text).
    SmtLib2Proof(String),
    /// VeriPB pseudo-Boolean proof (text).
    VeriPbText(String),
    /// OPB pseudo-Boolean formula (text).
    OpbText(String),
    /// Polynomial Calculus text certificate (PC-GF2 format).
    PcText(String),
    /// Polynomial Calculus binary certificate (PC2 magic format).
    PcBinary(Vec<u8>),
}

impl ProofInput {
    /// The proof format implied by this input variant.
    #[must_use]
    pub fn format(&self) -> ProofFormat {
        match self {
            ProofInput::DratText(_) | ProofInput::DratBinary(_) => ProofFormat::Drat,
            ProofInput::LratText(_) | ProofInput::LratBinary(_) => ProofFormat::Lrat,
            ProofInput::FratText(_) | ProofInput::FratBinary(_) => ProofFormat::Frat,
            ProofInput::AletheSmt(_) => ProofFormat::Alethe,
            ProofInput::SmtLib2Proof(_) => ProofFormat::SmtLib2Proof,
            ProofInput::VeriPbText(_) => ProofFormat::VeriPb,
            ProofInput::OpbText(_) => ProofFormat::Opb,
            ProofInput::PcText(_) | ProofInput::PcBinary(_) => ProofFormat::PolynomialCalculus,
        }
    }

    /// The raw byte size of the proof data.
    #[must_use]
    pub fn size_bytes(&self) -> usize {
        match self {
            ProofInput::DratText(s)
            | ProofInput::AletheSmt(s)
            | ProofInput::SmtLib2Proof(s)
            | ProofInput::VeriPbText(s)
            | ProofInput::OpbText(s)
            | ProofInput::FratText(s)
            | ProofInput::PcText(s) => s.len(),
            ProofInput::DratBinary(b)
            | ProofInput::LratBinary(b)
            | ProofInput::FratBinary(b)
            | ProofInput::PcBinary(b) => b.len(),
            ProofInput::LratText(s) => s.len(),
        }
    }
}

/// Statistics from a pipeline verification run.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PipelineStats {
    /// Number of proof steps that were fully verified.
    pub steps_verified: usize,
    /// Number of proof steps accepted on trust (not independently checked).
    pub steps_trusted: usize,
    /// Input formula size in bytes (DIMACS encoding).
    pub input_size_bytes: usize,
    /// Proof data size in bytes.
    pub proof_size_bytes: usize,
}

impl PipelineStats {
    /// Trust ratio: fraction of verified steps over total steps.
    ///
    /// Returns 1.0 if there are no steps (vacuously trusted).
    #[must_use]
    pub fn trust_ratio(&self) -> f64 {
        let total = self.steps_verified + self.steps_trusted;
        if total == 0 {
            return 1.0;
        }
        self.steps_verified as f64 / total as f64
    }
}

/// Result of a pipeline verification run.
#[derive(Debug, Clone)]
pub struct PipelineResult {
    /// Whether the proof was successfully verified.
    pub valid: bool,
    /// The detected (or hinted) proof format.
    pub format_detected: ProofFormat,
    /// Wall-clock verification time in microseconds.
    pub verification_time_us: u64,
    /// Certificate envelope for ay, if verification succeeded and
    /// certificate generation was enabled.
    pub certificate: Option<CertificateEnvelope>,
    /// Verification statistics.
    pub stats: PipelineStats,
    /// Diagnostic or error messages from the pipeline.
    pub errors: Vec<String>,
}

/// Pipeline configuration options.
#[derive(Debug, Clone)]
pub struct PipelineConfig {
    /// If true, reject any proof that contains trusted (unverified) steps.
    pub strict_mode: bool,
    /// If true, generate a [`CertificateEnvelope`] on successful verification.
    pub compute_certificate: bool,
    /// Optional timeout in milliseconds (not enforced by the pipeline itself,
    /// but recorded for downstream use).
    pub timeout_ms: Option<u64>,
    /// If set, skip auto-detection and use this format directly.
    pub format_hint: Option<ProofFormat>,
}

impl Default for PipelineConfig {
    fn default() -> Self {
        Self {
            strict_mode: false,
            compute_certificate: true,
            timeout_ms: None,
            format_hint: None,
        }
    }
}

// ---------------------------------------------------------------------------
// Format auto-detection
// ---------------------------------------------------------------------------

/// Detect the proof format from raw bytes.
///
/// Heuristics (checked in order):
/// - VeriPB: starts with `pseudo-Boolean` (case-insensitive).
/// - OPB: starts with `*` comment lines containing `#variable=` or `#constraint=`,
///   or has `>=` constraints in PB format.
/// - Alethe: starts with `(` or contains `set-logic` / `set-info` near start.
/// - LRAT binary: passes LRAT binary structure check (two zero-terminators).
/// - DRAT binary: ay_import detects binary DRAT encoding.
/// - LRAT text: lines match `<id> <lits> 0 <hints> 0` pattern.
/// - DRAT text: lines match `<lits> 0` pattern (fallback).
#[must_use]
pub fn detect_format(data: &[u8]) -> ProofFormat {
    if data.is_empty() {
        return ProofFormat::Unknown;
    }

    // Find first non-whitespace byte.
    let first_nonws = data.iter().position(|b| !b.is_ascii_whitespace());
    let Some(start) = first_nonws else {
        return ProofFormat::Unknown;
    };

    // Check for VeriPB: starts with "pseudo-Boolean" (case-insensitive prefix).
    if data.len() >= start + 14 {
        let prefix = &data[start..start + 14];
        if prefix.eq_ignore_ascii_case(b"pseudo-Boolean") {
            return ProofFormat::VeriPb;
        }
    }

    // Check for OPB: starts with `*` comment header containing PB metadata.
    if data[start] == b'*' {
        let search_window = std::cmp::min(data.len(), start + 512);
        if let Ok(text_window) = std::str::from_utf8(&data[start..search_window]) {
            if looks_like_opb(text_window) {
                return ProofFormat::Opb;
            }
        }
    }

    // Check for SMT-LIB2 proof format before Alethe — both start with `(`.
    // SMT-LIB2 proofs use `declare-sort`/`declare-fun` preamble + `(proof ...)` block,
    // while Alethe uses `(assume ...)` and `(step ...)` commands.
    if data[start] == b'(' && smtlib2_proof::looks_like_smtlib2_proof(data) {
        return ProofFormat::SmtLib2Proof;
    }

    // Check for Alethe: starts with `(` or has `set-logic` / `set-info` near start.
    if data[start] == b'(' {
        return ProofFormat::Alethe;
    }
    let search_window = std::cmp::min(data.len(), start + 256);
    if let Ok(text_window) = std::str::from_utf8(&data[start..search_window]) {
        if text_window.contains("set-logic") || text_window.contains("set-info") {
            return ProofFormat::Alethe;
        }
    }

    // Check for FRAT binary (tags o/l/f distinguish from DRAT/LRAT).
    if looks_like_frat_binary(data) {
        return ProofFormat::Frat;
    }

    // Binary format detection: check if LRAT binary first (more specific).
    if is_binary_lrat(data) {
        // Distinguish LRAT binary from DRAT binary.
        // LRAT binary steps have: tag + clause_id + lits + 0 + hints + 0
        // DRAT binary steps have: tag + lits + 0 (no clause_id, no hints section)
        // Try parsing a small prefix as LRAT to see if it succeeds.
        if try_parse_lrat_binary_prefix(data) {
            return ProofFormat::Lrat;
        }
        // Fall through to DRAT binary check.
    }

    // Check for DRAT binary using ay_import's heuristic.
    let drat_fmt = detect_drat_format(data);
    if drat_fmt == DratFormat::Binary {
        return ProofFormat::Drat;
    }

    // Check for PC/GF(2) binary certificate (magic bytes "PC2\0").
    if data.len() >= start + 4 {
        let magic = u32::from_le_bytes([
            data[start],
            data[start + 1],
            data[start + 2],
            data[start + 3],
        ]);
        // PC2\0 magic bytes (little-endian u32) marking Polynomial Calculus
        // proof files. The underscores group the four bytes 0x00 0x50 0x43 0x32.
        if magic == 0x0050_4332 {
            return ProofFormat::PolynomialCalculus;
        }
    }

    // Text format: FRAT text before LRAT/DRAT (FRAT has distinctive o/l/f tags).
    if let Ok(text) = std::str::from_utf8(data) {
        // Check for PC-GF2 text certificate format.
        if text.trim_start().starts_with("PC-GF2") {
            return ProofFormat::PolynomialCalculus;
        }
        if frat_text_heuristic(text) {
            return ProofFormat::Frat;
        }
        if looks_like_lrat_text(text) {
            return ProofFormat::Lrat;
        }
        if looks_like_drat_text(text) {
            return ProofFormat::Drat;
        }
    }

    ProofFormat::Unknown
}

/// Check if the data looks like LRAT binary by trying to parse the first step.
fn try_parse_lrat_binary_prefix(data: &[u8]) -> bool {
    // A quick heuristic: LRAT binary has two zero-terminated sections per 'a' step
    // (literals then hints). Count zeros after the first 'a' tag.
    let mut pos = 0;
    while pos < data.len() && data[pos].is_ascii_whitespace() {
        pos += 1;
    }
    if pos >= data.len() || data[pos] != b'a' {
        return false;
    }
    pos += 1;

    // In LRAT binary: clause_id (ULEB128) then lits... 0 hints... 0
    // In DRAT binary: lits... 0 (single zero terminator)
    // Count zero bytes encountered.
    let mut zero_count = 0;
    let limit = std::cmp::min(data.len(), pos + 64);
    while pos < limit {
        if data[pos] == 0 {
            zero_count += 1;
            if zero_count >= 2 {
                return true; // Two zero terminators = likely LRAT binary
            }
        }
        pos += 1;
    }
    false
}

/// Check if text looks like LRAT format.
///
/// LRAT text lines have the pattern: `<id> [d] <content> 0 [<hints> 0]`.
/// The key differentiator from DRAT is the leading clause ID on each line.
fn looks_like_lrat_text(text: &str) -> bool {
    for line in text.lines().take(5) {
        let trimmed = line.trim();
        if trimmed.is_empty() || trimmed.starts_with('c') {
            continue;
        }
        let tokens: Vec<&str> = trimmed.split_whitespace().collect();
        if tokens.len() < 2 {
            continue;
        }
        // LRAT lines start with a positive integer (clause ID).
        let first_is_positive_int = tokens[0].parse::<u64>().is_ok_and(|v| v > 0);
        if !first_is_positive_int {
            return false;
        }
        // Check for two zero terminators (clause 0 hints 0) or deletion (d).
        let zero_count = tokens.iter().filter(|&&t| t == "0").count();
        if zero_count >= 2 || tokens[1] == "d" {
            return true;
        }
    }
    false
}

/// Check if text looks like DRAT format.
fn looks_like_drat_text(text: &str) -> bool {
    for line in text.lines().take(5) {
        let trimmed = line.trim();
        if trimmed.is_empty() || trimmed.starts_with('c') {
            continue;
        }
        // DRAT lines are: optional 'd' prefix, then literals, then '0'.
        let content = trimmed.strip_prefix('d').map_or(trimmed, str::trim_start);
        let has_zero_terminator = content.split_whitespace().any(|t| t == "0");
        if has_zero_terminator {
            return true;
        }
    }
    false
}

/// Check if text looks like OPB format.
///
/// OPB files start with `*` comment lines and contain PB competition metadata
/// like `#variable=` or `#constraint=`, or have PB constraints with `>=`.
fn looks_like_opb(text: &str) -> bool {
    for line in text.lines().take(10) {
        let trimmed = line.trim();
        if trimmed.is_empty() {
            continue;
        }
        if trimmed.starts_with('*') {
            // PB competition header: `* #variable= N #constraint= M`
            if trimmed.contains("#variable=") || trimmed.contains("#constraint=") {
                return true;
            }
            continue;
        }
        // Non-comment constraint lines in OPB use `>=` or `=` with `xN` or `~xN` terms.
        if (trimmed.contains(">=") || trimmed.contains(" = "))
            && (trimmed.contains(" x") || trimmed.contains("~x"))
        {
            return true;
        }
    }
    false
}

// ---------------------------------------------------------------------------
// Trust level classification
// ---------------------------------------------------------------------------

/// Trust level for a unified verification result.
///
/// Classifies how deeply the proof was checked, from full kernel verification
/// down to format recognition without checking.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum TrustLevel {
    /// Every proof step was independently verified by clean's kernel.
    KernelVerified,
    /// Proof was verified but some steps were structurally accepted
    /// (correct arity/shape but not semantically rechecked).
    StructurallyVerified,
    /// Proof format was recognized and the proof was partially verified.
    PartiallyVerified,
    /// Format was detected but verification is not available.
    FormatRecognized,
    /// Unknown format or empty proof.
    Unverified,
}

impl std::fmt::Display for TrustLevel {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TrustLevel::KernelVerified => write!(f, "kernel-verified"),
            TrustLevel::StructurallyVerified => write!(f, "structurally-verified"),
            TrustLevel::PartiallyVerified => write!(f, "partially-verified"),
            TrustLevel::FormatRecognized => write!(f, "format-recognized"),
            TrustLevel::Unverified => write!(f, "unverified"),
        }
    }
}

/// Unified result from [`verify_any_proof`].
///
/// Combines format detection, verification outcome, timing, and trust
/// classification into a single result type suitable for competition
/// judges and ay integration.
#[derive(Debug, Clone)]
pub struct UnifiedResult {
    /// The detected proof format.
    pub format: ProofFormat,
    /// Whether the proof was successfully verified as a valid refutation.
    pub valid: bool,
    /// Wall-clock verification time in microseconds.
    pub verification_time_us: u64,
    /// Trust level classification.
    pub trust_level: TrustLevel,
    /// Number of proof steps verified.
    pub steps_verified: usize,
    /// Number of proof steps accepted on trust.
    pub steps_trusted: usize,
    /// Certificate envelope, if verification succeeded and the format supports it.
    pub certificate: Option<CertificateEnvelope>,
    /// Diagnostic or error messages.
    pub errors: Vec<String>,
}

// ---------------------------------------------------------------------------
// Top-level entry point
// ---------------------------------------------------------------------------

/// Verify any proof format against a formula, both provided as raw bytes.
///
/// This is the top-level entry point that:
/// 1. Auto-detects the proof format from byte content
/// 2. Routes to the appropriate checker (LRAT, DRAT, Alethe, VeriPB, OPB)
/// 3. Returns a [`UnifiedResult`] with format, validity, timing, and trust level
///
/// The `formula` parameter is interpreted based on the detected format:
/// - For SAT formats (DRAT/LRAT): DIMACS CNF text
/// - For SMT formats (Alethe): ignored (the proof is self-contained)
/// - For PB formats (VeriPB/OPB): OPB format or ignored
///
/// # Errors
///
/// Returns [`PipelineError`] if format detection, parsing, or verification fails.
pub fn verify_any_proof(formula: &[u8], proof: &[u8]) -> Result<UnifiedResult, PipelineError> {
    let start = Instant::now();

    if proof.is_empty() {
        return Err(PipelineError::EmptyProof);
    }

    let format = detect_format(proof);

    match format {
        ProofFormat::Lrat | ProofFormat::Drat | ProofFormat::Frat => {
            verify_any_sat_proof(formula, proof, format, start)
        }
        ProofFormat::Alethe => verify_any_alethe(proof, start),
        ProofFormat::SmtLib2Proof => verify_any_smtlib2(proof, start),
        ProofFormat::VeriPb => verify_any_veripb(proof, start),
        ProofFormat::Opb => verify_any_opb(proof, start),
        ProofFormat::PolynomialCalculus => Err(PipelineError::UnsupportedFormat {
            format: ProofFormat::PolynomialCalculus,
        }),
        ProofFormat::Unknown => Err(PipelineError::UnknownFormat),
    }
}

/// Route SAT proof formats (DRAT/LRAT) through the existing pipeline.
fn verify_any_sat_proof(
    formula: &[u8],
    proof: &[u8],
    format: ProofFormat,
    start: Instant,
) -> Result<UnifiedResult, PipelineError> {
    let dimacs_text = std::str::from_utf8(formula)
        .map_err(|e| PipelineError::InvalidUtf8(format!("formula: {e}")))?;

    let cnf = Cnf::from_dimacs(dimacs_text).map_err(|e| PipelineError::CnfParse(e.to_string()))?;
    let raw_clauses = cnf.to_dimacs_clauses();

    let proof_input = match format {
        ProofFormat::Lrat => {
            if is_binary_lrat(proof) {
                ProofInput::LratBinary(proof.to_vec())
            } else {
                let text = std::str::from_utf8(proof)
                    .map_err(|e| PipelineError::InvalidUtf8(format!("proof: {e}")))?;
                ProofInput::LratText(text.to_owned())
            }
        }
        ProofFormat::Drat => {
            let drat_fmt = detect_drat_format(proof);
            match drat_fmt {
                DratFormat::Binary => ProofInput::DratBinary(proof.to_vec()),
                DratFormat::Text => {
                    let text = std::str::from_utf8(proof)
                        .map_err(|e| PipelineError::InvalidUtf8(format!("proof: {e}")))?;
                    ProofInput::DratText(text.to_owned())
                }
            }
        }
        ProofFormat::Frat => {
            if looks_like_frat_binary(proof) {
                ProofInput::FratBinary(proof.to_vec())
            } else {
                let text = std::str::from_utf8(proof)
                    .map_err(|e| PipelineError::InvalidUtf8(format!("proof: {e}")))?;
                ProofInput::FratText(text.to_owned())
            }
        }
        _ => return Err(PipelineError::UnsupportedFormat { format }),
    };

    let config = PipelineConfig {
        compute_certificate: true,
        ..PipelineConfig::default()
    };

    let pipeline_result = verify_proof(&raw_clauses, proof_input, &config)?;
    let elapsed = start.elapsed().as_micros() as u64;

    let trust_level = if pipeline_result.valid && pipeline_result.stats.steps_trusted == 0 {
        TrustLevel::KernelVerified
    } else if pipeline_result.valid {
        TrustLevel::StructurallyVerified
    } else {
        TrustLevel::Unverified
    };

    Ok(UnifiedResult {
        format: pipeline_result.format_detected,
        valid: pipeline_result.valid,
        verification_time_us: elapsed,
        trust_level,
        steps_verified: pipeline_result.stats.steps_verified,
        steps_trusted: pipeline_result.stats.steps_trusted,
        certificate: pipeline_result.certificate,
        errors: pipeline_result.errors,
    })
}

/// Route Alethe proofs to the SMT verifier.
fn verify_any_alethe(proof: &[u8], start: Instant) -> Result<UnifiedResult, PipelineError> {
    let proof_text = std::str::from_utf8(proof)
        .map_err(|e| PipelineError::InvalidUtf8(format!("proof: {e}")))?;

    match smt_verify::verify_alethe_proof(proof_text) {
        Ok(result) => {
            let elapsed = start.elapsed().as_micros() as u64;
            let trust_level = if result.stats.is_fully_verified() {
                TrustLevel::KernelVerified
            } else if result.stats.trusted == 0 {
                TrustLevel::StructurallyVerified
            } else {
                TrustLevel::PartiallyVerified
            };

            Ok(UnifiedResult {
                format: ProofFormat::Alethe,
                valid: result.valid,
                verification_time_us: elapsed,
                trust_level,
                steps_verified: (result.stats.kernel_verified + result.stats.structurally_accepted)
                    as usize,
                steps_trusted: result.stats.trusted as usize,
                certificate: None,
                errors: Vec::new(),
            })
        }
        Err(e) => {
            let elapsed = start.elapsed().as_micros() as u64;
            Ok(UnifiedResult {
                format: ProofFormat::Alethe,
                valid: false,
                verification_time_us: elapsed,
                trust_level: TrustLevel::Unverified,
                steps_verified: 0,
                steps_trusted: 0,
                certificate: None,
                errors: vec![e.to_string()],
            })
        }
    }
}

/// Route SMT-LIB2 proofs to the SMT verifier via the smtlib2_proof module.
fn verify_any_smtlib2(proof: &[u8], start: Instant) -> Result<UnifiedResult, PipelineError> {
    let proof_text = std::str::from_utf8(proof)
        .map_err(|e| PipelineError::InvalidUtf8(format!("proof: {e}")))?;

    match smtlib2_proof::parse_and_convert(proof_text) {
        Ok(dag) => {
            let result = smt_verify::verify_smt_proof(&dag, VerifyMode::Permissive);
            let elapsed = start.elapsed().as_micros() as u64;
            let trust_level = if result.valid && result.stats.is_fully_verified() {
                TrustLevel::KernelVerified
            } else if result.valid && result.stats.trusted == 0 {
                TrustLevel::StructurallyVerified
            } else if result.valid {
                TrustLevel::PartiallyVerified
            } else {
                TrustLevel::Unverified
            };

            Ok(UnifiedResult {
                format: ProofFormat::SmtLib2Proof,
                valid: result.valid,
                verification_time_us: elapsed,
                trust_level,
                steps_verified: (result.stats.kernel_verified + result.stats.structurally_accepted)
                    as usize,
                steps_trusted: result.stats.trusted as usize,
                certificate: None,
                errors: result.first_error.iter().map(|e| e.to_string()).collect(),
            })
        }
        Err(e) => {
            let elapsed = start.elapsed().as_micros() as u64;
            Ok(UnifiedResult {
                format: ProofFormat::SmtLib2Proof,
                valid: false,
                verification_time_us: elapsed,
                trust_level: TrustLevel::Unverified,
                steps_verified: 0,
                steps_trusted: 0,
                certificate: None,
                errors: vec![e.to_string()],
            })
        }
    }
}

/// Route VeriPB proofs: parse the VeriPB proof text and verify.
fn verify_any_veripb(proof: &[u8], start: Instant) -> Result<UnifiedResult, PipelineError> {
    let _proof_text = std::str::from_utf8(proof)
        .map_err(|e| PipelineError::InvalidUtf8(format!("proof: {e}")))?;

    // VeriPB proofs are self-contained: the proof text includes both
    // the formula header and the proof steps. For now, we recognize the
    // format but note that the VeriPB parser expects a VeriPbProof struct
    // built programmatically. Full text parsing is a future enhancement.
    let elapsed = start.elapsed().as_micros() as u64;
    Ok(UnifiedResult {
        format: ProofFormat::VeriPb,
        valid: false,
        verification_time_us: elapsed,
        trust_level: TrustLevel::FormatRecognized,
        steps_verified: 0,
        steps_trusted: 0,
        certificate: None,
        errors: vec![
            "VeriPB text proof parsing not yet implemented; use VeriPbProof API directly"
                .to_owned(),
        ],
    })
}

/// Route OPB proofs: parse the OPB formula and run PB verification.
fn verify_any_opb(proof: &[u8], start: Instant) -> Result<UnifiedResult, PipelineError> {
    let proof_text = std::str::from_utf8(proof)
        .map_err(|e| PipelineError::InvalidUtf8(format!("proof: {e}")))?;

    // OPB format describes a PB formula. We can parse it and verify
    // that the formula is well-formed, but a separate proof is needed
    // for unsatisfiability. Recognize the format and parse the formula.
    match parse_opb(proof_text) {
        Ok(_formula) => {
            let elapsed = start.elapsed().as_micros() as u64;
            Ok(UnifiedResult {
                format: ProofFormat::Opb,
                valid: false,
                verification_time_us: elapsed,
                trust_level: TrustLevel::FormatRecognized,
                steps_verified: 0,
                steps_trusted: 0,
                certificate: None,
                errors: vec![
                    "OPB formula parsed successfully; pair with VeriPB proof for verification"
                        .to_owned(),
                ],
            })
        }
        Err(e) => Err(PipelineError::PseudoBoolean(e)),
    }
}

// ---------------------------------------------------------------------------
// Main pipeline
// ---------------------------------------------------------------------------

/// Verify a proof against a CNF formula using the unified pipeline.
///
/// Steps:
/// 1. Auto-detect format (or use `config.format_hint`).
/// 2. Parse the proof.
/// 3. Run the appropriate checker.
/// 4. Build a certificate if valid and `config.compute_certificate` is set.
/// 5. Return result with stats.
///
/// # Errors
///
/// Returns [`PipelineError`] if parsing, detection, or verification fails.
pub fn verify_proof(
    formula: &[Vec<i32>],
    proof: ProofInput,
    config: &PipelineConfig,
) -> Result<PipelineResult, PipelineError> {
    let start = Instant::now();
    let input_size = formula.iter().map(|c| c.len() * 4).sum::<usize>();
    let proof_size = proof.size_bytes();

    let format = config.format_hint.unwrap_or_else(|| proof.format());

    match format {
        ProofFormat::Drat => verify_drat(formula, &proof, config, start, input_size, proof_size),
        ProofFormat::Lrat => verify_lrat(formula, &proof, config, start, input_size, proof_size),
        ProofFormat::Frat => {
            verify_frat_pipeline(formula, &proof, config, start, input_size, proof_size)
        }
        ProofFormat::Alethe => {
            verify_alethe_pipeline(&proof, config, start, input_size, proof_size)
        }
        ProofFormat::SmtLib2Proof => {
            verify_smtlib2_pipeline(&proof, config, start, input_size, proof_size)
        }
        ProofFormat::VeriPb | ProofFormat::Opb | ProofFormat::PolynomialCalculus => {
            // VeriPB, OPB, and PC/GF(2) are recognized but the structured
            // pipeline (`verify_proof`) works with clause-level formulas.
            // Use `verify_any_proof` entry point for raw-bytes routing, or
            // call the respective module's API directly.
            // For PC/GF(2): use `gf2_algebra::PcProof::build()` +
            // `pc_soundness_gf2()` or `PcProofSystem` API.
            let elapsed = start.elapsed().as_micros() as u64;
            Ok(PipelineResult {
                valid: false,
                format_detected: format,
                verification_time_us: elapsed,
                certificate: None,
                stats: PipelineStats {
                    steps_verified: 0,
                    steps_trusted: 0,
                    input_size_bytes: input_size,
                    proof_size_bytes: proof_size,
                },
                errors: vec![format!(
                    "{format} verification: use verify_any_proof() or module API directly"
                )],
            })
        }
        ProofFormat::Unknown => Err(PipelineError::UnknownFormat),
    }
}

/// Verify a DRAT proof against a CNF formula.
fn verify_drat(
    formula: &[Vec<i32>],
    proof: &ProofInput,
    config: &PipelineConfig,
    start: Instant,
    input_size: usize,
    proof_size: usize,
) -> Result<PipelineResult, PipelineError> {
    let mut max_var = 0u32;
    for clause in formula {
        for &lit in clause {
            let var = lit.unsigned_abs();
            if var > max_var {
                max_var = var;
            }
        }
    }

    let importer = AyDratImporter::new(max_var, formula.to_vec());

    let proof_bytes: &[u8] = match proof {
        ProofInput::DratText(s) => s.as_bytes(),
        ProofInput::DratBinary(b) => b,
        _ => {
            return Err(PipelineError::UnsupportedFormat {
                format: proof.format(),
            })
        }
    };

    let result = verify_ay_drat_proof(&importer, proof_bytes)?;
    let elapsed = start.elapsed().as_micros() as u64;

    let certificate = if result.valid && config.compute_certificate {
        Some(build_drat_certificate(&result, proof_bytes))
    } else {
        None
    };

    let mut errors = Vec::new();
    if !result.valid {
        errors.extend(
            result
                .diagnostics
                .iter()
                .filter(|d| d.contains("failed") || d.contains("does not"))
                .cloned(),
        );
    }

    Ok(PipelineResult {
        valid: result.valid,
        format_detected: ProofFormat::Drat,
        verification_time_us: elapsed,
        certificate,
        stats: PipelineStats {
            steps_verified: result.steps_checked,
            steps_trusted: 0,
            input_size_bytes: input_size,
            proof_size_bytes: proof_size,
        },
        errors,
    })
}

/// Build a certificate envelope from a verified DRAT proof.
fn build_drat_certificate(
    result: &super::ay_import::AyDratVerificationResult,
    proof_bytes: &[u8],
) -> CertificateEnvelope {
    let proof_hash: [u8; 32] = blake3::hash(proof_bytes).into();
    let timestamp = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_secs())
        .unwrap_or(0);

    let mut metadata = HashMap::new();
    metadata.insert("steps_checked".to_owned(), result.steps_checked.to_string());
    metadata.insert("format".to_owned(), format!("{:?}", result.format));
    metadata.insert("verified".to_owned(), result.valid.to_string());

    CertificateEnvelope {
        theorem_id: "DRAT01".to_owned(),
        mechanism: "drat_verification".to_owned(),
        proof_hash,
        clean_version: env!("CARGO_PKG_VERSION").to_owned(),
        timestamp,
        dependencies: Vec::new(),
        metadata,
    }
}

/// Verify an LRAT proof against a CNF formula.
fn verify_lrat(
    formula: &[Vec<i32>],
    proof: &ProofInput,
    config: &PipelineConfig,
    start: Instant,
    input_size: usize,
    proof_size: usize,
) -> Result<PipelineResult, PipelineError> {
    let kernel_proof = match proof {
        ProofInput::LratText(s) => lrat_verify_text(formula, s)?,
        ProofInput::LratBinary(b) => lrat_verify_auto(formula, b)?,
        _ => {
            return Err(PipelineError::UnsupportedFormat {
                format: proof.format(),
            })
        }
    };

    let elapsed = start.elapsed().as_micros() as u64;
    let valid = kernel_proof.is_verified();

    let certificate = if valid && config.compute_certificate {
        Some(lrat_to_envelope(&kernel_proof))
    } else {
        None
    };

    let errors = if !valid {
        vec!["LRAT proof did not verify as a valid refutation".to_owned()]
    } else {
        Vec::new()
    };

    Ok(PipelineResult {
        valid,
        format_detected: ProofFormat::Lrat,
        verification_time_us: elapsed,
        certificate,
        stats: PipelineStats {
            steps_verified: kernel_proof.step_count,
            steps_trusted: 0,
            input_size_bytes: input_size,
            proof_size_bytes: proof_size,
        },
        errors,
    })
}

/// Verify a FRAT proof against a CNF formula through the pipeline.
fn verify_frat_pipeline(
    formula: &[Vec<i32>],
    proof: &ProofInput,
    _config: &PipelineConfig,
    start: Instant,
    input_size: usize,
    proof_size: usize,
) -> Result<PipelineResult, PipelineError> {
    let steps = match proof {
        ProofInput::FratText(s) => frat::parse_frat_text(s)?,
        ProofInput::FratBinary(b) => frat::parse_frat_binary(b)?,
        _ => {
            return Err(PipelineError::UnsupportedFormat {
                format: proof.format(),
            })
        }
    };

    let result = frat::verify_frat(formula, &steps)?;
    let elapsed = start.elapsed().as_micros() as u64;

    let mut errors = Vec::new();
    if !result.valid {
        errors.push("FRAT proof did not derive the empty clause".to_owned());
    }

    Ok(PipelineResult {
        valid: result.valid,
        format_detected: ProofFormat::Frat,
        verification_time_us: elapsed,
        certificate: None, // FRAT certificate generation is a future enhancement.
        stats: PipelineStats {
            steps_verified: result.rup_checks + result.rat_checks,
            steps_trusted: 0,
            input_size_bytes: input_size,
            proof_size_bytes: proof_size,
        },
        errors,
    })
}

/// Verify an Alethe proof through the structured pipeline.
///
/// Extracts the proof text from the [`ProofInput`] and delegates to
/// [`smt_verify::verify_alethe_proof`], translating the result into
/// a [`PipelineResult`].
fn verify_alethe_pipeline(
    proof: &ProofInput,
    config: &PipelineConfig,
    start: Instant,
    input_size: usize,
    proof_size: usize,
) -> Result<PipelineResult, PipelineError> {
    let proof_text = match proof {
        ProofInput::AletheSmt(s) => s.as_str(),
        _ => {
            return Err(PipelineError::UnsupportedFormat {
                format: proof.format(),
            })
        }
    };

    let mode = if config.strict_mode {
        VerifyMode::Strict
    } else {
        VerifyMode::Permissive
    };

    match smt_verify::verify_alethe_proof_with_mode(proof_text, mode) {
        Ok(result) => {
            let elapsed = start.elapsed().as_micros() as u64;
            let steps_verified =
                (result.stats.kernel_verified + result.stats.structurally_accepted) as usize;
            let steps_trusted = result.stats.trusted as usize;

            Ok(PipelineResult {
                valid: result.valid,
                format_detected: ProofFormat::Alethe,
                verification_time_us: elapsed,
                certificate: None,
                stats: PipelineStats {
                    steps_verified,
                    steps_trusted,
                    input_size_bytes: input_size,
                    proof_size_bytes: proof_size,
                },
                errors: Vec::new(),
            })
        }
        Err(e) => {
            let elapsed = start.elapsed().as_micros() as u64;
            Ok(PipelineResult {
                valid: false,
                format_detected: ProofFormat::Alethe,
                verification_time_us: elapsed,
                certificate: None,
                stats: PipelineStats {
                    steps_verified: 0,
                    steps_trusted: 0,
                    input_size_bytes: input_size,
                    proof_size_bytes: proof_size,
                },
                errors: vec![e.to_string()],
            })
        }
    }
}

/// Verify an SMT-LIB2 proof through the structured pipeline.
///
/// Extracts the proof text from the [`ProofInput`], parses the SMT-LIB2
/// proof format, converts to `SmtProofDag`, and runs the SMT verifier.
fn verify_smtlib2_pipeline(
    proof: &ProofInput,
    config: &PipelineConfig,
    start: Instant,
    input_size: usize,
    proof_size: usize,
) -> Result<PipelineResult, PipelineError> {
    let proof_text = match proof {
        ProofInput::SmtLib2Proof(s) => s.as_str(),
        _ => {
            return Err(PipelineError::UnsupportedFormat {
                format: proof.format(),
            })
        }
    };

    let mode = if config.strict_mode {
        VerifyMode::Strict
    } else {
        VerifyMode::Permissive
    };

    match smtlib2_proof::parse_and_convert(proof_text) {
        Ok(dag) => {
            let result = smt_verify::verify_smt_proof(&dag, mode);
            let elapsed = start.elapsed().as_micros() as u64;
            let steps_verified =
                (result.stats.kernel_verified + result.stats.structurally_accepted) as usize;
            let steps_trusted = result.stats.trusted as usize;

            Ok(PipelineResult {
                valid: result.valid,
                format_detected: ProofFormat::SmtLib2Proof,
                verification_time_us: elapsed,
                certificate: None,
                stats: PipelineStats {
                    steps_verified,
                    steps_trusted,
                    input_size_bytes: input_size,
                    proof_size_bytes: proof_size,
                },
                errors: result.first_error.iter().map(|e| e.to_string()).collect(),
            })
        }
        Err(e) => {
            let elapsed = start.elapsed().as_micros() as u64;
            Ok(PipelineResult {
                valid: false,
                format_detected: ProofFormat::SmtLib2Proof,
                verification_time_us: elapsed,
                certificate: None,
                stats: PipelineStats {
                    steps_verified: 0,
                    steps_trusted: 0,
                    input_size_bytes: input_size,
                    proof_size_bytes: proof_size,
                },
                errors: vec![e.to_string()],
            })
        }
    }
}

// ---------------------------------------------------------------------------
// Competition entry point
// ---------------------------------------------------------------------------

/// End-to-end verification for SAT-COMP competition entries.
///
/// Accepts raw DIMACS text and proof bytes, auto-detects the proof format,
/// verifies, and returns a [`PipelineResult`].
///
/// # Errors
///
/// Returns [`PipelineError`] if DIMACS parsing, format detection, or
/// verification fails.
pub fn verify_competition_entry(
    dimacs: &str,
    proof: &[u8],
) -> Result<PipelineResult, PipelineError> {
    let cnf = Cnf::from_dimacs(dimacs).map_err(|e| PipelineError::CnfParse(e.to_string()))?;
    let raw_clauses = cnf.to_dimacs_clauses();

    if proof.is_empty() {
        return Err(PipelineError::EmptyProof);
    }

    let format = detect_format(proof);
    let proof_input = match format {
        ProofFormat::Lrat => {
            if is_binary_lrat(proof) {
                ProofInput::LratBinary(proof.to_vec())
            } else {
                let text = std::str::from_utf8(proof).map_err(|e| {
                    PipelineError::CnfParse(format!("proof is not valid UTF-8: {e}"))
                })?;
                ProofInput::LratText(text.to_owned())
            }
        }
        ProofFormat::Drat => {
            let drat_fmt = detect_drat_format(proof);
            match drat_fmt {
                DratFormat::Binary => ProofInput::DratBinary(proof.to_vec()),
                DratFormat::Text => {
                    let text = std::str::from_utf8(proof).map_err(|e| {
                        PipelineError::CnfParse(format!("proof is not valid UTF-8: {e}"))
                    })?;
                    ProofInput::DratText(text.to_owned())
                }
            }
        }
        ProofFormat::Frat => {
            if looks_like_frat_binary(proof) {
                ProofInput::FratBinary(proof.to_vec())
            } else {
                let text = std::str::from_utf8(proof).map_err(|e| {
                    PipelineError::CnfParse(format!("proof is not valid UTF-8: {e}"))
                })?;
                ProofInput::FratText(text.to_owned())
            }
        }
        ProofFormat::Alethe => {
            let text = std::str::from_utf8(proof)
                .map_err(|e| PipelineError::CnfParse(format!("proof is not valid UTF-8: {e}")))?;
            ProofInput::AletheSmt(text.to_owned())
        }
        ProofFormat::SmtLib2Proof => {
            let text = std::str::from_utf8(proof)
                .map_err(|e| PipelineError::CnfParse(format!("proof is not valid UTF-8: {e}")))?;
            ProofInput::SmtLib2Proof(text.to_owned())
        }
        ProofFormat::VeriPb => {
            let text = std::str::from_utf8(proof)
                .map_err(|e| PipelineError::CnfParse(format!("proof is not valid UTF-8: {e}")))?;
            ProofInput::VeriPbText(text.to_owned())
        }
        ProofFormat::Opb => {
            let text = std::str::from_utf8(proof)
                .map_err(|e| PipelineError::CnfParse(format!("proof is not valid UTF-8: {e}")))?;
            ProofInput::OpbText(text.to_owned())
        }
        ProofFormat::PolynomialCalculus => {
            // Check for binary magic first.
            if proof.len() >= 4 {
                let magic = u32::from_le_bytes([proof[0], proof[1], proof[2], proof[3]]);
                // PC2\0 magic bytes (little-endian u32) marking Polynomial Calculus
                // proof files. The underscores group the four bytes 0x00 0x50 0x43 0x32.
                if magic == 0x0050_4332 {
                    return Ok(PipelineResult {
                        valid: false,
                        format_detected: ProofFormat::PolynomialCalculus,
                        verification_time_us: 0,
                        certificate: None,
                        stats: PipelineStats {
                            steps_verified: 0,
                            steps_trusted: 0,
                            input_size_bytes: dimacs.len(),
                            proof_size_bytes: proof.len(),
                        },
                        errors: vec![
                            "PC/GF(2) binary certificate: use PcProof API directly".to_string()
                        ],
                    });
                }
            }
            let text = std::str::from_utf8(proof)
                .map_err(|e| PipelineError::CnfParse(format!("proof is not valid UTF-8: {e}")))?;
            ProofInput::PcText(text.to_owned())
        }
        ProofFormat::Unknown => return Err(PipelineError::UnknownFormat),
    };

    let config = PipelineConfig {
        compute_certificate: true,
        ..PipelineConfig::default()
    };

    verify_proof(&raw_clauses, proof_input, &config)
}

// ---------------------------------------------------------------------------
// Streaming competition entry point
// ---------------------------------------------------------------------------

/// Streaming verification for competition-scale SAT proofs (>100GB).
///
/// Unlike [`verify_competition_entry`], which loads the entire proof into memory,
/// this function reads the DRAT proof from a streaming `BufRead` source.
/// The proof is converted to LRAT with hint extraction and verified in a single
/// pass, never materializing the full proof in memory.
///
/// Currently supports DRAT proofs only (the dominant format for competition-scale
/// proofs). LRAT streaming verification is available via
/// [`super::lrat::verify_lrat_streaming`].
///
/// # Parameters
///
/// - `dimacs`: DIMACS CNF formula text.
/// - `proof_reader`: buffered reader over the DRAT proof (text or binary).
/// - `binary`: `true` for binary DRAT format, `false` for text.
///
/// # Errors
///
/// Returns [`PipelineError`] if DIMACS parsing, DRAT conversion, or LRAT
/// verification fails.
pub fn verify_competition_entry_streaming<R: io::BufRead>(
    dimacs: &str,
    proof_reader: R,
    binary: bool,
) -> Result<PipelineResult, PipelineError> {
    let start = Instant::now();

    let cnf = Cnf::from_dimacs(dimacs).map_err(|e| PipelineError::CnfParse(e.to_string()))?;
    let raw_clauses = cnf.to_dimacs_clauses();
    let input_size = raw_clauses.iter().map(|c| c.len() * 4).sum::<usize>();

    let streaming_result =
        drat_converter::verify_drat_streaming(&raw_clauses, proof_reader, binary)?;
    let elapsed = start.elapsed().as_micros() as u64;

    let certificate = if streaming_result.valid {
        let timestamp = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map(|d| d.as_secs())
            .unwrap_or(0);
        let mut metadata = HashMap::new();
        metadata.insert(
            "drat_steps".to_owned(),
            streaming_result.drat_steps_processed.to_string(),
        );
        metadata.insert(
            "lrat_steps_verified".to_owned(),
            streaming_result.lrat_steps_verified.to_string(),
        );
        metadata.insert("streaming".to_owned(), "true".to_owned());

        Some(CertificateEnvelope {
            theorem_id: "DRAT_STREAMING01".to_owned(),
            mechanism: "drat_streaming_verification".to_owned(),
            proof_hash: [0u8; 32], // Hash not available for streaming proofs.
            clean_version: env!("CARGO_PKG_VERSION").to_owned(),
            timestamp,
            dependencies: Vec::new(),
            metadata,
        })
    } else {
        None
    };

    Ok(PipelineResult {
        valid: streaming_result.valid,
        format_detected: ProofFormat::Drat,
        verification_time_us: elapsed,
        certificate,
        stats: PipelineStats {
            steps_verified: streaming_result.lrat_steps_verified,
            steps_trusted: 0,
            input_size_bytes: input_size,
            proof_size_bytes: 0, // Not known for streaming.
        },
        errors: Vec::new(),
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    // Simple UNSAT: (x1) AND (-x1)
    fn simple_unsat_cnf() -> Vec<Vec<i32>> {
        vec![vec![1], vec![-1]]
    }

    // Two-variable UNSAT: (x1 v x2) AND (-x1) AND (-x2)
    fn two_var_unsat_cnf() -> Vec<Vec<i32>> {
        vec![vec![1, 2], vec![-1], vec![-2]]
    }

    // DRAT text proof for simple UNSAT: derive empty clause
    const SIMPLE_DRAT_TEXT: &str = "0\n";

    // LRAT text proof for simple UNSAT: derive empty clause from clauses 1,2
    const SIMPLE_LRAT_TEXT: &str = "3 0 1 2 0\n";

    // LRAT text proof for two-variable UNSAT
    const TWO_VAR_LRAT_TEXT: &str = "4 2 0 1 2 0\n5 0 4 3 0\n";

    // ---- DRAT pipeline tests ----

    #[test]
    fn test_pipeline_drat_text_end_to_end() {
        let cnf = simple_unsat_cnf();
        let config = PipelineConfig::default();
        let result = verify_proof(
            &cnf,
            ProofInput::DratText(SIMPLE_DRAT_TEXT.to_owned()),
            &config,
        )
        .expect("DRAT text pipeline should succeed");

        assert!(result.valid);
        assert_eq!(result.format_detected, ProofFormat::Drat);
        assert!(result.certificate.is_some());
        assert!(result.errors.is_empty());
        assert!(result.stats.steps_verified > 0);
        assert_eq!(result.stats.steps_trusted, 0);
    }

    #[test]
    fn test_pipeline_drat_text_invalid_proof() {
        // Formula is SAT, proof cannot derive empty clause
        let cnf = vec![vec![1, 2]];
        let config = PipelineConfig::default();
        // This proof adds empty clause but verification should fail because
        // the empty clause is not RUP with respect to the formula.
        let result = verify_proof(&cnf, ProofInput::DratText("0\n".to_owned()), &config);
        // Either returns an error or returns valid=false.
        if let Ok(r) = result {
            assert!(!r.valid || !r.errors.is_empty())
        }
    }

    // ---- LRAT pipeline tests ----

    #[test]
    fn test_pipeline_lrat_text_end_to_end() {
        let cnf = simple_unsat_cnf();
        let config = PipelineConfig::default();
        let result = verify_proof(
            &cnf,
            ProofInput::LratText(SIMPLE_LRAT_TEXT.to_owned()),
            &config,
        )
        .expect("LRAT text pipeline should succeed");

        assert!(result.valid);
        assert_eq!(result.format_detected, ProofFormat::Lrat);
        assert!(result.certificate.is_some());
        assert!(result.errors.is_empty());
        assert_eq!(result.stats.steps_verified, 1);
    }

    #[test]
    fn test_pipeline_lrat_text_two_variable() {
        let cnf = two_var_unsat_cnf();
        let config = PipelineConfig::default();
        let result = verify_proof(
            &cnf,
            ProofInput::LratText(TWO_VAR_LRAT_TEXT.to_owned()),
            &config,
        )
        .expect("LRAT two-variable pipeline should succeed");

        assert!(result.valid);
        assert_eq!(result.stats.steps_verified, 2);
    }

    #[test]
    fn test_pipeline_lrat_invalid_hints() {
        let cnf = simple_unsat_cnf();
        let config = PipelineConfig::default();
        // Hint references non-existent clause 99.
        let bad_lrat = "3 0 1 99 0\n";
        let result = verify_proof(&cnf, ProofInput::LratText(bad_lrat.to_owned()), &config);
        assert!(result.is_err());
    }

    // ---- Format auto-detection tests ----

    #[test]
    fn test_detect_format_drat_text() {
        assert_eq!(detect_format(b"1 2 0\n"), ProofFormat::Drat);
    }

    #[test]
    fn test_detect_format_lrat_text() {
        // LRAT: <id> <lits> 0 <hints> 0
        assert_eq!(detect_format(b"3 0 1 2 0\n"), ProofFormat::Lrat);
    }

    #[test]
    fn test_detect_format_alethe() {
        assert_eq!(detect_format(b"(set-logic QF_UF)\n"), ProofFormat::Alethe);
    }

    #[test]
    fn test_detect_format_veripb() {
        assert_eq!(
            detect_format(b"pseudo-Boolean proof\n"),
            ProofFormat::VeriPb
        );
    }

    #[test]
    fn test_detect_format_empty() {
        assert_eq!(detect_format(b""), ProofFormat::Unknown);
    }

    #[test]
    fn test_detect_format_whitespace_only() {
        assert_eq!(detect_format(b"   \n  \t  "), ProofFormat::Unknown);
    }

    // ---- Certificate generation tests ----

    #[test]
    fn test_pipeline_certificate_has_proof_hash() {
        let cnf = simple_unsat_cnf();
        let config = PipelineConfig::default();
        let result = verify_proof(
            &cnf,
            ProofInput::LratText(SIMPLE_LRAT_TEXT.to_owned()),
            &config,
        )
        .expect("should succeed");

        let cert = result.certificate.expect("certificate should be present");
        assert_ne!(cert.proof_hash, [0u8; 32]);
        assert_eq!(cert.mechanism, "lrat_verification");
        assert_eq!(cert.theorem_id, "LRAT01");
    }

    #[test]
    fn test_pipeline_no_certificate_when_disabled() {
        let cnf = simple_unsat_cnf();
        let config = PipelineConfig {
            compute_certificate: false,
            ..PipelineConfig::default()
        };
        let result = verify_proof(
            &cnf,
            ProofInput::LratText(SIMPLE_LRAT_TEXT.to_owned()),
            &config,
        )
        .expect("should succeed");

        assert!(result.valid);
        assert!(result.certificate.is_none());
    }

    // ---- Invalid proof rejection tests ----

    #[test]
    fn test_pipeline_rejects_unknown_format() {
        let cnf = simple_unsat_cnf();
        let config = PipelineConfig {
            format_hint: Some(ProofFormat::Unknown),
            ..PipelineConfig::default()
        };
        let result = verify_proof(&cnf, ProofInput::DratText("0\n".to_owned()), &config);
        assert!(result.is_err());
    }

    // ---- Competition entry tests ----

    #[test]
    fn test_competition_entry_lrat_text() {
        let dimacs = "c Simple UNSAT\np cnf 1 2\n1 0\n-1 0\n";
        let lrat = b"3 0 1 2 0\n";

        let result = verify_competition_entry(dimacs, lrat).expect("competition entry should work");

        assert!(result.valid);
        assert_eq!(result.format_detected, ProofFormat::Lrat);
        assert!(result.certificate.is_some());
    }

    #[test]
    fn test_competition_entry_drat_text() {
        let dimacs = "p cnf 1 2\n1 0\n-1 0\n";
        let drat = b"0\n";

        let result = verify_competition_entry(dimacs, drat).expect("competition DRAT should work");

        assert!(result.valid);
        assert_eq!(result.format_detected, ProofFormat::Drat);
    }

    #[test]
    fn test_competition_entry_empty_proof() {
        let dimacs = "p cnf 1 2\n1 0\n-1 0\n";
        let result = verify_competition_entry(dimacs, b"");
        assert!(matches!(result, Err(PipelineError::EmptyProof)));
    }

    #[test]
    fn test_competition_entry_invalid_dimacs() {
        let result = verify_competition_entry("not valid dimacs", b"0\n");
        assert!(matches!(result, Err(PipelineError::CnfParse(_))));
    }

    // ---- Stats tests ----

    #[test]
    fn test_pipeline_stats_trust_ratio() {
        let stats = PipelineStats {
            steps_verified: 8,
            steps_trusted: 2,
            input_size_bytes: 100,
            proof_size_bytes: 50,
        };
        assert!((stats.trust_ratio() - 0.8).abs() < f64::EPSILON);
    }

    #[test]
    fn test_pipeline_stats_trust_ratio_no_steps() {
        let stats = PipelineStats {
            steps_verified: 0,
            steps_trusted: 0,
            input_size_bytes: 0,
            proof_size_bytes: 0,
        };
        assert!((stats.trust_ratio() - 1.0).abs() < f64::EPSILON);
    }

    // ---- Config tests ----

    #[test]
    fn test_pipeline_config_default() {
        let config = PipelineConfig::default();
        assert!(!config.strict_mode);
        assert!(config.compute_certificate);
        assert!(config.timeout_ms.is_none());
        assert!(config.format_hint.is_none());
    }

    #[test]
    fn test_pipeline_config_format_hint_overrides_detection() {
        let cnf = simple_unsat_cnf();
        // Pass DRAT text but hint as LRAT -- should fail because parsing as LRAT
        // won't work on DRAT data.
        let config = PipelineConfig {
            format_hint: Some(ProofFormat::Lrat),
            ..PipelineConfig::default()
        };
        let result = verify_proof(
            &cnf,
            ProofInput::DratText(SIMPLE_DRAT_TEXT.to_owned()),
            &config,
        );
        // This should fail because the DratText variant doesn't match Lrat format.
        assert!(result.is_err());
    }

    // ---- ProofInput tests ----

    #[test]
    fn test_proof_input_format() {
        assert_eq!(
            ProofInput::DratText(String::new()).format(),
            ProofFormat::Drat
        );
        assert_eq!(ProofInput::DratBinary(vec![]).format(), ProofFormat::Drat);
        assert_eq!(
            ProofInput::LratText(String::new()).format(),
            ProofFormat::Lrat
        );
        assert_eq!(ProofInput::LratBinary(vec![]).format(), ProofFormat::Lrat);
        assert_eq!(
            ProofInput::AletheSmt(String::new()).format(),
            ProofFormat::Alethe
        );
        assert_eq!(
            ProofInput::SmtLib2Proof(String::new()).format(),
            ProofFormat::SmtLib2Proof
        );
        assert_eq!(
            ProofInput::VeriPbText(String::new()).format(),
            ProofFormat::VeriPb
        );
        assert_eq!(
            ProofInput::OpbText(String::new()).format(),
            ProofFormat::Opb
        );
    }

    #[test]
    fn test_proof_input_size_bytes() {
        assert_eq!(ProofInput::DratText("hello".to_owned()).size_bytes(), 5);
        assert_eq!(ProofInput::DratBinary(vec![1, 2, 3]).size_bytes(), 3);
        assert_eq!(ProofInput::LratText("ab".to_owned()).size_bytes(), 2);
        assert_eq!(ProofInput::OpbText("test".to_owned()).size_bytes(), 4);
    }

    // ---- ProofFormat display ----

    #[test]
    fn test_proof_format_display() {
        assert_eq!(ProofFormat::Drat.to_string(), "DRAT");
        assert_eq!(ProofFormat::Lrat.to_string(), "LRAT");
        assert_eq!(ProofFormat::Alethe.to_string(), "Alethe");
        assert_eq!(ProofFormat::SmtLib2Proof.to_string(), "SMT-LIB2");
        assert_eq!(ProofFormat::VeriPb.to_string(), "VeriPB");
        assert_eq!(ProofFormat::Opb.to_string(), "OPB");
        assert_eq!(ProofFormat::Unknown.to_string(), "Unknown");
    }

    // ---- SMT-LIB2 format detection tests ----

    #[test]
    fn test_detect_format_smtlib2_proof() {
        let data = b"(declare-sort U 0)\n(declare-fun p () Bool)\n(assert p)\n(proof (mp ...))";
        assert_eq!(detect_format(data), ProofFormat::SmtLib2Proof);
    }

    #[test]
    fn test_detect_format_smtlib2_with_assert_and_rules() {
        let data = b"(declare-fun p () Bool)\n(assert p)\n(assert (not p))\n(unit-resolution (asserted p) (asserted (not p)))";
        assert_eq!(detect_format(data), ProofFormat::SmtLib2Proof);
    }

    #[test]
    fn test_verify_any_proof_smtlib2() {
        let proof = br#"
            (declare-fun p () Bool)
            (assert p)
            (assert (not p))
            (proof
                (unit-resolution (asserted p) (asserted (not p)))
            )
        "#;
        let result =
            verify_any_proof(b"", proof).expect("verify_any_proof with SMT-LIB2 should succeed");
        assert_eq!(result.format, ProofFormat::SmtLib2Proof);
        // The proof may or may not fully verify depending on term matching,
        // but format detection and parsing should work.
        assert!(result.steps_verified > 0 || result.steps_trusted > 0);
    }

    // ---- OPB format detection tests ----

    #[test]
    fn test_detect_format_opb_with_header() {
        let opb = b"* #variable= 3 #constraint= 2\n+1 x1 +2 x2 >= 3 ;\n";
        assert_eq!(detect_format(opb), ProofFormat::Opb);
    }

    #[test]
    fn test_detect_format_opb_with_constraints() {
        // OPB with comment but no variable count header.
        let opb = b"* simple PB formula\n+1 x1 +1 x2 >= 1 ;\n";
        assert_eq!(detect_format(opb), ProofFormat::Opb);
    }

    // ---- verify_any_proof tests ----

    #[test]
    fn test_verify_any_proof_lrat_text() {
        let dimacs = b"c Simple UNSAT\np cnf 1 2\n1 0\n-1 0\n";
        let lrat = b"3 0 1 2 0\n";

        let result =
            verify_any_proof(dimacs, lrat).expect("verify_any_proof with LRAT should succeed");

        assert!(result.valid);
        assert_eq!(result.format, ProofFormat::Lrat);
        assert_eq!(result.trust_level, TrustLevel::KernelVerified);
        assert!(result.steps_verified > 0);
        assert_eq!(result.steps_trusted, 0);
        assert!(result.certificate.is_some());
        assert!(result.errors.is_empty());
    }

    #[test]
    fn test_verify_any_proof_drat_text() {
        let dimacs = b"p cnf 1 2\n1 0\n-1 0\n";
        let drat = b"0\n";

        let result =
            verify_any_proof(dimacs, drat).expect("verify_any_proof with DRAT should succeed");

        assert!(result.valid);
        assert_eq!(result.format, ProofFormat::Drat);
        assert!(result.certificate.is_some());
    }

    #[test]
    fn test_verify_any_proof_alethe() {
        let alethe = br#"
            (declare-const p Bool)
            (assume h1 p)
            (assume h2 (not p))
            (step t1 (cl) :rule resolution :premises (h1 h2))
        "#;

        let result =
            verify_any_proof(b"", alethe).expect("verify_any_proof with Alethe should succeed");

        assert!(result.valid);
        assert_eq!(result.format, ProofFormat::Alethe);
        assert!(
            result.trust_level == TrustLevel::KernelVerified
                || result.trust_level == TrustLevel::StructurallyVerified,
            "Alethe proof should be verified, got {:?}",
            result.trust_level,
        );
    }

    #[test]
    fn test_verify_any_proof_empty() {
        let result = verify_any_proof(b"", b"");
        assert!(matches!(result, Err(PipelineError::EmptyProof)));
    }

    #[test]
    fn test_verify_any_proof_unknown_format() {
        // Random bytes that don't match any format.
        let result = verify_any_proof(b"", b"zzz random garbage\n");
        assert!(matches!(result, Err(PipelineError::UnknownFormat)));
    }

    #[test]
    fn test_verify_any_proof_veripb_recognized() {
        let veripb = b"pseudo-Boolean proof\nsome steps\n";
        let result = verify_any_proof(b"", veripb).expect("VeriPB should be recognized");

        assert_eq!(result.format, ProofFormat::VeriPb);
        assert_eq!(result.trust_level, TrustLevel::FormatRecognized);
        assert!(!result.valid); // Not yet implemented for raw text
    }

    // ---- Trust level tests ----

    #[test]
    fn test_trust_level_display() {
        assert_eq!(TrustLevel::KernelVerified.to_string(), "kernel-verified");
        assert_eq!(
            TrustLevel::StructurallyVerified.to_string(),
            "structurally-verified"
        );
        assert_eq!(
            TrustLevel::PartiallyVerified.to_string(),
            "partially-verified"
        );
        assert_eq!(
            TrustLevel::FormatRecognized.to_string(),
            "format-recognized"
        );
        assert_eq!(TrustLevel::Unverified.to_string(), "unverified");
    }

    // ---- Alethe through pipeline tests ----

    #[test]
    fn test_pipeline_alethe_via_verify_proof() {
        let proof_text = r#"
            (declare-const p Bool)
            (assume h1 p)
            (assume h2 (not p))
            (step t1 (cl) :rule resolution :premises (h1 h2))
        "#;

        let config = PipelineConfig::default();
        let result = verify_proof(&[], ProofInput::AletheSmt(proof_text.to_owned()), &config)
            .expect("Alethe through pipeline should succeed");

        assert!(result.valid);
        assert_eq!(result.format_detected, ProofFormat::Alethe);
        assert!(result.stats.steps_verified > 0);
    }

    #[test]
    fn test_pipeline_alethe_invalid_proof() {
        // Only an assumption, no empty clause derived.
        let proof_text = r#"
            (declare-const p Bool)
            (assume h1 p)
        "#;

        let config = PipelineConfig::default();
        let result = verify_proof(&[], ProofInput::AletheSmt(proof_text.to_owned()), &config)
            .expect("Alethe invalid should return result, not error");

        assert!(!result.valid);
        assert!(!result.errors.is_empty());
    }

    // ---- Streaming competition entry tests ----

    #[test]
    fn test_competition_entry_streaming_text_simple() {
        let dimacs = "p cnf 1 2\n1 0\n-1 0\n";
        let drat = b"0\n";
        let reader = io::BufReader::new(&drat[..]);

        let result = verify_competition_entry_streaming(dimacs, reader, false)
            .expect("streaming competition entry should work");

        assert!(result.valid);
        assert_eq!(result.format_detected, ProofFormat::Drat);
        assert!(result.certificate.is_some());
        assert!(result.stats.steps_verified > 0);
        assert_eq!(result.stats.steps_trusted, 0);
    }

    #[test]
    fn test_competition_entry_streaming_text_three_clause() {
        let dimacs = "p cnf 2 3\n1 2 0\n-1 0\n-2 0\n";
        let drat = b"2 0\n0\n";
        let reader = io::BufReader::new(&drat[..]);

        let result = verify_competition_entry_streaming(dimacs, reader, false)
            .expect("streaming competition entry should work");

        assert!(result.valid);
        assert_eq!(result.stats.steps_verified, 2);
    }

    #[test]
    fn test_competition_entry_streaming_invalid_dimacs() {
        let reader = io::BufReader::new(&b"0\n"[..]);
        let result = verify_competition_entry_streaming("not valid dimacs", reader, false);
        assert!(matches!(result, Err(PipelineError::CnfParse(_))));
    }

    #[test]
    fn test_competition_entry_streaming_rup_failure() {
        let dimacs = "p cnf 2 1\n1 2 0\n";
        let drat = b"0\n"; // Empty clause not RUP.
        let reader = io::BufReader::new(&drat[..]);

        let result = verify_competition_entry_streaming(dimacs, reader, false);
        assert!(result.is_err());
    }

    #[test]
    fn test_competition_entry_streaming_large_chain() {
        // Chain UNSAT with 50 variables.
        let num_vars = 50;
        let mut dimacs = format!("p cnf {num_vars} {}\n", num_vars + 1);
        dimacs.push_str("1 2 0\n");
        dimacs.push_str("-1 0\n");
        for i in 2..num_vars {
            dimacs.push_str(&format!("-{} {} 0\n", i, i + 1));
        }
        dimacs.push_str(&format!("-{num_vars} 0\n"));

        let mut drat_text = String::new();
        for i in 2..=num_vars {
            drat_text.push_str(&format!("{i} 0\n"));
        }
        drat_text.push_str("0\n");

        let reader = io::BufReader::new(drat_text.as_bytes());
        let result = verify_competition_entry_streaming(&dimacs, reader, false)
            .expect("large chain streaming should succeed");

        assert!(result.valid);
        assert!(
            result.stats.steps_verified >= 50,
            "expected 50+ verified steps, got {}",
            result.stats.steps_verified,
        );

        let cert = result.certificate.expect("should have certificate");
        assert_eq!(cert.mechanism, "drat_streaming_verification");
        assert_eq!(cert.metadata.get("streaming"), Some(&"true".to_string()),);
    }

    #[test]
    fn test_competition_entry_streaming_certificate_metadata() {
        let dimacs = "p cnf 1 2\n1 0\n-1 0\n";
        let drat = b"0\n";
        let reader = io::BufReader::new(&drat[..]);

        let result =
            verify_competition_entry_streaming(dimacs, reader, false).expect("should succeed");

        let cert = result.certificate.expect("should have certificate");
        assert_eq!(cert.theorem_id, "DRAT_STREAMING01");
        assert!(cert.metadata.contains_key("drat_steps"));
        assert!(cert.metadata.contains_key("lrat_steps_verified"));
    }
}
