// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Support helpers for the `clean verify proof` runners:
//!
//! * certificate emission (full Alethe SMT certificate for Alethe proofs,
//!   minimal hash-based certificate for every other format),
//! * LRAT-proof trimming,
//! * `--format` token parsing,
//! * the owned `OwnedProofCheckInputs` / borrowed `ProofCheckInputs`
//!   pair that both the unified CLI and the `proof_check` compat binary use
//!   to drive the runners.
//!
//! Split out of [`super::pipeline`] so every `cli/*.rs` file stays under the
//! 500-line cap.

use std::path::{Path, PathBuf};

use crate::sat_verify::pipeline::ProofFormat;
use crate::sat_verify::proof_trim;
use crate::smt_verify::certificate::{CertificateVerdict, SmtCertificate, TrustSummary};
use crate::smt_verify::VerifyMode;

// -- Input structures ---------------------------------------------------------

/// All inputs to a single `clean verify proof` invocation, owned as plain
/// references so both the standalone `proof_check` compat binary and the
/// `clean verify proof` subcommand can drive the runners.
pub struct ProofCheckInputs<'a> {
    /// Path to the CNF / SMT-LIB formula.
    pub formula_path: &'a Path,
    /// Path to the proof artifact.
    pub proof_path: &'a Path,
    /// Explicit format override; `None` means auto-detect.
    pub format: Option<ProofFormat>,
    /// Reject any proof containing trusted (unverified) steps.
    pub strict: bool,
    /// Emit parse/verification timings to stderr.
    pub timing: bool,
    /// Optional destination for the JSON certificate.
    pub certificate_path: Option<&'a Path>,
    /// Optional destination for trimmed LRAT output.
    pub trim_output: Option<&'a Path>,
}

/// Owned wrapper around [`ProofCheckInputs`] so CLI argument structures (which
/// own their `PathBuf`s) can hand borrowed views to the runners without
/// re-allocating.
pub struct OwnedProofCheckInputs {
    /// Path to the CNF / SMT-LIB formula.
    pub formula_path: PathBuf,
    /// Path to the proof artifact.
    pub proof_path: PathBuf,
    /// Optional format override; `None` means auto-detect.
    pub format: Option<ProofFormat>,
    /// Reject proofs containing trusted steps.
    pub strict: bool,
    /// Emit parse/verification timings to stderr.
    pub timing: bool,
    /// Optional JSON certificate output path.
    pub certificate_path: Option<PathBuf>,
    /// Optional trimmed-LRAT output path.
    pub trim_output: Option<PathBuf>,
}

impl OwnedProofCheckInputs {
    /// Borrow the owned paths as a [`ProofCheckInputs`] suitable for the
    /// per-mode runners.
    #[must_use]
    pub fn as_inputs(&self) -> ProofCheckInputs<'_> {
        ProofCheckInputs {
            formula_path: &self.formula_path,
            proof_path: &self.proof_path,
            format: self.format,
            strict: self.strict,
            timing: self.timing,
            certificate_path: self.certificate_path.as_deref(),
            trim_output: self.trim_output.as_deref(),
        }
    }
}

// -- Format token parsing -----------------------------------------------------

/// Parse a `--format` token (case-insensitive). Returns `Ok(None)` for
/// `"auto"`.
pub fn parse_format(s: &str) -> Result<Option<ProofFormat>, String> {
    match s.to_ascii_lowercase().as_str() {
        "auto" => Ok(None),
        "lrat" => Ok(Some(ProofFormat::Lrat)),
        "drat" => Ok(Some(ProofFormat::Drat)),
        "alethe" => Ok(Some(ProofFormat::Alethe)),
        "smtlib2" | "smt-lib2" | "smtlib2-proof" => Ok(Some(ProofFormat::SmtLib2Proof)),
        "veripb" => Ok(Some(ProofFormat::VeriPb)),
        other => Err(format!("unknown format: {other}")),
    }
}

// -- Certificate emission -----------------------------------------------------

/// Attempt to generate and write an SMT certificate.
///
/// Alethe proofs route through the full SMT verification pipeline to produce a
/// detailed certificate with trust-level and theory summaries. Every other
/// format falls back to a minimal hash-based certificate.
pub(crate) fn emit_certificate(
    cert_path: &Path,
    formula_bytes: &[u8],
    proof_bytes: &[u8],
    strict: bool,
    format: &ProofFormat,
) {
    let mode = if strict {
        VerifyMode::Strict
    } else {
        VerifyMode::Permissive
    };

    if *format == ProofFormat::Alethe {
        let proof_text = match std::str::from_utf8(proof_bytes) {
            Ok(s) => s,
            Err(e) => {
                eprintln!("c certificate: proof is not valid UTF-8: {e}");
                return;
            }
        };

        match crate::smt_verify::certificate::certify_alethe_proof(
            proof_text,
            formula_bytes,
            proof_bytes,
            mode,
        ) {
            Ok(cert) => write_certificate(&cert, cert_path),
            Err(e) => eprintln!("c certificate: generation failed: {e}"),
        }
        return;
    }

    // Non-Alethe: minimal hash-based certificate.
    let formula_hash: String = blake3::hash(formula_bytes)
        .as_bytes()
        .iter()
        .map(|b| format!("{b:02x}"))
        .collect();
    let proof_hash: String = blake3::hash(proof_bytes)
        .as_bytes()
        .iter()
        .map(|b| format!("{b:02x}"))
        .collect();

    let cert = SmtCertificate {
        version: 1,
        formula_hash,
        proof_hash,
        proof_format: format!("{format}"),
        trust_summary: TrustSummary {
            kernel_verified: 0,
            structurally_accepted: 0,
            axiomatic: 0,
            trusted: 0,
            total: 0,
        },
        theory_summaries: vec![],
        timestamp: std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map(|d| d.as_secs())
            .unwrap_or(0),
        verifier_version: env!("CARGO_PKG_VERSION").to_owned(),
        verdict: CertificateVerdict::Valid,
        verify_mode: if strict { "strict" } else { "permissive" }.to_owned(),
        num_terms: 0,
        num_steps: 0,
    };

    write_certificate(&cert, cert_path);
}

fn write_certificate(cert: &SmtCertificate, path: &Path) {
    match cert.to_json() {
        Ok(json) => match std::fs::write(path, &json) {
            Ok(()) => {
                eprintln!("c certificate written to {}", path.display());
            }
            Err(e) => {
                eprintln!("c ERROR: writing certificate: {e}");
            }
        },
        Err(e) => {
            eprintln!("c ERROR: serializing certificate: {e}");
        }
    }
}

// -- LRAT proof trimming ------------------------------------------------------

/// Trim an LRAT proof and write the minimized output.
///
/// `--trim` only supports LRAT; other formats emit an explicit skip message.
pub(crate) fn run_trim(proof_bytes: &[u8], output_path: &Path, format: &ProofFormat) {
    if *format != ProofFormat::Lrat {
        eprintln!("c trim: skipping non-LRAT proof (format: {format}); --trim only supports LRAT");
        return;
    }

    let proof_text = match std::str::from_utf8(proof_bytes) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("c trim: proof is not valid UTF-8: {e}");
            return;
        }
    };

    match proof_trim::trim_lrat_text(proof_text) {
        Ok((trimmed_text, stats)) => {
            eprintln!(
                "c trim: {}/{} steps retained (ratio: {:.2}x, removed: {:.1}%)",
                stats.trimmed_add_steps,
                stats.original_add_steps,
                stats.trim_ratio(),
                stats.removal_fraction() * 100.0,
            );
            match std::fs::write(output_path, &trimmed_text) {
                Ok(()) => {
                    eprintln!("c trim: wrote trimmed proof to {}", output_path.display());
                }
                Err(e) => {
                    eprintln!("c trim: ERROR writing trimmed proof: {e}");
                }
            }
        }
        Err(e) => {
            eprintln!("c trim: ERROR: {e}");
        }
    }
}
