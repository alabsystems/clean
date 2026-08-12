// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! SMT proof certificate export with blake3 hashing.
//!
//! Produces kernel-verifiable certificates from verified SMT proofs — the
//! final link in the trust chain. A certificate contains:
//!
//! - Input formula hash (blake3)
//! - Proof format and version
//! - Per-step trust level summary
//! - Theory lemma summary
//! - Verification timestamp
//! - Overall verdict
//!
//! ## Certificate Lifecycle
//!
//! 1. Verify an SMT proof via [`super::verify_smt_proof`]
//! 2. Generate a certificate via [`generate_certificate`]
//! 3. Serialize to JSON ([`SmtCertificate::to_json`]) or compact binary
//!    ([`SmtCertificate::to_binary`])
//! 4. Re-verify via [`verify_certificate`] to confirm the certificate matches

use std::collections::BTreeMap;
use std::time::{SystemTime, UNIX_EPOCH};

use serde::{Deserialize, Serialize};
use thiserror::Error;

use super::dag::SmtProofDag;
use super::trust::{SmtVerifyResult, SmtVerifyStats};
use super::{verify_smt_proof, VerifyMode};

/// Certificate format version. Bump on breaking changes to the binary format.
const CERTIFICATE_VERSION: u32 = 1;

/// Magic bytes for the compact binary format: "SMT\x00".
const BINARY_MAGIC: [u8; 4] = [b'S', b'M', b'T', 0x00];

/// Errors from certificate operations.
#[derive(Debug, Error)]
#[non_exhaustive]
pub enum CertificateError {
    /// The certificate's formula hash does not match the provided formula.
    #[error("formula hash mismatch: certificate={expected}, actual={actual}")]
    FormulaHashMismatch { expected: String, actual: String },

    /// The certificate's proof hash does not match the provided proof.
    #[error("proof hash mismatch: certificate={expected}, actual={actual}")]
    ProofHashMismatch { expected: String, actual: String },

    /// Re-verification produced a different verdict than the certificate claims.
    #[error("verdict mismatch: certificate claims {expected:?}, re-verification got {actual:?}")]
    VerdictMismatch {
        expected: CertificateVerdict,
        actual: CertificateVerdict,
    },

    /// Trust level counts do not match re-verification.
    #[error("trust summary mismatch: {reason}")]
    TrustMismatch { reason: String },

    /// JSON serialization/deserialization failed.
    #[error("serialization error: {0}")]
    Serialization(String),

    /// Binary format parsing failed.
    #[error("binary format error: {0}")]
    BinaryFormat(String),
}

/// Overall verification verdict.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
#[serde(rename_all = "snake_case")]
pub enum CertificateVerdict {
    /// Proof is a *fully kernel-verified* refutation (UNSAT): the terminal empty
    /// clause's support contains no structurally-accepted or trusted steps.
    Valid,
    /// The proof structurally derives the empty clause, but at least one step in
    /// the derivation was only structurally accepted (an unchecked theory lemma
    /// or boolean-rule catch-all) rather than semantically re-verified. A holey
    /// refutation is **not** a verified proof: its empty clause may rest on a
    /// false clause admitted verbatim from an unchecked step.
    Holey,
    /// Proof verification failed.
    Invalid,
    /// Verification encountered an error.
    Error,
}

/// Per-trust-level step counts.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TrustSummary {
    /// Steps verified by clean's semantic checkers.
    pub kernel_verified: u32,
    /// Steps structurally accepted (correct shape, not semantically checked).
    pub structurally_accepted: u32,
    /// Axiomatic steps (input assumptions).
    pub axiomatic: u32,
    /// Unverified trust fallback steps.
    pub trusted: u32,
    /// Total step count.
    pub total: u32,
}

impl TrustSummary {
    /// Verification coverage: fraction of non-trusted steps.
    #[must_use]
    pub fn coverage(&self) -> f64 {
        if self.total == 0 {
            return 1.0;
        }
        f64::from(self.kernel_verified + self.structurally_accepted + self.axiomatic)
            / f64::from(self.total)
    }

    /// Whether every step was semantically verified (no structural holes and no
    /// trusted fallbacks).
    ///
    // SOUNDNESS: a "fully verified" certificate must have *zero* structurally
    // accepted steps as well as zero trusted steps. A structurally-accepted step
    // admits its claimed clause verbatim into the resolution graph without a
    // semantic check, so it can launder a false clause into the empty-clause
    // derivation. Matches `SmtVerifyStats::is_fully_verified` (trust.rs). See
    // docs/SOUNDNESS_FINDINGS_CLEAN_VERIFY_2026-07.md root cause B.
    #[must_use]
    pub fn is_fully_verified(&self) -> bool {
        self.trusted == 0 && self.structurally_accepted == 0
    }

    /// Whether the proof structurally derives the empty clause but contains
    /// structurally-accepted holes (and no blindly-trusted steps): a "holey"
    /// refutation, which is **not** a verified proof.
    #[must_use]
    pub fn is_holey(&self) -> bool {
        self.trusted == 0 && self.structurally_accepted > 0
    }
}

/// Per-theory lemma counts.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TheorySummary {
    /// Theory name (e.g., "EUF", "LRA").
    pub theory: String,
    /// Number of lemmas from this theory.
    pub count: u32,
}

/// A compact, serializable SMT proof certificate.
///
/// Contains everything needed to independently verify that a proof was
/// correctly checked, without re-running the full verification.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SmtCertificate {
    /// Certificate format version.
    pub version: u32,
    /// Blake3 hash of the input formula (32 bytes, hex-encoded).
    pub formula_hash: String,
    /// Blake3 hash of the proof data (32 bytes, hex-encoded).
    pub proof_hash: String,
    /// Proof format identifier (e.g., "alethe", "smt_dag").
    pub proof_format: String,
    /// Trust level summary across all proof steps.
    pub trust_summary: TrustSummary,
    /// Per-theory lemma counts.
    pub theory_summaries: Vec<TheorySummary>,
    /// Unix timestamp of when verification was performed.
    pub timestamp: u64,
    /// Verifier version string.
    pub verifier_version: String,
    /// Overall verdict.
    pub verdict: CertificateVerdict,
    /// Verification mode used ("permissive" or "strict").
    pub verify_mode: String,
    /// Number of terms in the proof DAG.
    pub num_terms: u32,
    /// Number of steps in the proof DAG.
    pub num_steps: u32,
}

impl SmtCertificate {
    /// Serialize the certificate to pretty-printed JSON.
    ///
    /// # Errors
    ///
    /// Returns [`CertificateError::Serialization`] if serialization fails.
    pub fn to_json(&self) -> Result<String, CertificateError> {
        serde_json::to_string_pretty(self)
            .map_err(|e| CertificateError::Serialization(e.to_string()))
    }

    /// Deserialize a certificate from JSON.
    ///
    /// # Errors
    ///
    /// Returns [`CertificateError::Serialization`] if the JSON is invalid.
    pub fn from_json(json: &str) -> Result<Self, CertificateError> {
        serde_json::from_str(json).map_err(|e| CertificateError::Serialization(e.to_string()))
    }

    /// Serialize the certificate to a compact binary format.
    ///
    /// Format:
    /// - 4 bytes: magic "SMT\0"
    /// - 4 bytes: version (u32 LE)
    /// - 32 bytes: formula hash (raw)
    /// - 32 bytes: proof hash (raw)
    /// - 1 byte: verdict (0=Valid, 1=Invalid, 2=Error)
    /// - 4 bytes: kernel_verified (u32 LE)
    /// - 4 bytes: structurally_accepted (u32 LE)
    /// - 4 bytes: axiomatic (u32 LE)
    /// - 4 bytes: trusted (u32 LE)
    /// - 4 bytes: total (u32 LE)
    /// - 8 bytes: timestamp (u64 LE)
    /// - 4 bytes: num_terms (u32 LE)
    /// - 4 bytes: num_steps (u32 LE)
    /// - 1 byte: theory_count
    /// - For each theory: 1 byte name_len + name bytes + 4 bytes count
    ///
    /// # Errors
    ///
    /// Returns [`CertificateError::BinaryFormat`] if hash decoding fails.
    pub fn to_binary(&self) -> Result<Vec<u8>, CertificateError> {
        let mut buf = Vec::with_capacity(128);

        buf.extend_from_slice(&BINARY_MAGIC);
        buf.extend_from_slice(&self.version.to_le_bytes());

        let formula_hash_bytes = hex_to_bytes(&self.formula_hash)?;
        let proof_hash_bytes = hex_to_bytes(&self.proof_hash)?;
        buf.extend_from_slice(&formula_hash_bytes);
        buf.extend_from_slice(&proof_hash_bytes);

        buf.push(verdict_to_byte(self.verdict));

        buf.extend_from_slice(&self.trust_summary.kernel_verified.to_le_bytes());
        buf.extend_from_slice(&self.trust_summary.structurally_accepted.to_le_bytes());
        buf.extend_from_slice(&self.trust_summary.axiomatic.to_le_bytes());
        buf.extend_from_slice(&self.trust_summary.trusted.to_le_bytes());
        buf.extend_from_slice(&self.trust_summary.total.to_le_bytes());
        buf.extend_from_slice(&self.timestamp.to_le_bytes());
        buf.extend_from_slice(&self.num_terms.to_le_bytes());
        buf.extend_from_slice(&self.num_steps.to_le_bytes());

        let theory_count = self.theory_summaries.len().min(255) as u8;
        buf.push(theory_count);
        for summary in self.theory_summaries.iter().take(theory_count as usize) {
            let name_bytes = summary.theory.as_bytes();
            let name_len = name_bytes.len().min(255) as u8;
            buf.push(name_len);
            buf.extend_from_slice(&name_bytes[..name_len as usize]);
            buf.extend_from_slice(&summary.count.to_le_bytes());
        }

        Ok(buf)
    }

    /// Deserialize a certificate from compact binary format.
    ///
    /// # Errors
    ///
    /// Returns [`CertificateError::BinaryFormat`] if the data is malformed.
    pub fn from_binary(data: &[u8]) -> Result<Self, CertificateError> {
        let mut pos = 0;

        let read_bytes = |pos: &mut usize, n: usize| -> Result<&[u8], CertificateError> {
            if *pos + n > data.len() {
                return Err(CertificateError::BinaryFormat(format!(
                    "unexpected end at offset {}, need {} bytes",
                    *pos, n
                )));
            }
            let slice = &data[*pos..*pos + n];
            *pos += n;
            Ok(slice)
        };

        let magic = read_bytes(&mut pos, 4)?;
        if magic != BINARY_MAGIC {
            return Err(CertificateError::BinaryFormat(
                "invalid magic bytes".to_owned(),
            ));
        }

        let version = u32::from_le_bytes(
            read_bytes(&mut pos, 4)?
                .try_into()
                .map_err(|_| CertificateError::BinaryFormat("version".to_owned()))?,
        );

        let formula_hash = bytes_to_hex(read_bytes(&mut pos, 32)?);
        let proof_hash = bytes_to_hex(read_bytes(&mut pos, 32)?);

        let verdict_byte = read_bytes(&mut pos, 1)?[0];
        let verdict = byte_to_verdict(verdict_byte)?;

        let kernel_verified = read_u32_le(&mut pos, data)?;
        let structurally_accepted = read_u32_le(&mut pos, data)?;
        let axiomatic = read_u32_le(&mut pos, data)?;
        let trusted = read_u32_le(&mut pos, data)?;
        let total = read_u32_le(&mut pos, data)?;

        let timestamp = read_u64_le(&mut pos, data)?;
        let num_terms = read_u32_le(&mut pos, data)?;
        let num_steps = read_u32_le(&mut pos, data)?;

        let theory_count = read_bytes(&mut pos, 1)?[0];
        let mut theory_summaries = Vec::with_capacity(theory_count as usize);
        for _ in 0..theory_count {
            let name_len = read_bytes(&mut pos, 1)?[0] as usize;
            let name_bytes = read_bytes(&mut pos, name_len)?;
            let theory = String::from_utf8(name_bytes.to_vec())
                .map_err(|e| CertificateError::BinaryFormat(format!("theory name: {e}")))?;
            let count = read_u32_le(&mut pos, data)?;
            theory_summaries.push(TheorySummary { theory, count });
        }

        Ok(Self {
            version,
            formula_hash,
            proof_hash,
            proof_format: String::new(),
            trust_summary: TrustSummary {
                kernel_verified,
                structurally_accepted,
                axiomatic,
                trusted,
                total,
            },
            theory_summaries,
            timestamp,
            verifier_version: String::new(),
            verdict,
            verify_mode: String::new(),
            num_terms,
            num_steps,
        })
    }
}

/// Generate a certificate from a completed SMT proof verification.
///
/// # Arguments
/// * `dag` - The proof DAG that was verified.
/// * `result` - The verification result from [`super::verify_smt_proof`].
/// * `formula_bytes` - Raw formula bytes for blake3 hashing.
/// * `proof_bytes` - Raw proof bytes for blake3 hashing.
/// * `proof_format` - String identifying the proof format (e.g., "alethe").
/// * `mode` - The verification mode that was used.
#[must_use]
pub fn generate_certificate(
    dag: &SmtProofDag,
    result: &SmtVerifyResult,
    formula_bytes: &[u8],
    proof_bytes: &[u8],
    proof_format: &str,
    mode: VerifyMode,
) -> SmtCertificate {
    let formula_hash = bytes_to_hex(blake3::hash(formula_bytes).as_bytes());
    let proof_hash = bytes_to_hex(blake3::hash(proof_bytes).as_bytes());

    let verdict = result_to_verdict(result);

    let trust_summary = stats_to_trust_summary(&result.stats);
    let theory_summaries = stats_to_theory_summaries(&result.stats);

    let timestamp = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|d| d.as_secs())
        .unwrap_or(0);

    let verify_mode = match mode {
        VerifyMode::Permissive => "permissive",
        VerifyMode::Strict => "strict",
    };

    SmtCertificate {
        version: CERTIFICATE_VERSION,
        formula_hash,
        proof_hash,
        proof_format: proof_format.to_owned(),
        trust_summary,
        theory_summaries,
        timestamp,
        verifier_version: env!("CARGO_PKG_VERSION").to_owned(),
        verdict,
        verify_mode: verify_mode.to_owned(),
        num_terms: dag.num_terms() as u32,
        num_steps: dag.num_steps() as u32,
    }
}

/// Verify a certificate against original formula and proof data.
///
/// Re-runs verification and checks that the certificate's hashes and
/// trust summary match. This is the independent check that confirms
/// the certificate is authentic.
///
/// # Arguments
/// * `cert` - The certificate to verify.
/// * `dag` - The original proof DAG.
/// * `formula_bytes` - Original formula bytes.
/// * `proof_bytes` - Original proof bytes.
///
/// # Errors
///
/// Returns [`CertificateError`] if any check fails.
pub fn verify_certificate(
    cert: &SmtCertificate,
    dag: &SmtProofDag,
    formula_bytes: &[u8],
    proof_bytes: &[u8],
) -> Result<(), CertificateError> {
    // 1. Verify formula hash.
    let actual_formula_hash = bytes_to_hex(blake3::hash(formula_bytes).as_bytes());
    if cert.formula_hash != actual_formula_hash {
        return Err(CertificateError::FormulaHashMismatch {
            expected: cert.formula_hash.clone(),
            actual: actual_formula_hash,
        });
    }

    // 2. Verify proof hash.
    let actual_proof_hash = bytes_to_hex(blake3::hash(proof_bytes).as_bytes());
    if cert.proof_hash != actual_proof_hash {
        return Err(CertificateError::ProofHashMismatch {
            expected: cert.proof_hash.clone(),
            actual: actual_proof_hash,
        });
    }

    // 3. Re-verify the proof.
    let mode = match cert.verify_mode.as_str() {
        "strict" => VerifyMode::Strict,
        _ => VerifyMode::Permissive,
    };
    let re_result = verify_smt_proof(dag, mode);

    // 4. Check verdict matches.
    let re_verdict = result_to_verdict(&re_result);

    if cert.verdict != re_verdict {
        return Err(CertificateError::VerdictMismatch {
            expected: cert.verdict,
            actual: re_verdict,
        });
    }

    // 5. Check trust summary matches.
    let re_trust = stats_to_trust_summary(&re_result.stats);
    if cert.trust_summary != re_trust {
        return Err(CertificateError::TrustMismatch {
            reason: format!(
                "certificate: kv={} sa={} ax={} tr={}, re-verify: kv={} sa={} ax={} tr={}",
                cert.trust_summary.kernel_verified,
                cert.trust_summary.structurally_accepted,
                cert.trust_summary.axiomatic,
                cert.trust_summary.trusted,
                re_trust.kernel_verified,
                re_trust.structurally_accepted,
                re_trust.axiomatic,
                re_trust.trusted,
            ),
        });
    }

    Ok(())
}

/// End-to-end Alethe proof certificate generation.
///
/// Parses an Alethe proof, verifies it, and produces a certificate.
/// This is the convenience entry point for the CLI.
///
/// # Arguments
/// * `proof_text` - Alethe proof in S-expression format.
/// * `formula_bytes` - Raw formula bytes for blake3 hashing.
/// * `proof_bytes` - Raw proof bytes for blake3 hashing.
/// * `mode` - Verification mode (strict or permissive).
///
/// # Errors
///
/// Returns [`CertificateError`] if parsing or verification fails.
pub fn certify_alethe_proof(
    proof_text: &str,
    formula_bytes: &[u8],
    proof_bytes: &[u8],
    mode: VerifyMode,
) -> Result<SmtCertificate, CertificateError> {
    let parsed = super::alethe_parser::parse_alethe(proof_text)
        .map_err(|e| CertificateError::Serialization(format!("Alethe parse error: {e}")))?;

    let dag = super::alethe_bridge::alethe_to_dag(parsed);
    let result = verify_smt_proof(&dag, mode);

    Ok(generate_certificate(
        &dag,
        &result,
        formula_bytes,
        proof_bytes,
        "alethe",
        mode,
    ))
}

// ---------------------------------------------------------------------------
// Internal helpers
// ---------------------------------------------------------------------------

/// Derive a certificate verdict from a verification result.
///
/// - `Valid` iff the proof structurally derives the empty clause **and** every
///   step in the derivation was semantically verified (fully kernel-verified).
/// - `Holey` if the proof derives the empty clause but rests on one or more
///   structurally-accepted steps (no blindly-trusted steps).
/// - `Error` if strict mode rejected a trusted step (the proof was
///   structurally valid but failed the trust policy).
/// - `Invalid` otherwise (proof doesn't derive empty clause, structural
///   issues, etc.).
//
// SOUNDNESS: `result.valid` is a *structural* precondition ("derives the empty
// clause") — it is true even when the empty clause is laundered from a
// structurally-accepted step's unchecked (possibly false) clause. A `Valid`
// certificate is a discharge claim, so it must additionally require
// `stats.is_fully_verified()`; a holey refutation maps to `Holey`, never
// `Valid`. See docs/SOUNDNESS_FINDINGS_CLEAN_VERIFY_2026-07.md root cause B.
fn result_to_verdict(result: &SmtVerifyResult) -> CertificateVerdict {
    if result.valid {
        if result.stats.is_fully_verified() {
            return CertificateVerdict::Valid;
        }
        // Structurally derives the empty clause but leans on unchecked holes.
        if result.stats.trusted == 0 {
            return CertificateVerdict::Holey;
        }
        // Trusted (blindly accepted) steps feed the derivation: not a discharge.
        return CertificateVerdict::Error;
    }
    // Distinguish strict-mode trust rejection (Error) from proof invalidity.
    if let Some(ref err) = result.first_error {
        if matches!(err, super::trust::SmtVerifyError::TrustStep { .. }) {
            return CertificateVerdict::Error;
        }
    }
    CertificateVerdict::Invalid
}

fn stats_to_trust_summary(stats: &SmtVerifyStats) -> TrustSummary {
    TrustSummary {
        kernel_verified: stats.kernel_verified,
        structurally_accepted: stats.structurally_accepted,
        axiomatic: stats.axiomatic,
        trusted: stats.trusted,
        total: stats.total_steps,
    }
}

fn stats_to_theory_summaries(stats: &SmtVerifyStats) -> Vec<TheorySummary> {
    let sorted: BTreeMap<String, u32> = stats
        .theory_lemma_counts
        .iter()
        .map(|(theory, &count)| (theory.to_string(), count))
        .collect();

    sorted
        .into_iter()
        .map(|(theory, count)| TheorySummary { theory, count })
        .collect()
}

fn bytes_to_hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

fn hex_to_bytes(hex: &str) -> Result<Vec<u8>, CertificateError> {
    if !hex.len().is_multiple_of(2) {
        return Err(CertificateError::BinaryFormat(
            "odd-length hex string".to_owned(),
        ));
    }
    (0..hex.len())
        .step_by(2)
        .map(|i| {
            u8::from_str_radix(&hex[i..i + 2], 16)
                .map_err(|e| CertificateError::BinaryFormat(format!("invalid hex: {e}")))
        })
        .collect()
}

fn verdict_to_byte(v: CertificateVerdict) -> u8 {
    match v {
        CertificateVerdict::Valid => 0,
        CertificateVerdict::Invalid => 1,
        CertificateVerdict::Error => 2,
        CertificateVerdict::Holey => 3,
    }
}

fn byte_to_verdict(b: u8) -> Result<CertificateVerdict, CertificateError> {
    match b {
        0 => Ok(CertificateVerdict::Valid),
        1 => Ok(CertificateVerdict::Invalid),
        2 => Ok(CertificateVerdict::Error),
        3 => Ok(CertificateVerdict::Holey),
        _ => Err(CertificateError::BinaryFormat(format!(
            "invalid verdict byte: {b}"
        ))),
    }
}

fn read_u32_le(pos: &mut usize, data: &[u8]) -> Result<u32, CertificateError> {
    if *pos + 4 > data.len() {
        return Err(CertificateError::BinaryFormat(format!(
            "unexpected end at offset {} reading u32",
            *pos
        )));
    }
    let val = u32::from_le_bytes(
        data[*pos..*pos + 4]
            .try_into()
            .map_err(|_| CertificateError::BinaryFormat("u32 conversion".to_owned()))?,
    );
    *pos += 4;
    Ok(val)
}

fn read_u64_le(pos: &mut usize, data: &[u8]) -> Result<u64, CertificateError> {
    if *pos + 8 > data.len() {
        return Err(CertificateError::BinaryFormat(format!(
            "unexpected end at offset {} reading u64",
            *pos
        )));
    }
    let val = u64::from_le_bytes(
        data[*pos..*pos + 8]
            .try_into()
            .map_err(|_| CertificateError::BinaryFormat("u64 conversion".to_owned()))?,
    );
    *pos += 8;
    Ok(val)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::smt_verify::dag::{
        SmtProofStep, SmtSort, SmtSymbol, SmtTerm, SmtTheory, TheoryLemmaDetail,
    };

    /// Build a simple valid proof: assume p, assume not(p), resolve to empty.
    fn build_simple_proof() -> SmtProofDag {
        let mut dag = SmtProofDag::new();
        let p = dag.add_term(SmtTerm::Var("p".to_string(), SmtSort::Bool));
        let not_p = dag.add_term(SmtTerm::Not(p));

        let s0 = dag.add_step(SmtProofStep::Assume(p));
        let s1 = dag.add_step(SmtProofStep::Assume(not_p));
        dag.add_step(SmtProofStep::Resolution {
            clause: vec![],
            premises: vec![s0, s1],
            pivot: Some(p),
        });
        dag
    }

    /// Build a proof with a theory lemma (LRA Farkas).
    fn build_lra_proof() -> SmtProofDag {
        let mut dag = SmtProofDag::new();
        dag.declare("x".to_string(), SmtSort::Real);

        let x = dag.add_term(SmtTerm::Var("x".to_string(), SmtSort::Real));
        let zero = dag.add_term(SmtTerm::Int(0));
        let neg_one = dag.add_term(SmtTerm::Int(-1));

        let ge_x_0 = dag.add_term(SmtTerm::App(
            SmtSymbol::Named(">=".to_string()),
            vec![x, zero],
        ));
        let le_x_neg1 = dag.add_term(SmtTerm::App(
            SmtSymbol::Named("<=".to_string()),
            vec![x, neg_one],
        ));
        let not_ge_x_0 = dag.add_term(SmtTerm::Not(ge_x_0));
        let not_le_x_neg1 = dag.add_term(SmtTerm::Not(le_x_neg1));

        let s0 = dag.add_step(SmtProofStep::Assume(ge_x_0));
        let s1 = dag.add_step(SmtProofStep::Assume(le_x_neg1));
        let s2 = dag.add_step(SmtProofStep::TheoryLemma {
            theory: SmtTheory::Lra,
            kind: TheoryLemmaDetail::LraFarkas {
                coefficients: vec![(1, 1), (1, 1)],
            },
            clause: vec![not_ge_x_0, not_le_x_neg1],
        });
        let s3 = dag.add_step(SmtProofStep::Resolution {
            clause: vec![not_le_x_neg1],
            premises: vec![s0, s2],
            pivot: Some(ge_x_0),
        });
        dag.add_step(SmtProofStep::Resolution {
            clause: vec![],
            premises: vec![s1, s3],
            pivot: Some(le_x_neg1),
        });

        dag
    }

    #[test]
    fn test_generate_certificate_simple_proof() {
        let dag = build_simple_proof();
        let result = verify_smt_proof(&dag, VerifyMode::Permissive);
        let formula = b"(declare-const p Bool)";
        let proof = b"simple proof data";

        let cert = generate_certificate(
            &dag,
            &result,
            formula,
            proof,
            "smt_dag",
            VerifyMode::Permissive,
        );

        assert_eq!(cert.version, CERTIFICATE_VERSION);
        assert_eq!(cert.verdict, CertificateVerdict::Valid);
        assert_eq!(cert.proof_format, "smt_dag");
        assert_eq!(cert.verify_mode, "permissive");
        assert_eq!(cert.num_steps, 3);
        assert_eq!(cert.trust_summary.total, 3);
        assert_eq!(cert.trust_summary.axiomatic, 2);
        assert_eq!(cert.trust_summary.kernel_verified, 1);
        assert_eq!(cert.trust_summary.trusted, 0);
        assert!(cert.trust_summary.is_fully_verified());
        assert!((cert.trust_summary.coverage() - 1.0).abs() < f64::EPSILON);
        assert!(!cert.formula_hash.is_empty());
        assert!(!cert.proof_hash.is_empty());
        assert!(cert.timestamp > 0);
    }

    #[test]
    fn test_generate_certificate_lra_proof_has_theory_summary() {
        let dag = build_lra_proof();
        let result = verify_smt_proof(&dag, VerifyMode::Permissive);
        let formula = b"(declare-const x Real)";
        let proof = b"lra proof data";

        let cert = generate_certificate(
            &dag,
            &result,
            formula,
            proof,
            "smt_dag",
            VerifyMode::Permissive,
        );

        assert_eq!(cert.verdict, CertificateVerdict::Valid);
        assert!(!cert.theory_summaries.is_empty());
        let lra_summary = cert
            .theory_summaries
            .iter()
            .find(|s| s.theory == "LRA")
            .expect("should have LRA summary");
        assert_eq!(lra_summary.count, 1);
    }

    #[test]
    fn test_certificate_json_roundtrip() {
        let dag = build_simple_proof();
        let result = verify_smt_proof(&dag, VerifyMode::Permissive);
        let cert = generate_certificate(
            &dag,
            &result,
            b"formula",
            b"proof",
            "smt_dag",
            VerifyMode::Permissive,
        );

        let json = cert.to_json().expect("serialization should succeed");
        let restored = SmtCertificate::from_json(&json).expect("deserialization should succeed");

        assert_eq!(cert.version, restored.version);
        assert_eq!(cert.formula_hash, restored.formula_hash);
        assert_eq!(cert.proof_hash, restored.proof_hash);
        assert_eq!(cert.verdict, restored.verdict);
        assert_eq!(cert.trust_summary, restored.trust_summary);
        assert_eq!(cert.theory_summaries, restored.theory_summaries);
        assert_eq!(cert.num_steps, restored.num_steps);
        assert_eq!(cert.num_terms, restored.num_terms);
    }

    #[test]
    fn test_certificate_binary_roundtrip() {
        let dag = build_lra_proof();
        let result = verify_smt_proof(&dag, VerifyMode::Permissive);
        let cert = generate_certificate(
            &dag,
            &result,
            b"formula",
            b"proof",
            "smt_dag",
            VerifyMode::Permissive,
        );

        let binary = cert
            .to_binary()
            .expect("binary serialization should succeed");
        let restored =
            SmtCertificate::from_binary(&binary).expect("binary deserialization should succeed");

        assert_eq!(cert.version, restored.version);
        assert_eq!(cert.formula_hash, restored.formula_hash);
        assert_eq!(cert.proof_hash, restored.proof_hash);
        assert_eq!(cert.verdict, restored.verdict);
        assert_eq!(cert.trust_summary, restored.trust_summary);
        assert_eq!(cert.theory_summaries, restored.theory_summaries);
        assert_eq!(cert.num_steps, restored.num_steps);
        assert_eq!(cert.num_terms, restored.num_terms);
    }

    #[test]
    fn test_certificate_binary_starts_with_magic() {
        let dag = build_simple_proof();
        let result = verify_smt_proof(&dag, VerifyMode::Permissive);
        let cert = generate_certificate(
            &dag,
            &result,
            b"formula",
            b"proof",
            "smt_dag",
            VerifyMode::Permissive,
        );

        let binary = cert.to_binary().expect("should serialize");
        assert!(binary.len() >= 4);
        assert_eq!(&binary[0..4], &BINARY_MAGIC);
    }

    #[test]
    fn test_certificate_binary_invalid_magic() {
        let bad_data = b"BAD\x00rest of data";
        let err = SmtCertificate::from_binary(bad_data).expect_err("should fail");
        assert!(matches!(err, CertificateError::BinaryFormat(_)));
    }

    #[test]
    fn test_certificate_binary_truncated() {
        let err = SmtCertificate::from_binary(b"SMT\x00").expect_err("should fail");
        assert!(matches!(err, CertificateError::BinaryFormat(_)));
    }

    #[test]
    fn test_verify_certificate_valid() {
        let dag = build_simple_proof();
        let formula = b"formula bytes";
        let proof = b"proof bytes";
        let result = verify_smt_proof(&dag, VerifyMode::Permissive);
        let cert = generate_certificate(
            &dag,
            &result,
            formula,
            proof,
            "smt_dag",
            VerifyMode::Permissive,
        );

        verify_certificate(&cert, &dag, formula, proof)
            .expect("certificate should verify against original data");
    }

    #[test]
    fn test_verify_certificate_formula_hash_mismatch() {
        let dag = build_simple_proof();
        let formula = b"formula bytes";
        let proof = b"proof bytes";
        let result = verify_smt_proof(&dag, VerifyMode::Permissive);
        let cert = generate_certificate(
            &dag,
            &result,
            formula,
            proof,
            "smt_dag",
            VerifyMode::Permissive,
        );

        let err = verify_certificate(&cert, &dag, b"different formula", proof)
            .expect_err("should fail with different formula");
        assert!(matches!(err, CertificateError::FormulaHashMismatch { .. }));
    }

    #[test]
    fn test_verify_certificate_proof_hash_mismatch() {
        let dag = build_simple_proof();
        let formula = b"formula bytes";
        let proof = b"proof bytes";
        let result = verify_smt_proof(&dag, VerifyMode::Permissive);
        let cert = generate_certificate(
            &dag,
            &result,
            formula,
            proof,
            "smt_dag",
            VerifyMode::Permissive,
        );

        let err = verify_certificate(&cert, &dag, formula, b"different proof")
            .expect_err("should fail with different proof");
        assert!(matches!(err, CertificateError::ProofHashMismatch { .. }));
    }

    #[test]
    fn test_verify_certificate_verdict_mismatch() {
        let dag = build_simple_proof();
        let formula = b"formula";
        let proof = b"proof";
        let result = verify_smt_proof(&dag, VerifyMode::Permissive);
        let mut cert = generate_certificate(
            &dag,
            &result,
            formula,
            proof,
            "smt_dag",
            VerifyMode::Permissive,
        );

        // Tamper with verdict.
        cert.verdict = CertificateVerdict::Invalid;

        let err = verify_certificate(&cert, &dag, formula, proof)
            .expect_err("should fail with tampered verdict");
        assert!(matches!(err, CertificateError::VerdictMismatch { .. }));
    }

    #[test]
    fn test_verify_certificate_trust_mismatch() {
        let dag = build_simple_proof();
        let formula = b"formula";
        let proof = b"proof";
        let result = verify_smt_proof(&dag, VerifyMode::Permissive);
        let mut cert = generate_certificate(
            &dag,
            &result,
            formula,
            proof,
            "smt_dag",
            VerifyMode::Permissive,
        );

        // Tamper with trust counts.
        cert.trust_summary.kernel_verified += 5;

        let err = verify_certificate(&cert, &dag, formula, proof)
            .expect_err("should fail with tampered trust");
        assert!(matches!(err, CertificateError::TrustMismatch { .. }));
    }

    #[test]
    fn test_certificate_invalid_proof_verdict() {
        // A proof that doesn't derive empty clause.
        let mut dag = SmtProofDag::new();
        let p = dag.add_term(SmtTerm::Var("p".to_string(), SmtSort::Bool));
        dag.add_step(SmtProofStep::Assume(p));

        let result = verify_smt_proof(&dag, VerifyMode::Permissive);
        let cert = generate_certificate(
            &dag,
            &result,
            b"formula",
            b"proof",
            "smt_dag",
            VerifyMode::Permissive,
        );

        assert_eq!(cert.verdict, CertificateVerdict::Invalid);
    }

    #[test]
    fn test_certificate_strict_mode_error_verdict() {
        // Proof with a trust step verified in strict mode.
        let mut dag = SmtProofDag::new();
        let p = dag.add_term(SmtTerm::Var("p".to_string(), SmtSort::Bool));
        let not_p = dag.add_term(SmtTerm::Not(p));

        let s0 = dag.add_step(SmtProofStep::Assume(p));
        let s1 = dag.add_step(SmtProofStep::TheoryLemma {
            theory: SmtTheory::Core,
            kind: TheoryLemmaDetail::Generic,
            clause: vec![not_p],
        });
        dag.add_step(SmtProofStep::Resolution {
            clause: vec![],
            premises: vec![s0, s1],
            pivot: Some(p),
        });

        let result = verify_smt_proof(&dag, VerifyMode::Strict);
        let cert = generate_certificate(
            &dag,
            &result,
            b"formula",
            b"proof",
            "smt_dag",
            VerifyMode::Strict,
        );

        // Strict mode rejects trusted steps, so the result has an error.
        assert_eq!(cert.verdict, CertificateVerdict::Error);
        assert_eq!(cert.verify_mode, "strict");
    }

    #[test]
    fn test_certificate_from_invalid_json() {
        let err = SmtCertificate::from_json("not valid json").expect_err("should fail");
        assert!(matches!(err, CertificateError::Serialization(_)));
    }

    #[test]
    fn test_trust_summary_coverage_empty() {
        let summary = TrustSummary {
            kernel_verified: 0,
            structurally_accepted: 0,
            axiomatic: 0,
            trusted: 0,
            total: 0,
        };
        assert!((summary.coverage() - 1.0).abs() < f64::EPSILON);
        assert!(summary.is_fully_verified());
    }

    #[test]
    fn test_trust_summary_coverage_mixed() {
        let summary = TrustSummary {
            kernel_verified: 6,
            structurally_accepted: 2,
            axiomatic: 1,
            trusted: 1,
            total: 10,
        };
        assert!((summary.coverage() - 0.9).abs() < f64::EPSILON);
        assert!(!summary.is_fully_verified());
    }

    // SOUNDNESS (root cause B): a structurally-accepted step is a hole, not a
    // verification. Even with zero trusted steps, a summary with any
    // structurally-accepted step must NOT be reported fully verified.
    #[test]
    fn test_trust_summary_structurally_accepted_is_not_fully_verified() {
        let summary = TrustSummary {
            kernel_verified: 5,
            structurally_accepted: 1,
            axiomatic: 2,
            trusted: 0,
            total: 8,
        };
        assert!(
            !summary.is_fully_verified(),
            "a holey summary (structurally_accepted > 0) is not fully verified"
        );
        assert!(summary.is_holey(), "no trusted steps, but has holes");
    }

    #[test]
    fn test_hex_roundtrip() {
        let original = [0xDE, 0xAD, 0xBE, 0xEF, 0x00, 0xFF];
        let hex = bytes_to_hex(&original);
        assert_eq!(hex, "deadbeef00ff");
        let recovered = hex_to_bytes(&hex).expect("should decode");
        assert_eq!(recovered, original);
    }

    #[test]
    fn test_hex_to_bytes_invalid() {
        let err = hex_to_bytes("zz").expect_err("should fail");
        assert!(matches!(err, CertificateError::BinaryFormat(_)));
    }

    #[test]
    fn test_hex_to_bytes_odd_length() {
        let err = hex_to_bytes("abc").expect_err("should fail");
        assert!(matches!(err, CertificateError::BinaryFormat(_)));
    }

    #[test]
    fn test_verdict_byte_roundtrip() {
        for &v in &[
            CertificateVerdict::Valid,
            CertificateVerdict::Invalid,
            CertificateVerdict::Error,
            CertificateVerdict::Holey,
        ] {
            let b = verdict_to_byte(v);
            let recovered = byte_to_verdict(b).expect("should decode");
            assert_eq!(v, recovered);
        }
    }

    #[test]
    fn test_verdict_byte_invalid() {
        let err = byte_to_verdict(99).expect_err("should fail");
        assert!(matches!(err, CertificateError::BinaryFormat(_)));
    }

    #[test]
    fn test_certificate_json_contains_expected_fields() {
        let dag = build_simple_proof();
        let result = verify_smt_proof(&dag, VerifyMode::Permissive);
        let cert = generate_certificate(
            &dag,
            &result,
            b"formula",
            b"proof",
            "alethe",
            VerifyMode::Permissive,
        );

        let json = cert.to_json().expect("should serialize");
        assert!(json.contains("\"version\""));
        assert!(json.contains("\"formula_hash\""));
        assert!(json.contains("\"proof_hash\""));
        assert!(json.contains("\"proof_format\""));
        assert!(json.contains("\"trust_summary\""));
        assert!(json.contains("\"verdict\""));
        assert!(json.contains("\"verifier_version\""));
        assert!(json.contains("\"valid\""));
        assert!(json.contains("\"alethe\""));
    }

    #[test]
    fn test_generate_certificate_deterministic_hashes() {
        let dag = build_simple_proof();
        let formula = b"same formula";
        let proof = b"same proof";

        let result1 = verify_smt_proof(&dag, VerifyMode::Permissive);
        let cert1 = generate_certificate(
            &dag,
            &result1,
            formula,
            proof,
            "smt_dag",
            VerifyMode::Permissive,
        );

        let result2 = verify_smt_proof(&dag, VerifyMode::Permissive);
        let cert2 = generate_certificate(
            &dag,
            &result2,
            formula,
            proof,
            "smt_dag",
            VerifyMode::Permissive,
        );

        assert_eq!(cert1.formula_hash, cert2.formula_hash);
        assert_eq!(cert1.proof_hash, cert2.proof_hash);
        assert_eq!(cert1.trust_summary, cert2.trust_summary);
        assert_eq!(cert1.verdict, cert2.verdict);
    }

    // ---- AI Model-flagged adversarial soundness tests ----

    #[test]
    fn test_structurally_similar_but_semantically_different_proofs_have_different_hashes() {
        use crate::smt_verify::dag::AletheRuleKind;

        fn build_boolean_refutation(connective: &str, rule: AletheRuleKind) -> SmtProofDag {
            let mut dag = SmtProofDag::new();

            let p = dag.add_term(SmtTerm::Var("p".to_string(), SmtSort::Bool));
            let q = dag.add_term(SmtTerm::Var("q".to_string(), SmtSort::Bool));
            let compound = dag.add_term(SmtTerm::App(
                SmtSymbol::Named(connective.to_string()),
                vec![p, q],
            ));
            let not_p = dag.add_term(SmtTerm::Not(p));

            let assume_compound = dag.add_step(SmtProofStep::Assume(compound));
            let assume_not_p = dag.add_step(SmtProofStep::Assume(not_p));
            let derive_p = dag.add_step(SmtProofStep::Step {
                rule,
                clause: vec![p],
                premises: vec![assume_compound],
                args: vec![compound],
            });
            dag.add_step(SmtProofStep::Resolution {
                clause: vec![],
                premises: vec![assume_not_p, derive_p],
                pivot: Some(p),
            });

            dag
        }

        let dag_a = build_boolean_refutation("and", AletheRuleKind::AndPos(0));
        let dag_b = build_boolean_refutation("or", AletheRuleKind::OrPos);

        let formula_a = b"(assert (and p q))\n(assert (not p))";
        let formula_b = b"(assert (or p q))\n(assert (not p))";
        let proof_bytes = b"(proof structurally-similar boolean refutation)";

        let result_a = verify_smt_proof(&dag_a, VerifyMode::Strict);
        let result_b = verify_smt_proof(&dag_b, VerifyMode::Strict);
        assert!(
            result_a.valid,
            "AND proof should verify before hashing: {:?}",
            result_a.first_error
        );
        assert!(
            result_b.valid,
            "OR proof should verify before hashing: {:?}",
            result_b.first_error
        );

        let cert_a = generate_certificate(
            &dag_a,
            &result_a,
            formula_a,
            proof_bytes,
            "smt_dag",
            VerifyMode::Strict,
        );
        let cert_b = generate_certificate(
            &dag_b,
            &result_b,
            formula_b,
            proof_bytes,
            "smt_dag",
            VerifyMode::Strict,
        );

        verify_certificate(&cert_a, &dag_a, formula_a, proof_bytes)
            .expect("certificate A should verify against its original formula");
        verify_certificate(&cert_b, &dag_b, formula_b, proof_bytes)
            .expect("certificate B should verify against its original formula");

        assert_eq!(cert_a.num_steps, cert_b.num_steps);
        assert_eq!(cert_a.trust_summary, cert_b.trust_summary);
        assert_eq!(cert_a.proof_hash, cert_b.proof_hash);
        assert_eq!(
            cert_a.formula_hash,
            blake3::hash(formula_a).to_hex().to_string()
        );
        assert_eq!(
            cert_b.formula_hash,
            blake3::hash(formula_b).to_hex().to_string()
        );
        assert_ne!(
            cert_a.formula_hash, cert_b.formula_hash,
            "formula_hash collision would let an AND proof certificate masquerade as an OR proof certificate"
        );

        let err = verify_certificate(&cert_a, &dag_a, formula_b, proof_bytes)
            .expect_err("certificate A must not accept proof B's formula bytes");
        assert!(matches!(err, CertificateError::FormulaHashMismatch { .. }));
    }

    #[test]
    fn test_tampered_binary_certificate_single_byte_flip_fails_verification() {
        let dag = build_simple_proof();
        let formula = b"(assert p)\n(assert (not p))";
        let proof = b"(proof direct resolution)";
        let result = verify_smt_proof(&dag, VerifyMode::Permissive);
        assert!(
            result.valid,
            "baseline proof should verify before tampering: {:?}",
            result.first_error
        );

        let cert = generate_certificate(
            &dag,
            &result,
            formula,
            proof,
            "smt_dag",
            VerifyMode::Permissive,
        );
        let mut binary = cert
            .to_binary()
            .expect("binary serialization should succeed");

        // Flip a byte in the middle of the binary data
        let flip_index = binary.len() / 2;
        binary[flip_index] ^= 0x01;

        // Either deserialization fails or verification catches the tamper
        match SmtCertificate::from_binary(&binary) {
            Err(_) => {
                // Deserialization failed — tamper detected at parse time, which is fine
            }
            Ok(tampered) => {
                // Deserialized but must fail verification
                let verify_result = verify_certificate(&tampered, &dag, formula, proof);
                assert!(
                    verify_result.is_err(),
                    "tampered binary certificate must not verify"
                );
            }
        }
    }

    #[test]
    fn test_certificate_different_proof_same_formula_different_proof_hash() {
        fn build_direct_refutation() -> SmtProofDag {
            let mut dag = SmtProofDag::new();
            let p = dag.add_term(SmtTerm::Var("p".to_string(), SmtSort::Bool));
            let not_p = dag.add_term(SmtTerm::Not(p));

            let s0 = dag.add_step(SmtProofStep::Assume(p));
            let s1 = dag.add_step(SmtProofStep::Assume(not_p));
            dag.add_step(SmtProofStep::Resolution {
                clause: vec![],
                premises: vec![s0, s1],
                pivot: Some(p),
            });

            dag
        }

        fn build_anchored_refutation() -> SmtProofDag {
            let mut dag = SmtProofDag::new();
            let p = dag.add_term(SmtTerm::Var("p".to_string(), SmtSort::Bool));
            let not_p = dag.add_term(SmtTerm::Not(p));

            let s0 = dag.add_step(SmtProofStep::Assume(p));
            let s1 = dag.add_step(SmtProofStep::Assume(not_p));
            let empty = dag.add_step(SmtProofStep::Resolution {
                clause: vec![],
                premises: vec![s0, s1],
                pivot: Some(p),
            });
            dag.add_step(SmtProofStep::Anchor {
                end_step: empty,
                variables: vec![],
            });

            dag
        }

        let dag_a = build_direct_refutation();
        let dag_b = build_anchored_refutation();

        let formula = b"(assert p)\n(assert (not p))";
        let proof_a = b"(assume p)\n(assume (not p))\n(resolution)";
        let proof_b = b"(assume p)\n(assume (not p))\n(resolution)\n(anchor)";

        let result_a = verify_smt_proof(&dag_a, VerifyMode::Strict);
        let result_b = verify_smt_proof(&dag_b, VerifyMode::Strict);
        assert!(
            result_a.valid,
            "direct proof should verify before hashing: {:?}",
            result_a.first_error
        );
        assert!(
            result_b.valid,
            "anchored proof should verify before hashing: {:?}",
            result_b.first_error
        );

        let cert_a = generate_certificate(
            &dag_a,
            &result_a,
            formula,
            proof_a,
            "smt_dag",
            VerifyMode::Strict,
        );
        let cert_b = generate_certificate(
            &dag_b,
            &result_b,
            formula,
            proof_b,
            "smt_dag",
            VerifyMode::Strict,
        );

        verify_certificate(&cert_a, &dag_a, formula, proof_a)
            .expect("certificate A should verify against proof A");
        verify_certificate(&cert_b, &dag_b, formula, proof_b)
            .expect("certificate B should verify against proof B");

        assert_ne!(cert_a.num_steps, cert_b.num_steps);
        assert_eq!(cert_a.formula_hash, cert_b.formula_hash);
        assert_eq!(
            cert_a.formula_hash,
            blake3::hash(formula).to_hex().to_string()
        );
        assert_eq!(
            cert_a.proof_hash,
            blake3::hash(proof_a).to_hex().to_string()
        );
        assert_eq!(
            cert_b.proof_hash,
            blake3::hash(proof_b).to_hex().to_string()
        );
        assert_ne!(
            cert_a.proof_hash, cert_b.proof_hash,
            "proof_hash must change when proof bytes change, even if formula bytes are identical"
        );

        let err = verify_certificate(&cert_a, &dag_a, formula, proof_b)
            .expect_err("certificate A must not accept proof B's bytes");
        assert!(matches!(err, CertificateError::ProofHashMismatch { .. }));
    }
}
