// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Polynomial Calculus proof certificates for export and replay.
//!
//! Provides a text-based certificate format compatible with the proof
//! complexity literature, plus a binary format for compact storage.
//!
//! ## Text Format
//!
//! The text format is human-readable and designed for interoperability
//! with academic proof checkers:
//!
//! ```text
//! PC-GF2 v1
//! CLAUSES 3
//! STEPS 6
//! MAXDEG 2
//! ---
//! 0 AXIOM 0
//! 1 AXIOM 1
//! 2 AXIOM 2
//! 3 MULVAR 0 1
//! 4 ADD 2 3
//! 5 ADD 1 4
//! ---
//! RESULT 1
//! ```
//!
//! ## Binary Format
//!
//! See [`super::gf2_algebra::pc_to_competition_certificate`] for the
//! binary format (magic `PC2\0`, LE32 records).
//!
//! ## Replay Verification
//!
//! [`PcCertificateVerifier`] replays certificate steps against a given
//! clause set and verifies the derivation is sound.
//!
//! ## References
//!
//! - Clegg, Edmonds, Impagliazzo (1996). Using the Groebner basis
//!   algorithm to find proofs of unsatisfiability. STOC'96.

use std::collections::BTreeSet;

use super::gf2_algebra::{Gf2Poly, PcError, PcProof, PcStepTracked};

use thiserror::Error;

// ---------------------------------------------------------------------------
// Error types
// ---------------------------------------------------------------------------

/// Errors from certificate parsing and verification.
#[derive(Debug, Clone, Error)]
#[non_exhaustive]
pub enum CertificateError {
    /// The certificate header is malformed.
    #[error("malformed header: {0}")]
    MalformedHeader(String),

    /// A step line is malformed.
    #[error("malformed step at line {line}: {reason}")]
    MalformedStep { line: usize, reason: String },

    /// The step count does not match the actual number of steps.
    #[error("header claims {expected} steps but found {actual}")]
    StepCountMismatch { expected: usize, actual: usize },

    /// Replay verification failed.
    #[error("replay failed: {0}")]
    ReplayError(#[from] PcError),

    /// The certificate result does not match the replayed proof.
    #[error("result mismatch: certificate claims {claimed}, replay produced {actual}")]
    ResultMismatch { claimed: String, actual: String },
}

// ---------------------------------------------------------------------------
// PcCertificate
// ---------------------------------------------------------------------------

/// A Polynomial Calculus proof certificate.
///
/// Contains the proof steps, clause count, and metadata for serialization
/// and replay verification.
#[derive(Debug, Clone)]
pub struct PcCertificate {
    /// Number of clauses in the axiom pool.
    pub num_clauses: usize,
    /// The proof steps.
    pub steps: Vec<PcStepTracked>,
    /// Maximum degree encountered during the proof.
    pub max_degree: usize,
}

impl PcCertificate {
    /// Create a certificate from a verified proof.
    #[must_use]
    pub fn from_proof(proof: &PcProof, num_clauses: usize) -> Self {
        Self {
            num_clauses,
            steps: proof.steps.clone(),
            max_degree: proof.max_degree,
        }
    }

    /// Create a certificate from raw steps.
    #[must_use]
    pub fn new(num_clauses: usize, steps: Vec<PcStepTracked>, max_degree: usize) -> Self {
        Self {
            num_clauses,
            steps,
            max_degree,
        }
    }

    /// Serialize the certificate to the text format.
    #[must_use]
    pub fn to_text(&self) -> String {
        let mut out = String::new();

        // Header
        out.push_str("PC-GF2 v1\n");
        out.push_str(&format!("CLAUSES {}\n", self.num_clauses));
        out.push_str(&format!("STEPS {}\n", self.steps.len()));
        out.push_str(&format!("MAXDEG {}\n", self.max_degree));
        out.push_str("---\n");

        // Steps
        for (idx, step) in self.steps.iter().enumerate() {
            match step {
                PcStepTracked::ClauseAxiom(clause_idx) => {
                    out.push_str(&format!("{idx} AXIOM {clause_idx}\n"));
                }
                PcStepTracked::BooleanAxiom(var) => {
                    out.push_str(&format!("{idx} BOOLAX {var}\n"));
                }
                PcStepTracked::Add(i, j) => {
                    out.push_str(&format!("{idx} ADD {i} {j}\n"));
                }
                PcStepTracked::MulVar(i, var) => {
                    out.push_str(&format!("{idx} MULVAR {i} {var}\n"));
                }
                PcStepTracked::MulPoly(i, j) => {
                    out.push_str(&format!("{idx} MULPOLY {i} {j}\n"));
                }
                PcStepTracked::Weaken(i, mono_vars) => {
                    let vars_str: Vec<String> = mono_vars.iter().map(|v| v.to_string()).collect();
                    out.push_str(&format!("{idx} WEAKEN {i} {}\n", vars_str.join(",")));
                }
            }
        }

        out.push_str("---\n");
        out.push_str("RESULT 1\n");

        out
    }

    /// Parse a certificate from the text format.
    ///
    /// # Errors
    ///
    /// Returns `CertificateError` if the text is malformed.
    pub fn from_text(text: &str) -> Result<Self, CertificateError> {
        let lines: Vec<&str> = text.lines().collect();

        if lines.is_empty() {
            return Err(CertificateError::MalformedHeader(
                "empty certificate".to_string(),
            ));
        }

        // Parse header
        if !lines[0].starts_with("PC-GF2 v") {
            return Err(CertificateError::MalformedHeader(format!(
                "expected 'PC-GF2 v1', got '{}'",
                lines[0]
            )));
        }

        let mut num_clauses = 0;
        let mut expected_steps = 0;
        let mut max_degree = 0;
        let mut step_start = 0;

        for (i, line) in lines.iter().enumerate().skip(1) {
            if *line == "---" {
                step_start = i + 1;
                break;
            }
            if let Some(val) = line.strip_prefix("CLAUSES ") {
                num_clauses = val.trim().parse().map_err(|_| {
                    CertificateError::MalformedHeader(format!("bad CLAUSES: {line}"))
                })?;
            } else if let Some(val) = line.strip_prefix("STEPS ") {
                expected_steps = val
                    .trim()
                    .parse()
                    .map_err(|_| CertificateError::MalformedHeader(format!("bad STEPS: {line}")))?;
            } else if let Some(val) = line.strip_prefix("MAXDEG ") {
                max_degree = val.trim().parse().map_err(|_| {
                    CertificateError::MalformedHeader(format!("bad MAXDEG: {line}"))
                })?;
            }
        }

        // Parse steps
        let mut steps = Vec::with_capacity(expected_steps);
        for (offset, line) in lines[step_start..].iter().enumerate() {
            let line = line.trim();
            if line == "---" || line.starts_with("RESULT") || line.is_empty() {
                break;
            }

            let line_num = step_start + offset;
            let step = parse_step_line(line, line_num)?;
            steps.push(step);
        }

        if expected_steps > 0 && steps.len() != expected_steps {
            return Err(CertificateError::StepCountMismatch {
                expected: expected_steps,
                actual: steps.len(),
            });
        }

        Ok(Self {
            num_clauses,
            steps,
            max_degree,
        })
    }
}

/// Parse a single step line from the text format.
fn parse_step_line(line: &str, line_num: usize) -> Result<PcStepTracked, CertificateError> {
    let parts: Vec<&str> = line.split_whitespace().collect();
    if parts.len() < 2 {
        return Err(CertificateError::MalformedStep {
            line: line_num,
            reason: format!("too few tokens: '{line}'"),
        });
    }

    // Skip the step index (parts[0])
    let op = parts[1];

    match op {
        "AXIOM" => {
            let clause_idx: usize = parse_usize(parts.get(2), line_num, "clause index")?;
            Ok(PcStepTracked::ClauseAxiom(clause_idx))
        }
        "BOOLAX" => {
            let var: u32 = parse_u32(parts.get(2), line_num, "variable")?;
            Ok(PcStepTracked::BooleanAxiom(var))
        }
        "ADD" => {
            let i: usize = parse_usize(parts.get(2), line_num, "left index")?;
            let j: usize = parse_usize(parts.get(3), line_num, "right index")?;
            Ok(PcStepTracked::Add(i, j))
        }
        "MULVAR" => {
            let i: usize = parse_usize(parts.get(2), line_num, "poly index")?;
            let var: u32 = parse_u32(parts.get(3), line_num, "variable")?;
            Ok(PcStepTracked::MulVar(i, var))
        }
        "MULPOLY" => {
            let i: usize = parse_usize(parts.get(2), line_num, "left index")?;
            let j: usize = parse_usize(parts.get(3), line_num, "right index")?;
            Ok(PcStepTracked::MulPoly(i, j))
        }
        "WEAKEN" => {
            let i: usize = parse_usize(parts.get(2), line_num, "poly index")?;
            let vars_str = parts
                .get(3)
                .ok_or_else(|| CertificateError::MalformedStep {
                    line: line_num,
                    reason: "missing monomial variables".to_string(),
                })?;
            let mono_vars: BTreeSet<u32> = vars_str
                .split(',')
                .map(|s| {
                    s.trim()
                        .parse::<u32>()
                        .map_err(|_| CertificateError::MalformedStep {
                            line: line_num,
                            reason: format!("bad variable in monomial: '{s}'"),
                        })
                })
                .collect::<Result<_, _>>()?;
            Ok(PcStepTracked::Weaken(i, mono_vars))
        }
        _ => Err(CertificateError::MalformedStep {
            line: line_num,
            reason: format!("unknown operation '{op}'"),
        }),
    }
}

fn parse_usize(
    val: Option<&&str>,
    line_num: usize,
    field: &str,
) -> Result<usize, CertificateError> {
    val.ok_or_else(|| CertificateError::MalformedStep {
        line: line_num,
        reason: format!("missing {field}"),
    })?
    .parse()
    .map_err(|_| CertificateError::MalformedStep {
        line: line_num,
        reason: format!("bad {field}"),
    })
}

fn parse_u32(val: Option<&&str>, line_num: usize, field: &str) -> Result<u32, CertificateError> {
    val.ok_or_else(|| CertificateError::MalformedStep {
        line: line_num,
        reason: format!("missing {field}"),
    })?
    .parse()
    .map_err(|_| CertificateError::MalformedStep {
        line: line_num,
        reason: format!("bad {field}"),
    })
}

// ---------------------------------------------------------------------------
// PcCertificateVerifier
// ---------------------------------------------------------------------------

/// Replays a PC certificate against a clause set and verifies soundness.
pub struct PcCertificateVerifier;

impl PcCertificateVerifier {
    /// Replay a certificate against the given clauses.
    ///
    /// Builds a [`PcProof`] from the certificate steps and the clause set,
    /// then verifies the proof derives the constant 1.
    ///
    /// # Errors
    ///
    /// Returns `CertificateError::ReplayError` if any step is invalid.
    /// Returns `CertificateError::ResultMismatch` if the final polynomial
    /// is not the constant 1.
    pub fn verify(
        cert: &PcCertificate,
        clauses: &[Vec<i32>],
    ) -> Result<ReplayResult, CertificateError> {
        let proof = PcProof::build(clauses, cert.steps.clone())?;

        // Verify the final polynomial is 1.
        let last = proof.derived.last().ok_or(PcError::EmptyProof)?;

        if !last.is_one() {
            return Err(CertificateError::ResultMismatch {
                claimed: "1".to_string(),
                actual: format!("{last}"),
            });
        }

        // Verify degree matches.
        let actual_max_degree = proof.max_degree;

        Ok(ReplayResult {
            verified: true,
            num_steps: proof.steps.len(),
            max_degree: actual_max_degree,
            degree_matches: actual_max_degree == cert.max_degree,
            derived_polynomials: proof.derived,
        })
    }
}

/// Result of replaying a certificate.
#[derive(Debug, Clone)]
pub struct ReplayResult {
    /// Whether the certificate verified successfully (final poly = 1).
    pub verified: bool,
    /// Number of proof steps.
    pub num_steps: usize,
    /// Maximum degree encountered during replay.
    pub max_degree: usize,
    /// Whether the claimed max degree matches the actual.
    pub degree_matches: bool,
    /// The derived polynomials from the replay.
    pub derived_polynomials: Vec<Gf2Poly>,
}
