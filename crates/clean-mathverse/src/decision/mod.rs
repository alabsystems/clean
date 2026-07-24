// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Decision procedure certificate importers for the Mathverse Library.
//!
//! Parses proof certificates from SAT solvers (DRAT/LRAT), SMT solvers
//! (Alethe/LFSC), and first-order ATP (TSTP/TPTP). Each certificate
//! gets an Mathverse entry with appropriate trust level and axiom profile.

use std::path::Path;

use crate::types::{AxiomProfile, Provenance, SourceSystem, TrustLevel};

use thiserror::Error;

/// Errors from certificate import.
#[derive(Debug, Error)]
#[non_exhaustive]
pub enum CertError {
    #[error("IO error: {0}")]
    Io(#[from] std::io::Error),
    #[error("invalid certificate format: {message}")]
    Format { message: String },
    #[error("certificate verification failed: {message}")]
    Verification { message: String },
}

// ─── DRAT/LRAT (SAT solver certificates) ────────────────────────────────

/// A clause from a DRAT/LRAT certificate.
#[derive(Clone, Debug)]
pub struct SatClause {
    /// Clause ID (LRAT) or index (DRAT).
    pub id: u64,
    /// Literals in the clause (positive = true, negative = false).
    pub literals: Vec<i64>,
    /// Whether this is an addition or deletion.
    pub kind: ClauseKind,
    /// For LRAT: antecedent clause IDs used in the resolution proof.
    pub antecedents: Vec<u64>,
}

/// Kind of clause operation in a proof certificate.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ClauseKind {
    /// Original problem clause.
    Original,
    /// Added by the solver (RAT/RUP).
    Addition,
    /// Deleted clause (optimization).
    Deletion,
}

/// Parsed SAT certificate.
#[derive(Clone, Debug)]
pub struct SatCertificate {
    pub format: SatCertFormat,
    pub clauses: Vec<SatClause>,
    pub variables: u64,
    pub original_clauses: u64,
    pub proof_steps: u64,
}

/// SAT certificate format.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SatCertFormat {
    Drat,
    Lrat,
    DratBinary,
}

/// Parse a DRAT text certificate.
pub fn parse_drat(text: &str) -> Result<SatCertificate, CertError> {
    let mut clauses = Vec::new();
    let mut max_var = 0u64;
    let mut proof_steps = 0u64;

    for line in text.lines() {
        let trimmed = line.trim();
        if trimmed.is_empty() || trimmed.starts_with('c') {
            continue;
        }

        let kind = if trimmed.starts_with('d') {
            ClauseKind::Deletion
        } else {
            proof_steps += 1;
            ClauseKind::Addition
        };

        let nums_str = if kind == ClauseKind::Deletion {
            &trimmed[1..]
        } else {
            trimmed
        };

        let literals: Vec<i64> = nums_str
            .split_whitespace()
            .filter_map(|s| s.parse::<i64>().ok())
            .filter(|&n| n != 0) // 0 terminates clause
            .collect();

        for &lit in &literals {
            let var = lit.unsigned_abs();
            if var > max_var {
                max_var = var;
            }
        }

        clauses.push(SatClause {
            id: clauses.len() as u64,
            literals,
            kind,
            antecedents: Vec::new(),
        });
    }

    let original_clauses = clauses
        .iter()
        .filter(|c| c.kind == ClauseKind::Original)
        .count() as u64;

    Ok(SatCertificate {
        format: SatCertFormat::Drat,
        clauses,
        variables: max_var,
        original_clauses,
        proof_steps,
    })
}

/// Parse an LRAT text certificate.
pub fn parse_lrat(text: &str) -> Result<SatCertificate, CertError> {
    let mut clauses = Vec::new();
    let mut max_var = 0u64;
    let mut proof_steps = 0u64;

    for line in text.lines() {
        let trimmed = line.trim();
        if trimmed.is_empty() || trimmed.starts_with('c') {
            continue;
        }

        let tokens: Vec<&str> = trimmed.split_whitespace().collect();
        if tokens.is_empty() {
            continue;
        }

        let id = tokens[0].parse::<u64>().unwrap_or(0);

        if tokens.len() > 1 && tokens[1] == "d" {
            // Deletion line: "id d c1 c2 ... 0"
            let deleted: Vec<u64> = tokens[2..]
                .iter()
                .filter_map(|s| s.parse::<u64>().ok())
                .filter(|&n| n != 0)
                .collect();
            clauses.push(SatClause {
                id,
                literals: Vec::new(),
                kind: ClauseKind::Deletion,
                antecedents: deleted,
            });
        } else {
            // Addition line: "id lit1 lit2 ... 0 ante1 ante2 ... 0"
            proof_steps += 1;
            let rest = &tokens[1..];
            let mut literals = Vec::new();
            let mut antecedents = Vec::new();
            let mut past_zero = false;

            for &tok in rest {
                if tok == "0" {
                    if past_zero {
                        break;
                    }
                    past_zero = true;
                    continue;
                }
                if past_zero {
                    if let Ok(a) = tok.parse::<u64>() {
                        antecedents.push(a);
                    }
                } else if let Ok(lit) = tok.parse::<i64>() {
                    let var = lit.unsigned_abs();
                    if var > max_var {
                        max_var = var;
                    }
                    literals.push(lit);
                }
            }

            clauses.push(SatClause {
                id,
                literals,
                kind: ClauseKind::Addition,
                antecedents,
            });
        }
    }

    let original_clauses = clauses
        .iter()
        .filter(|c| c.kind == ClauseKind::Original)
        .count() as u64;

    Ok(SatCertificate {
        format: SatCertFormat::Lrat,
        clauses,
        variables: max_var,
        original_clauses,
        proof_steps,
    })
}

// ─── TSTP (First-order ATP certificates) ────────────────────────────────

/// A step in a TSTP proof.
#[derive(Clone, Debug)]
pub struct TstpStep {
    pub name: String,
    pub role: TstpRole,
    pub formula: String,
    pub source: String,
}

/// Role of a TSTP formula.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum TstpRole {
    Axiom,
    Hypothesis,
    Conjecture,
    NegatedConjecture,
    Lemma,
    Theorem,
    Plain,
}

/// Parsed TSTP proof.
#[derive(Clone, Debug)]
pub struct TstpProof {
    pub steps: Vec<TstpStep>,
    pub status: TstpStatus,
}

/// TSTP SZS status.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum TstpStatus {
    Theorem,
    Unsatisfiable,
    CounterSatisfiable,
    Satisfiable,
    Unknown,
}

/// Parse a TSTP proof output.
pub fn parse_tstp(text: &str) -> Result<TstpProof, CertError> {
    let mut steps = Vec::new();
    let mut status = TstpStatus::Unknown;

    for line in text.lines() {
        let trimmed = line.trim();

        // SZS status line
        if trimmed.contains("SZS status") {
            if trimmed.contains("Theorem") {
                status = TstpStatus::Theorem;
            } else if trimmed.contains("Unsatisfiable") {
                status = TstpStatus::Unsatisfiable;
            } else if trimmed.contains("CounterSatisfiable") {
                status = TstpStatus::CounterSatisfiable;
            } else if trimmed.contains("Satisfiable") {
                status = TstpStatus::Satisfiable;
            }
            continue;
        }

        // TSTP formula: fof(name,role,formula,source).
        if trimmed.starts_with("fof(") || trimmed.starts_with("cnf(") || trimmed.starts_with("thf(")
        {
            if let Some(inner) = trimmed
                .strip_prefix("fof(")
                .or_else(|| trimmed.strip_prefix("cnf("))
                .or_else(|| trimmed.strip_prefix("thf("))
            {
                let inner = inner.trim_end_matches(").");
                let parts: Vec<&str> = inner.splitn(4, ',').collect();
                if parts.len() >= 3 {
                    let name = parts[0].trim().to_owned();
                    let role_str = parts[1].trim();
                    let formula = parts[2].trim().to_owned();
                    let source = parts.get(3).map_or("", |s| s.trim()).to_owned();

                    let role = match role_str {
                        "axiom" => TstpRole::Axiom,
                        "hypothesis" => TstpRole::Hypothesis,
                        "conjecture" => TstpRole::Conjecture,
                        "negated_conjecture" => TstpRole::NegatedConjecture,
                        "lemma" => TstpRole::Lemma,
                        "theorem" => TstpRole::Theorem,
                        _ => TstpRole::Plain,
                    };

                    steps.push(TstpStep {
                        name,
                        role,
                        formula,
                        source,
                    });
                }
            }
        }
    }

    Ok(TstpProof { steps, status })
}

// ─── Provenance helpers ──────────────────────────────────────────────────

/// Axiom profile for a SAT certificate.
#[must_use]
pub fn sat_cert_profile(_cert: &SatCertificate) -> AxiomProfile {
    AxiomProfile::SAT_CERT
}

/// Trust level for a SAT certificate.
///
/// SOUNDNESS: no RUP/RAT replay checker exists in clean-mathverse (the parsers
/// only PARSE the certificate), so no SAT certificate is ever actually replayed.
/// `TrustLevel::CertificateReplayed` would be an overclaim; an unreplayed
/// certificate is honestly `PartiallyAxiomatized` (its UNSAT claim is taken on
/// the solver's word, not re-derived). See
/// [`crate::decision_certs::types::sat_cert_trust_level`].
#[must_use]
pub fn sat_cert_trust(_cert: &SatCertificate) -> TrustLevel {
    TrustLevel::PartiallyAxiomatized
}

/// Axiom profile for a TSTP proof.
#[must_use]
pub fn tstp_profile(_proof: &TstpProof) -> AxiomProfile {
    AxiomProfile::ATP_CERT
}

/// Trust level for a TSTP proof.
///
/// SOUNDNESS: the SZS status is SELF-ASSERTED by the ATP in its output;
/// [`parse_tstp`] reads that status line and does NOT replay the proof steps.
/// A self-asserted "Theorem"/"Unsatisfiable" is a trusted-oracle claim, NOT a
/// replayed certificate — labeling it `CertificateReplayed` would assert a
/// re-derivation that never happened. It is honestly `TrustedOracle`.
#[must_use]
pub fn tstp_trust(_proof: &TstpProof) -> TrustLevel {
    TrustLevel::TrustedOracle
}

/// Provenance for a SAT certificate.
#[must_use]
pub fn sat_provenance(cert: &SatCertificate, file: Option<&str>) -> Provenance {
    Provenance {
        source: SourceSystem::SatSolver,
        original_name: format!("sat_cert_{}", cert.variables),
        source_file: file.map(|s| s.to_owned()),
        axiom_profile: sat_cert_profile(cert),
    }
}

/// Provenance for a TSTP proof.
#[must_use]
pub fn tstp_provenance(proof: &TstpProof, file: Option<&str>) -> Provenance {
    Provenance {
        source: SourceSystem::Atp,
        original_name: format!("tstp_proof_{}_steps", proof.steps.len()),
        source_file: file.map(|s| s.to_owned()),
        axiom_profile: tstp_profile(proof),
    }
}

/// Import statistics for decision procedure certificates.
#[derive(Clone, Debug, Default)]
pub struct DecisionImportStats {
    pub sat_certs_parsed: usize,
    pub sat_certs_failed: usize,
    pub tstp_proofs_parsed: usize,
    pub tstp_proofs_failed: usize,
    pub total_proof_steps: u64,
    pub total_variables: u64,
}

/// Batch import SAT certificates from a directory.
pub fn import_sat_certs_dir(
    dir: &Path,
) -> Result<(Vec<SatCertificate>, DecisionImportStats), CertError> {
    let mut certs = Vec::new();
    let mut stats = DecisionImportStats::default();
    let mut files = Vec::new();
    collect_files(dir, "drat", &mut files);
    collect_files(dir, "lrat", &mut files);
    files.sort();

    for path in &files {
        let text = std::fs::read_to_string(path)?;
        let is_lrat = path.extension().is_some_and(|e| e == "lrat");
        let result = if is_lrat {
            parse_lrat(&text)
        } else {
            parse_drat(&text)
        };

        match result {
            Ok(cert) => {
                stats.total_proof_steps += cert.proof_steps;
                stats.total_variables += cert.variables;
                stats.sat_certs_parsed += 1;
                certs.push(cert);
            }
            Err(_) => stats.sat_certs_failed += 1,
        }
    }

    Ok((certs, stats))
}

fn collect_files(dir: &Path, ext: &str, out: &mut Vec<std::path::PathBuf>) {
    if let Ok(rd) = std::fs::read_dir(dir) {
        for entry in rd.filter_map(|e| e.ok()) {
            let path = entry.path();
            if path.is_dir() {
                collect_files(&path, ext, out);
            } else if path.extension().is_some_and(|e| e == ext) {
                out.push(path);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_drat_basic() {
        let cert = "1 2 0\n-1 3 0\nd 1 2 0\n";
        let result = parse_drat(cert).unwrap();
        assert_eq!(result.format, SatCertFormat::Drat);
        assert_eq!(result.clauses.len(), 3);
        assert_eq!(result.proof_steps, 2);
        assert_eq!(result.variables, 3);
    }

    #[test]
    fn test_parse_lrat_basic() {
        let cert = "1 1 2 0 0\n2 -1 3 0 1 0\n3 d 1 0\n";
        let result = parse_lrat(cert).unwrap();
        assert_eq!(result.format, SatCertFormat::Lrat);
        assert_eq!(result.clauses.len(), 3);
        assert_eq!(result.proof_steps, 2);
    }

    #[test]
    fn test_parse_tstp_theorem() {
        let proof = "\
% SZS status Theorem
fof(ax1,axiom,p(a)).
fof(goal,conjecture,p(a)).
fof(step1,plain,p(a),inference(trivial,[],[ax1])).
";
        let result = parse_tstp(proof).unwrap();
        assert_eq!(result.status, TstpStatus::Theorem);
        assert_eq!(result.steps.len(), 3);
        assert_eq!(result.steps[0].role, TstpRole::Axiom);
        assert_eq!(result.steps[1].role, TstpRole::Conjecture);
    }

    #[test]
    fn test_sat_cert_trust_lrat_not_overclaimed_as_replayed() {
        // No RUP/RAT replay checker exists, so a parsed LRAT certificate is never
        // actually replayed — it must not be labeled `CertificateReplayed`.
        let cert = SatCertificate {
            format: SatCertFormat::Lrat,
            clauses: Vec::new(),
            variables: 10,
            original_clauses: 5,
            proof_steps: 3,
        };
        assert_eq!(sat_cert_trust(&cert), TrustLevel::PartiallyAxiomatized);
        assert_ne!(sat_cert_trust(&cert), TrustLevel::CertificateReplayed);
    }

    #[test]
    fn test_tstp_trust_theorem_is_oracle_not_replayed() {
        // The SZS status is self-asserted by the ATP; nothing replays the proof,
        // so a "Theorem" status is a trusted-oracle claim, not a replayed cert.
        let proof = TstpProof {
            steps: Vec::new(),
            status: TstpStatus::Theorem,
        };
        assert_eq!(tstp_trust(&proof), TrustLevel::TrustedOracle);
        assert_ne!(tstp_trust(&proof), TrustLevel::CertificateReplayed);
    }

    #[test]
    fn test_tstp_trust_unknown() {
        let proof = TstpProof {
            steps: Vec::new(),
            status: TstpStatus::Unknown,
        };
        assert_eq!(tstp_trust(&proof), TrustLevel::TrustedOracle);
    }
}
