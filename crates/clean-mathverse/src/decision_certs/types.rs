// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Core types for SAT certificate import into the Mathverse Library.
//!
//! Defines the structured representations for CNF formulas, DRAT proof steps,
//! LRAT proof steps, and verification results. These types are the interchange
//! format between parsers (`drat.rs`, `lrat.rs`) and the shard writer.

use serde::{Deserialize, Serialize};

use crate::types::{AxiomProfile, Provenance, SourceSystem, TrustLevel};

// ---------------------------------------------------------------------------
// CNF Formula
// ---------------------------------------------------------------------------

/// A propositional formula in conjunctive normal form.
///
/// Variables are positive integers (1-indexed). Literals are signed: positive
/// means the variable is true, negative means false.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct CnfFormula {
    /// Number of distinct variables in the formula.
    pub num_vars: u32,
    /// Clauses: each clause is a disjunction of literals.
    pub clauses: Vec<Vec<i32>>,
}

impl CnfFormula {
    /// Create a new CNF formula.
    #[must_use]
    pub fn new(num_vars: u32, clauses: Vec<Vec<i32>>) -> Self {
        Self { num_vars, clauses }
    }

    /// Number of clauses in the formula.
    #[must_use]
    pub fn num_clauses(&self) -> usize {
        self.clauses.len()
    }

    /// Compute `num_vars` from the clauses by scanning for the maximum variable.
    #[must_use]
    pub fn compute_num_vars(clauses: &[Vec<i32>]) -> u32 {
        clauses
            .iter()
            .flat_map(|c| c.iter())
            .map(|lit| lit.unsigned_abs())
            .max()
            .unwrap_or(0)
    }
}

// ---------------------------------------------------------------------------
// DRAT types
// ---------------------------------------------------------------------------

/// Kind of DRAT proof step.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum DratStepKind {
    /// Add a clause (RUP or RAT).
    Add,
    /// Delete a clause.
    Delete,
}

/// A single step in a DRAT proof.
///
/// DRAT (Deletion Resolution Asymmetric Tautology) certificates consist of
/// clause additions (which must be RUP or RAT with respect to the current
/// formula) and clause deletions.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct DratStep {
    /// Whether this step adds or deletes a clause.
    pub kind: DratStepKind,
    /// The clause literals.
    pub clause: Vec<i32>,
}

impl DratStep {
    /// Create a new addition step.
    #[must_use]
    pub fn add(clause: Vec<i32>) -> Self {
        Self {
            kind: DratStepKind::Add,
            clause,
        }
    }

    /// Create a new deletion step.
    #[must_use]
    pub fn delete(clause: Vec<i32>) -> Self {
        Self {
            kind: DratStepKind::Delete,
            clause,
        }
    }
}

// ---------------------------------------------------------------------------
// LRAT types
// ---------------------------------------------------------------------------

/// Kind of LRAT proof step.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum LratStepKind {
    /// Add a clause with resolution hints.
    Add,
    /// Delete clauses by ID.
    Delete,
}

/// A single step in an LRAT proof.
///
/// LRAT (Linear Resolution Asymmetric Tautology) extends DRAT with clause IDs
/// and resolution hints, making verification linear-time.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct LratStep {
    /// Clause ID (unique, monotonically increasing for additions).
    pub id: u64,
    /// Whether this step adds or deletes.
    pub kind: LratStepKind,
    /// The clause literals (empty for deletion steps).
    pub clause: Vec<i32>,
    /// Resolution hints: clause IDs used to derive this clause (additions)
    /// or clause IDs to delete (deletions).
    pub hints: Vec<u64>,
}

impl LratStep {
    /// Create a new addition step.
    #[must_use]
    pub fn add(id: u64, clause: Vec<i32>, hints: Vec<u64>) -> Self {
        Self {
            id,
            kind: LratStepKind::Add,
            clause,
            hints,
        }
    }

    /// Create a new deletion step.
    #[must_use]
    pub fn delete(id: u64, hints: Vec<u64>) -> Self {
        Self {
            id,
            kind: LratStepKind::Delete,
            clause: Vec::new(),
            hints,
        }
    }
}

// ---------------------------------------------------------------------------
// SAT Certificate (unified)
// ---------------------------------------------------------------------------

/// Format of the SAT proof certificate.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum SatCertFormat {
    /// Text DRAT.
    DratText,
    /// Binary DRAT.
    DratBinary,
    /// Text LRAT.
    LratText,
}

/// A parsed SAT solver proof certificate.
///
/// Unifies DRAT and LRAT formats. The `proof_steps` field holds the generic
/// step representation; the original format is recorded in `format`.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct SatCertificate {
    /// The original CNF formula the certificate applies to.
    pub formula: CnfFormula,
    /// Proof steps (DRAT steps are stored without hints).
    pub drat_steps: Vec<DratStep>,
    /// LRAT steps (empty if format is DRAT).
    pub lrat_steps: Vec<LratStep>,
    /// Certificate format.
    pub format: SatCertFormat,
    /// Name of the verifier tool that produced this certificate, if known.
    pub verifier_tool: Option<String>,
}

impl SatCertificate {
    /// Total number of proof steps (additions only, excluding deletions).
    #[must_use]
    pub fn addition_count(&self) -> usize {
        match self.format {
            SatCertFormat::DratText | SatCertFormat::DratBinary => self
                .drat_steps
                .iter()
                .filter(|s| s.kind == DratStepKind::Add)
                .count(),
            SatCertFormat::LratText => self
                .lrat_steps
                .iter()
                .filter(|s| s.kind == LratStepKind::Add)
                .count(),
        }
    }

    /// Total number of deletion steps.
    #[must_use]
    pub fn deletion_count(&self) -> usize {
        match self.format {
            SatCertFormat::DratText | SatCertFormat::DratBinary => self
                .drat_steps
                .iter()
                .filter(|s| s.kind == DratStepKind::Delete)
                .count(),
            SatCertFormat::LratText => self
                .lrat_steps
                .iter()
                .filter(|s| s.kind == LratStepKind::Delete)
                .count(),
        }
    }
}

// ---------------------------------------------------------------------------
// Verification result
// ---------------------------------------------------------------------------

/// Result of verifying a SAT certificate.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct CertificateVerifyResult {
    /// Whether the certificate is valid.
    pub valid: bool,
    /// Verification statistics.
    pub stats: VerifyStats,
    /// Error message if verification failed.
    pub error: Option<String>,
}

/// Statistics from certificate verification.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct VerifyStats {
    /// Number of RUP checks performed.
    pub rup_checks: u64,
    /// Number of RAT checks performed.
    pub rat_checks: u64,
    /// Number of clause deletions processed.
    pub deletions_processed: u64,
    /// Peak number of active clauses during verification.
    pub peak_active_clauses: u64,
}

// ---------------------------------------------------------------------------
// Provenance / trust helpers
// ---------------------------------------------------------------------------

/// Axiom profile for a SAT certificate entry in the Mathverse shard.
#[must_use]
pub fn sat_cert_axiom_profile() -> AxiomProfile {
    AxiomProfile::SAT_CERT
}

/// Trust level for a SAT certificate.
///
/// SOUNDNESS: `TrustLevel::CertificateReplayed` asserts the certificate's proof
/// steps were REPLAYED (re-checked). clean-mathverse has NO RUP/RAT/resolution
/// replay checker — `drat`/`lrat` only PARSE the certificate, and the
/// [`CertificateVerifyResult`]/[`VerifyStats`] types are never populated by any
/// production path. Granting LRAT `CertificateReplayed` merely for CARRYING
/// resolution hints therefore overclaimed: an LRAT file whose steps do not
/// actually derive the empty clause — or that certifies a satisfiable formula as
/// UNSAT — would be labeled "replayed" although nothing checked it. Until a real
/// replay checker gates the verdict, every parsed-but-unreplayed certificate is
/// honestly `PartiallyAxiomatized` (the UNSAT claim is taken on the solver's
/// word, not re-derived). `format` is retained for API/call-site stability.
#[must_use]
pub fn sat_cert_trust_level(_format: SatCertFormat) -> TrustLevel {
    TrustLevel::PartiallyAxiomatized
}

/// Build a provenance record for a SAT certificate.
#[must_use]
pub fn sat_cert_provenance(cert: &SatCertificate, source_file: Option<&str>) -> Provenance {
    let format_tag = match cert.format {
        SatCertFormat::DratText => "drat_text",
        SatCertFormat::DratBinary => "drat_binary",
        SatCertFormat::LratText => "lrat_text",
    };
    Provenance {
        source: SourceSystem::SatSolver,
        original_name: format!(
            "sat_cert_{fmt}_{vars}v_{cls}c",
            fmt = format_tag,
            vars = cert.formula.num_vars,
            cls = cert.formula.num_clauses(),
        ),
        source_file: source_file.map(|s| s.to_owned()),
        axiom_profile: sat_cert_axiom_profile(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_cnf_formula_new() {
        let f = CnfFormula::new(3, vec![vec![1, -2], vec![2, 3]]);
        assert_eq!(f.num_vars, 3);
        assert_eq!(f.num_clauses(), 2);
    }

    #[test]
    fn test_cnf_formula_compute_num_vars() {
        let clauses = vec![vec![1, -5], vec![3, -2]];
        assert_eq!(CnfFormula::compute_num_vars(&clauses), 5);
    }

    #[test]
    fn test_cnf_formula_compute_num_vars_empty() {
        let clauses: Vec<Vec<i32>> = vec![];
        assert_eq!(CnfFormula::compute_num_vars(&clauses), 0);
    }

    #[test]
    fn test_drat_step_constructors() {
        let add = DratStep::add(vec![1, -2, 3]);
        assert_eq!(add.kind, DratStepKind::Add);
        assert_eq!(add.clause, vec![1, -2, 3]);

        let del = DratStep::delete(vec![1, 2]);
        assert_eq!(del.kind, DratStepKind::Delete);
        assert_eq!(del.clause, vec![1, 2]);
    }

    #[test]
    fn test_lrat_step_constructors() {
        let add = LratStep::add(5, vec![1, -3], vec![1, 2, 3]);
        assert_eq!(add.id, 5);
        assert_eq!(add.kind, LratStepKind::Add);
        assert_eq!(add.clause, vec![1, -3]);
        assert_eq!(add.hints, vec![1, 2, 3]);

        let del = LratStep::delete(6, vec![1, 4]);
        assert_eq!(del.id, 6);
        assert_eq!(del.kind, LratStepKind::Delete);
        assert!(del.clause.is_empty());
        assert_eq!(del.hints, vec![1, 4]);
    }

    #[test]
    fn test_sat_certificate_counts() {
        let cert = SatCertificate {
            formula: CnfFormula::new(3, vec![vec![1, 2], vec![-1, 3]]),
            drat_steps: vec![
                DratStep::add(vec![1]),
                DratStep::delete(vec![1, 2]),
                DratStep::add(vec![]),
            ],
            lrat_steps: Vec::new(),
            format: SatCertFormat::DratText,
            verifier_tool: None,
        };
        assert_eq!(cert.addition_count(), 2);
        assert_eq!(cert.deletion_count(), 1);
    }

    #[test]
    fn test_sat_cert_trust_level_lrat_not_overclaimed_as_replayed() {
        // No RUP/RAT replay checker exists, so an LRAT certificate is parsed but
        // NOT replayed — it must never be labeled `CertificateReplayed`.
        let level = sat_cert_trust_level(SatCertFormat::LratText);
        assert_eq!(level, TrustLevel::PartiallyAxiomatized);
        assert_ne!(level, TrustLevel::CertificateReplayed);
    }

    #[test]
    fn test_sat_cert_trust_level_drat() {
        assert_eq!(
            sat_cert_trust_level(SatCertFormat::DratText),
            TrustLevel::PartiallyAxiomatized,
        );
        assert_eq!(
            sat_cert_trust_level(SatCertFormat::DratBinary),
            TrustLevel::PartiallyAxiomatized,
        );
    }

    #[test]
    fn test_sat_cert_provenance() {
        let cert = SatCertificate {
            formula: CnfFormula::new(10, vec![vec![1]; 5]),
            drat_steps: Vec::new(),
            lrat_steps: Vec::new(),
            format: SatCertFormat::DratText,
            verifier_tool: Some("drat-trim".to_string()),
        };
        let prov = sat_cert_provenance(&cert, Some("test.drat"));
        assert_eq!(prov.source, SourceSystem::SatSolver);
        assert!(prov.original_name.contains("drat_text"));
        assert!(prov.original_name.contains("10v"));
        assert!(prov.original_name.contains("5c"));
        assert_eq!(prov.source_file.as_deref(), Some("test.drat"));
        assert!(prov.axiom_profile.has(AxiomProfile::SAT_CERT));
    }

    #[test]
    fn test_verify_result_serde_roundtrip() {
        let result = CertificateVerifyResult {
            valid: true,
            stats: VerifyStats {
                rup_checks: 100,
                rat_checks: 5,
                deletions_processed: 20,
                peak_active_clauses: 50,
            },
            error: None,
        };
        let json = serde_json::to_string(&result).expect("should serialize");
        let back: CertificateVerifyResult =
            serde_json::from_str(&json).expect("should deserialize");
        assert!(back.valid);
        assert_eq!(back.stats.rup_checks, 100);
        assert_eq!(back.stats.rat_checks, 5);
    }
}
