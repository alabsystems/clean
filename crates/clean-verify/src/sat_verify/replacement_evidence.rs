// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Rust-owned bounded evidence for SAT/PB certificate-library replacement.
//!
//! This module is deliberately not a proof replay engine. It is a small,
//! deterministic checker over the executable SAT/PB domain semantics used by
//! proof-factory and CLI evidence. The output is JSON-ready so CLI/report
//! surfaces can consume Rust evidence rather than relying only on Python report
//! wrappers.

use serde::Serialize;

use super::domain::{
    clause_from_dimacs, cnf_from_dimacs_clauses, eval_cardinality, eval_clause_detail,
    eval_cnf_detail, eval_lit, eval_pb_constraint, CardinalityConstraint, CardinalityKind,
    PbComparison, PbConstraint,
};
use super::types::{Assignment, CnfError, Lit, Var};

/// Schema version for [`SatPbReplacementEvidence`].
pub const SAT_PB_REPLACEMENT_EVIDENCE_SCHEMA: &str = "clean-sat-pb-replacement-evidence-v1";

/// Default variable bound for checked-in replacement evidence.
pub const DEFAULT_MAX_VARS: u32 = 4;

/// Configuration for the bounded SAT/PB replacement evidence checker.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub struct SatPbEvidenceConfig {
    /// Enumerate all total assignments up to this variable count.
    pub max_vars: u32,
}

impl Default for SatPbEvidenceConfig {
    fn default() -> Self {
        Self {
            max_vars: DEFAULT_MAX_VARS,
        }
    }
}

/// Top-level Rust evidence packet for SAT/PB replacement review.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct SatPbReplacementEvidence {
    /// Stable schema marker for report/CLI consumers.
    pub schema_version: &'static str,
    /// Producer identity.
    pub generated_by: &'static str,
    /// Replacement status this evidence justifies.
    pub status: &'static str,
    /// The bounded claim made by this evidence.
    pub claim: &'static str,
    /// Claims this bounded checker explicitly does not make.
    pub non_claims: Vec<&'static str>,
    /// Checker configuration.
    pub checker: SatPbEvidenceConfig,
    /// Aggregate summary.
    pub summary: SatPbEvidenceSummary,
    /// Individual check results.
    pub checks: Vec<SatPbEvidenceCheck>,
    /// Remaining blockers before full Lean4 replacement can be claimed.
    pub blockers: Vec<&'static str>,
}

impl SatPbReplacementEvidence {
    /// True when every bounded Rust check passed.
    #[must_use]
    pub fn accepted(&self) -> bool {
        self.checks.iter().all(|check| check.passed)
    }
}

/// Aggregate summary for the evidence packet.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct SatPbEvidenceSummary {
    /// Number of checks executed.
    pub check_count: usize,
    /// Number of checks that passed.
    pub passed_count: usize,
    /// Total checked semantic cases across all checks.
    pub semantic_cases: usize,
    /// Number of total assignments enumerated.
    pub total_assignments_enumerated: usize,
    /// Number of fail-closed invalid-input cases checked.
    pub invalid_input_cases: usize,
    /// Stable digest over check ids, pass/fail states, and case counts.
    pub evidence_digest: String,
}

/// One bounded evidence check.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct SatPbEvidenceCheck {
    /// Stable check id.
    pub id: &'static str,
    /// Human-readable behavior under test.
    pub behavior: &'static str,
    /// Number of checked semantic cases.
    pub semantic_cases: usize,
    /// Number of fail-closed invalid-input cases.
    pub invalid_input_cases: usize,
    /// Whether the check passed.
    pub passed: bool,
    /// Failure diagnostics. Empty iff `passed`.
    pub failures: Vec<String>,
}

impl SatPbEvidenceCheck {
    fn new(id: &'static str, behavior: &'static str) -> Self {
        Self {
            id,
            behavior,
            semantic_cases: 0,
            invalid_input_cases: 0,
            passed: true,
            failures: Vec::new(),
        }
    }

    fn fail(&mut self, message: impl Into<String>) {
        self.passed = false;
        self.failures.push(message.into());
    }
}

/// Build the default SAT/PB replacement evidence packet.
#[must_use]
pub fn default_sat_pb_replacement_evidence() -> SatPbReplacementEvidence {
    build_sat_pb_replacement_evidence(SatPbEvidenceConfig::default())
}

/// Build bounded SAT/PB replacement evidence.
#[must_use]
pub fn build_sat_pb_replacement_evidence(config: SatPbEvidenceConfig) -> SatPbReplacementEvidence {
    let checks = vec![
        check_literal_semantics(config),
        check_clause_and_cnf_semantics(config),
        check_cardinality_semantics(config),
        check_pseudo_boolean_semantics(config),
        check_fail_closed_inputs(),
    ];
    let passed_count = checks.iter().filter(|check| check.passed).count();
    let semantic_cases = checks.iter().map(|check| check.semantic_cases).sum();
    let invalid_input_cases = checks.iter().map(|check| check.invalid_input_cases).sum();
    let total_assignments_enumerated = (0..=config.max_vars).map(assignment_count).sum();
    let evidence_digest = evidence_digest(&checks);

    SatPbReplacementEvidence {
        schema_version: SAT_PB_REPLACEMENT_EVIDENCE_SCHEMA,
        generated_by: "clean_verify::sat_verify::replacement_evidence",
        status: if passed_count == checks.len() {
            "bounded_rust_evidence_passed"
        } else {
            "bounded_rust_evidence_failed"
        },
        claim: "clean has Rust-owned bounded evidence for deterministic SAT/PB domain semantics used by certificate-library replacement work.",
        non_claims: vec![
            "This evidence is bounded and does not claim complete SAT solver replacement.",
            "This evidence does not claim full VeriPB proof replay coverage.",
            "This evidence does not make the Lean4 replacement scorecard green by itself.",
        ],
        checker: config,
        summary: SatPbEvidenceSummary {
            check_count: checks.len(),
            passed_count,
            semantic_cases,
            total_assignments_enumerated,
            invalid_input_cases,
            evidence_digest,
        },
        checks,
        blockers: vec![
            "Integrate this Rust evidence into the public replacement CLI scorecard surface.",
            "Extend from bounded domain semantics to end-to-end PB certificate replay evidence.",
            "Keep launch readiness gated on the broader Lean4 replacement scorecard.",
        ],
    }
}

fn check_literal_semantics(config: SatPbEvidenceConfig) -> SatPbEvidenceCheck {
    let mut check = SatPbEvidenceCheck::new(
        "literal-total-truth-table",
        "eval_lit agrees with the DIMACS polarity truth table for all bounded total assignments",
    );

    for vars in 0..=config.max_vars {
        for bits in 0..assignment_count(vars) {
            let assignment = total_assignment(vars, bits);
            for var in 1..=vars {
                for raw_lit in [var as i32, -(var as i32)] {
                    let lit = Lit::new(raw_lit).expect("nonzero literal");
                    let expected = reference_lit(bits, lit);
                    let actual = eval_lit(&assignment, lit);
                    check.semantic_cases += 1;
                    if actual != Some(expected) {
                        check.fail(format!(
                            "vars={vars} bits={bits:b} lit={raw_lit}: expected {expected:?}, got {actual:?}",
                        ));
                    }
                }
            }
        }
    }

    check
}

fn check_clause_and_cnf_semantics(config: SatPbEvidenceConfig) -> SatPbEvidenceCheck {
    let mut check = SatPbEvidenceCheck::new(
        "clause-cnf-total-truth-table",
        "clause and CNF evaluators agree with reference disjunction/conjunction semantics",
    );
    let clauses = [
        vec![],
        vec![1],
        vec![-1],
        vec![1, -1],
        vec![1, 2],
        vec![-1, 2, -3],
    ];
    let cnfs = [
        vec![],
        vec![vec![]],
        vec![vec![1], vec![-1]],
        vec![vec![1, 2], vec![-2, 3]],
        vec![vec![1, -1], vec![-2]],
    ];

    for vars in 0..=config.max_vars {
        for bits in 0..assignment_count(vars) {
            let assignment = total_assignment(vars, bits);
            for raw_clause in clauses.iter().filter(|clause| max_var(clause) <= vars) {
                let clause = clause_from_dimacs(raw_clause).expect("valid clause");
                let expected = reference_clause(bits, raw_clause);
                let actual = eval_clause_detail(&assignment, &clause).value;
                check.semantic_cases += 1;
                if actual != Some(expected) {
                    check.fail(format!(
                        "vars={vars} bits={bits:b} clause={raw_clause:?}: expected {expected:?}, got {actual:?}",
                    ));
                }
            }

            for raw_cnf in cnfs
                .iter()
                .filter(|cnf| cnf.iter().all(|clause| max_var(clause) <= vars))
            {
                let cnf = cnf_from_dimacs_clauses(vars, raw_cnf).expect("valid cnf");
                let expected = raw_cnf
                    .iter()
                    .all(|raw_clause| reference_clause(bits, raw_clause));
                let actual = eval_cnf_detail(&assignment, &cnf).value;
                check.semantic_cases += 1;
                if actual != Some(expected) {
                    check.fail(format!(
                        "vars={vars} bits={bits:b} cnf={raw_cnf:?}: expected {expected:?}, got {actual:?}",
                    ));
                }
            }
        }
    }

    check
}

fn check_cardinality_semantics(config: SatPbEvidenceConfig) -> SatPbEvidenceCheck {
    let mut check = SatPbEvidenceCheck::new(
        "cardinality-total-truth-table",
        "cardinality AtLeast/AtMost/Exactly evaluators agree with bounded reference counts",
    );
    let constraints: [(Vec<i32>, usize, CardinalityKind); 4] = [
        (vec![], 0, CardinalityKind::Exactly),
        (vec![1, 2, 3], 2, CardinalityKind::AtLeast),
        (vec![1, -2, 3], 1, CardinalityKind::AtMost),
        (vec![1, -2, -3], 2, CardinalityKind::Exactly),
    ];

    for vars in 0..=config.max_vars {
        for bits in 0..assignment_count(vars) {
            let assignment = total_assignment(vars, bits);
            for (lits, bound, kind) in constraints
                .iter()
                .filter(|(lits, _, _)| max_var(lits) <= vars)
            {
                let constraint =
                    CardinalityConstraint::new(lits, *bound, *kind).expect("valid cardinality");
                let true_count = lits
                    .iter()
                    .filter(|&&raw_lit| reference_lit(bits, Lit::new(raw_lit).unwrap()))
                    .count();
                let expected = match kind {
                    CardinalityKind::AtLeast => true_count >= *bound,
                    CardinalityKind::AtMost => true_count <= *bound,
                    CardinalityKind::Exactly => true_count == *bound,
                };
                let actual = eval_cardinality(&assignment, &constraint).value;
                check.semantic_cases += 1;
                if actual != Some(expected) {
                    check.fail(format!(
                        "vars={vars} bits={bits:b} cardinality=({lits:?}, {bound}, {kind:?}): expected {expected:?}, got {actual:?}",
                    ));
                }
            }
        }
    }

    let mut partial = Assignment::new(2);
    partial.set(Var(1), true);
    let open =
        CardinalityConstraint::new(&[1, 2], 2, CardinalityKind::Exactly).expect("valid partial");
    check.semantic_cases += 1;
    if eval_cardinality(&partial, &open).value.is_some() {
        check.fail("partial exact cardinality should remain open");
    }

    check
}

fn check_pseudo_boolean_semantics(config: SatPbEvidenceConfig) -> SatPbEvidenceCheck {
    let mut check = SatPbEvidenceCheck::new(
        "pb-constraint-total-truth-table",
        "PB GE/LE/EQ evaluators agree with bounded weighted-sum reference semantics",
    );
    let constraints: [(Vec<(i64, i32)>, i64, PbComparison); 3] = [
        (vec![(2, 1), (3, -2), (5, 3)], 5, PbComparison::Ge),
        (vec![(2, 1), (-4, 2), (1, -3)], 1, PbComparison::Le),
        (vec![(1, 1), (1, -2), (2, 3)], 3, PbComparison::Eq),
    ];

    for vars in 0..=config.max_vars {
        for bits in 0..assignment_count(vars) {
            let assignment = total_assignment(vars, bits);
            for (terms, rhs, comparison) in constraints
                .iter()
                .filter(|(terms, _, _)| terms.iter().all(|(_, lit)| lit.unsigned_abs() <= vars))
            {
                let constraint =
                    PbConstraint::new(terms, *rhs, *comparison).expect("valid pb constraint");
                let sum = terms
                    .iter()
                    .map(|(coeff, raw_lit)| {
                        let lit = Lit::new(*raw_lit).expect("nonzero literal");
                        if reference_lit(bits, lit) {
                            *coeff
                        } else {
                            0
                        }
                    })
                    .sum::<i64>();
                let expected = match comparison {
                    PbComparison::Ge => sum >= *rhs,
                    PbComparison::Le => sum <= *rhs,
                    PbComparison::Eq => sum == *rhs,
                };
                let actual = eval_pb_constraint(&assignment, &constraint).value;
                check.semantic_cases += 1;
                if actual != Some(expected) {
                    check.fail(format!(
                        "vars={vars} bits={bits:b} pb=({terms:?}, {comparison:?}, {rhs}): expected {expected:?}, got {actual:?}",
                    ));
                }
            }
        }
    }

    let mut partial = Assignment::new(2);
    partial.set(Var(1), true);
    let open = PbConstraint::new(&[(1, 1), (1, 2)], 2, PbComparison::Ge).expect("valid partial");
    check.semantic_cases += 1;
    if eval_pb_constraint(&partial, &open).value.is_some() {
        check.fail("partial PB constraint should remain open");
    }

    check
}

fn check_fail_closed_inputs() -> SatPbEvidenceCheck {
    let mut check = SatPbEvidenceCheck::new(
        "fail-closed-invalid-inputs",
        "raw DIMACS/PB builders reject zero literals and out-of-range CNF variables",
    );
    let invalid_cases = [
        clause_from_dimacs(&[1, 0, -2]) == Err(CnfError::ZeroLiteral),
        cnf_from_dimacs_clauses(2, &[vec![1], vec![-3]])
            .is_err_and(|err| err == CnfError::VariableOutOfRange { var: 3, max: 2 }),
        CardinalityConstraint::new(&[1, 0], 1, CardinalityKind::AtLeast)
            == Err(CnfError::ZeroLiteral),
        PbConstraint::new(&[(1, 1), (2, 0)], 1, PbComparison::Ge) == Err(CnfError::ZeroLiteral),
    ];
    for (idx, passed) in invalid_cases.into_iter().enumerate() {
        check.invalid_input_cases += 1;
        if !passed {
            check.fail(format!("invalid input case {idx} did not fail closed"));
        }
    }
    check
}

fn assignment_count(vars: u32) -> usize {
    1usize << vars
}

fn total_assignment(vars: u32, bits: usize) -> Assignment {
    let mut assignment = Assignment::new(vars);
    for var in 1..=vars {
        assignment.set(Var(var), (bits & bit(var)) != 0);
    }
    assignment
}

fn bit(var: u32) -> usize {
    1usize << (var - 1)
}

fn reference_lit(bits: usize, lit: Lit) -> bool {
    let value = (bits & bit(lit.var().index())) != 0;
    if lit.polarity() {
        value
    } else {
        !value
    }
}

fn reference_clause(bits: usize, clause: &[i32]) -> bool {
    clause
        .iter()
        .any(|&raw_lit| reference_lit(bits, Lit::new(raw_lit).expect("nonzero literal")))
}

fn max_var(lits: &[i32]) -> u32 {
    lits.iter().map(|lit| lit.unsigned_abs()).max().unwrap_or(0)
}

fn evidence_digest(checks: &[SatPbEvidenceCheck]) -> String {
    let mut bytes = Vec::new();
    for check in checks {
        bytes.extend_from_slice(check.id.as_bytes());
        bytes.push(if check.passed { b'1' } else { b'0' });
        bytes.extend_from_slice(check.semantic_cases.to_string().as_bytes());
        bytes.push(b':');
        bytes.extend_from_slice(check.invalid_input_cases.to_string().as_bytes());
        bytes.push(b'\n');
    }
    blake3::hash(&bytes).to_hex().to_string()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn default_evidence_passes_and_is_json_ready() {
        let evidence = default_sat_pb_replacement_evidence();

        assert!(evidence.accepted());
        assert_eq!(evidence.schema_version, SAT_PB_REPLACEMENT_EVIDENCE_SCHEMA);
        assert_eq!(evidence.summary.check_count, 5);
        assert_eq!(evidence.summary.passed_count, 5);
        assert!(evidence.summary.semantic_cases > 100);
        assert_eq!(evidence.summary.invalid_input_cases, 4);
        assert_eq!(evidence.checker.max_vars, DEFAULT_MAX_VARS);

        let json = serde_json::to_string_pretty(&evidence).expect("serialize evidence");
        assert!(json.contains("\"schema_version\""));
        assert!(json.contains("literal-total-truth-table"));
        assert!(json.contains("fail-closed-invalid-inputs"));
        assert!(json.contains("does not claim full VeriPB proof replay coverage"));
    }

    #[test]
    fn bounded_checker_counts_are_deterministic() {
        let evidence = build_sat_pb_replacement_evidence(SatPbEvidenceConfig { max_vars: 3 });

        assert!(evidence.accepted());
        assert_eq!(evidence.summary.total_assignments_enumerated, 15);
        assert_eq!(
            evidence.summary.evidence_digest,
            "1b5a6376dac351fc375adb7346539763de6a2770bd9709d9425e65e8500a9400"
        );
    }

    #[test]
    fn every_check_reports_no_failures_when_passed() {
        let evidence = default_sat_pb_replacement_evidence();

        for check in evidence.checks {
            assert!(check.passed, "{} should pass", check.id);
            assert!(
                check.failures.is_empty(),
                "{} should not carry stale failure diagnostics",
                check.id
            );
        }
    }
}
