// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Kernel-level proof certificates for CDCL invariants S01-S06.
//!
//! These certificates turn the runtime invariant checks into structured,
//! serializable artifacts that can be consumed by the proof promotion pipeline.

// 2026-07-31: the `pub(crate)` items in this module are exercised only by its
// own `#[cfg(test)]` tests, so only the non-test `lib` build sees them as dead.
// Scoped to `not(test)` on purpose: the `lib test` build still enforces
// `dead_code` in full, so an item with no caller anywhere still fails the gate.
#![cfg_attr(not(test), allow(dead_code))]

use super::{termination, var_of, CdclError, CdclState, Literal};
use serde::Serialize;
use serde_json::{json, Value};
use thiserror::Error;

#[derive(Debug, Error)]
pub(crate) enum CdclKernelProofError {
    #[error("failed to serialize CDCL kernel proof data")]
    Serialize(#[from] serde_json::Error),
}

#[derive(Debug, Clone, PartialEq, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub(crate) enum CertificateEvidence {
    TrailConsistency {
        num_vars: u32,
        trail_len: usize,
        all_unique: bool,
    },
    TwoWatchedLiteral {
        num_clauses: usize,
        all_valid: bool,
    },
    LearnedClauseSoundness {
        clause: Vec<i32>,
        all_vars_present: bool,
    },
    BacktrackCorrectness {
        decision_level: u32,
        trail_consistent: bool,
        trail_lim_matches: bool,
    },
    PropagationCompleteness {
        num_clauses: usize,
        no_unpropagated_units: bool,
    },
    Termination {
        num_clauses: usize,
        no_duplicates: bool,
    },
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub(crate) struct CdclProofCertificate {
    pub(crate) theorem_id: &'static str,
    pub(crate) theorem_name: &'static str,
    pub(crate) verified: bool,
    pub(crate) evidence: CertificateEvidence,
    pub(crate) witness_data: Value,
}

impl CdclProofCertificate {
    #[must_use]
    fn new(
        theorem_id: &'static str,
        theorem_name: &'static str,
        verified: bool,
        evidence: CertificateEvidence,
        witness_data: Value,
    ) -> Self {
        Self {
            theorem_id,
            theorem_name,
            verified,
            evidence,
            witness_data,
        }
    }

    pub(crate) fn to_json(&self) -> Result<String, CdclKernelProofError> {
        serde_json::to_string(self).map_err(CdclKernelProofError::from)
    }
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub(crate) struct CdclKernelProofs {
    pub(crate) s01: CdclProofCertificate,
    pub(crate) s02: CdclProofCertificate,
    pub(crate) s03: CdclProofCertificate,
    pub(crate) s04: CdclProofCertificate,
    pub(crate) s05: CdclProofCertificate,
    pub(crate) s06: CdclProofCertificate,
}

impl CdclKernelProofs {
    #[must_use]
    pub(crate) fn from_state(state: &CdclState) -> Self {
        Self {
            s01: verify_s01_trail_consistency(state),
            s02: verify_s02_two_watched_literal(state),
            s03: verify_s03_learned_clause_soundness(state),
            s04: verify_s04_backtrack_correctness(state),
            s05: verify_s05_propagation_completeness(state),
            s06: verify_s06_termination(state),
        }
    }

    #[must_use]
    pub(crate) fn as_vec(&self) -> Vec<CdclProofCertificate> {
        vec![
            self.s01.clone(),
            self.s02.clone(),
            self.s03.clone(),
            self.s04.clone(),
            self.s05.clone(),
            self.s06.clone(),
        ]
    }

    #[must_use]
    pub(crate) fn verify_all(state: &CdclState) -> Vec<CdclProofCertificate> {
        Self::from_state(state).as_vec()
    }

    pub(crate) fn to_json(&self) -> Result<String, CdclKernelProofError> {
        serde_json::to_string(self).map_err(CdclKernelProofError::from)
    }
}

#[must_use]
pub(crate) fn verify_all(state: &CdclState) -> Vec<CdclProofCertificate> {
    CdclKernelProofs::verify_all(state)
}

#[must_use]
pub(crate) fn verify_s01_trail_consistency(state: &CdclState) -> CdclProofCertificate {
    let trail_literals: Vec<Literal> = state.trail.iter().map(|entry| entry.literal).collect();
    let trail_variables: Vec<u32> = trail_literals.iter().map(|&lit| var_of(lit)).collect();
    let check_result = run_s01_trail_consistency_check(state);
    let duplicate_variable = find_duplicate_variable(&trail_variables, state.num_vars);
    let invalid_variable = trail_variables
        .iter()
        .copied()
        .find(|&var| var == 0 || var > state.num_vars);
    let all_unique = check_result.is_ok();

    CdclProofCertificate::new(
        "S01",
        "trail_consistency",
        all_unique,
        CertificateEvidence::TrailConsistency {
            num_vars: state.num_vars,
            trail_len: state.trail.len(),
            all_unique,
        },
        json!({
            "trail_literals": trail_literals,
            "trail_variables": trail_variables,
            "duplicate_variable": duplicate_variable,
            "invalid_variable": invalid_variable,
            "check_error": check_result.err().map(|err| err.to_string()),
        }),
    )
}

#[must_use]
pub(crate) fn verify_s02_two_watched_literal(state: &CdclState) -> CdclProofCertificate {
    let mut invalid_clause = None;
    let mut clause_checks = Vec::with_capacity(state.clauses.len());

    for (clause_idx, clause) in state.clauses.iter().enumerate() {
        let watch_entry = state.watches.get(clause_idx).copied();
        let valid = clause.len() < 2
            || matches!(
                watch_entry,
                Some((watch0, watch1))
                    if watch0 != watch1 && watch0 < clause.len() && watch1 < clause.len()
            );
        if !valid && invalid_clause.is_none() {
            invalid_clause = Some(clause_idx);
        }
        clause_checks.push(json!({
            "clause_idx": clause_idx,
            "clause_len": clause.len(),
            "clause": clause,
            "watch0": watch_entry.map(|(watch0, _)| watch0),
            "watch1": watch_entry.map(|(_, watch1)| watch1),
            "valid": valid,
        }));
    }

    let all_valid = run_s02_two_watched_check(state).is_ok();
    CdclProofCertificate::new(
        "S02",
        "two_watched_literal",
        all_valid,
        CertificateEvidence::TwoWatchedLiteral {
            num_clauses: state.clauses.len(),
            all_valid,
        },
        json!({
            "watch_count": state.watches.len(),
            "invalid_clause": invalid_clause,
            "clause_checks": clause_checks,
        }),
    )
}

#[must_use]
pub(crate) fn verify_s03_learned_clause_soundness(state: &CdclState) -> CdclProofCertificate {
    let candidate_clause = latest_clause_candidate(state).unwrap_or_default();
    let support_clauses = supporting_clauses_for_latest(state);
    let runtime_check = if candidate_clause.is_empty() {
        Ok(())
    } else {
        state.verify_learned_clause(&candidate_clause)
    };
    let all_vars_present = candidate_clause.iter().all(|&lit| {
        support_clauses.iter().any(|clause| {
            clause
                .iter()
                .any(|&existing| var_of(existing) == var_of(lit))
        })
    });
    let verified = runtime_check.is_ok() && all_vars_present;
    let candidate_vars: Vec<u32> = candidate_clause.iter().map(|&lit| var_of(lit)).collect();
    let missing_variables: Vec<u32> = candidate_vars
        .iter()
        .copied()
        .filter(|&var| {
            !support_clauses
                .iter()
                .any(|clause| clause.iter().any(|&existing| var_of(existing) == var))
        })
        .collect();

    CdclProofCertificate::new(
        "S03",
        "learned_clause_soundness",
        verified,
        CertificateEvidence::LearnedClauseSoundness {
            clause: candidate_clause.clone(),
            all_vars_present,
        },
        json!({
            "candidate_clause": candidate_clause,
            "candidate_clause_vars": candidate_vars,
            "support_clause_count": support_clauses.len(),
            "support_clauses": support_clauses,
            "missing_variables": missing_variables,
            "runtime_check_error": runtime_check.err().map(|err| err.to_string()),
            "assumption": "latest clause is treated as the learned clause candidate",
        }),
    )
}

#[must_use]
pub(crate) fn verify_s04_backtrack_correctness(state: &CdclState) -> CdclProofCertificate {
    let trail_consistent = state
        .trail
        .iter()
        .all(|entry| entry.decision_level <= state.decision_level);
    let trail_lim_matches = state.trail_lim.len() as u32 == state.decision_level;
    let verified = run_s04_backtrack_correctness_check(state).is_ok();
    let trail_levels: Vec<u32> = state
        .trail
        .iter()
        .map(|entry| entry.decision_level)
        .collect();

    CdclProofCertificate::new(
        "S04",
        "backtrack_correctness",
        verified,
        CertificateEvidence::BacktrackCorrectness {
            decision_level: state.decision_level,
            trail_consistent,
            trail_lim_matches,
        },
        json!({
            "trail_levels": trail_levels,
            "trail_lim": state.trail_lim.clone(),
            "decision_level": state.decision_level,
            "trail_len": state.trail.len(),
            "check_error": run_s04_backtrack_correctness_check(state)
                .err()
                .map(|err| err.to_string()),
        }),
    )
}

#[must_use]
pub(crate) fn verify_s05_propagation_completeness(state: &CdclState) -> CdclProofCertificate {
    let mut unit_clauses = Vec::new();
    let mut clause_checks = Vec::with_capacity(state.clauses.len());

    for (clause_idx, clause) in state.clauses.iter().enumerate() {
        let mut unassigned = Vec::new();
        let mut satisfied = false;
        for &lit in clause {
            match state.eval_literal(lit) {
                Some(true) => {
                    satisfied = true;
                    break;
                }
                Some(false) => {}
                None => unassigned.push(lit),
            }
        }
        let is_unpropagated_unit = !satisfied && unassigned.len() == 1;
        if is_unpropagated_unit {
            unit_clauses.push(clause_idx);
        }
        clause_checks.push(json!({
            "clause_idx": clause_idx,
            "clause": clause,
            "satisfied": satisfied,
            "unassigned_literals": unassigned,
            "is_unpropagated_unit": is_unpropagated_unit,
        }));
    }

    let no_unpropagated_units = run_s05_propagation_completeness_check(state).is_ok();
    CdclProofCertificate::new(
        "S05",
        "propagation_completeness",
        no_unpropagated_units,
        CertificateEvidence::PropagationCompleteness {
            num_clauses: state.clauses.len(),
            no_unpropagated_units,
        },
        json!({
            "unpropagated_unit_clause_indices": unit_clauses,
            "clause_checks": clause_checks,
        }),
    )
}

#[must_use]
pub(crate) fn verify_s06_termination(state: &CdclState) -> CdclProofCertificate {
    let normalized_clauses: Vec<Vec<Literal>> = state
        .clauses
        .iter()
        .map(|clause| normalize_clause(clause))
        .collect();
    let mut duplicate_pairs = Vec::new();

    for left in 0..normalized_clauses.len() {
        for right in (left + 1)..normalized_clauses.len() {
            if normalized_clauses[left] == normalized_clauses[right] {
                duplicate_pairs.push(json!({
                    "left": left,
                    "right": right,
                    "normalized_clause": normalized_clauses[left],
                }));
            }
        }
    }

    let no_duplicates = run_s06_termination_check(state).is_ok();
    CdclProofCertificate::new(
        "S06",
        "termination",
        no_duplicates,
        CertificateEvidence::Termination {
            num_clauses: state.clauses.len(),
            no_duplicates,
        },
        json!({
            "normalized_clauses": normalized_clauses,
            "duplicate_pairs": duplicate_pairs,
            "num_vars": state.num_vars,
        }),
    )
}

fn run_s01_trail_consistency_check(state: &CdclState) -> Result<(), CdclError> {
    let mut seen = vec![false; (state.num_vars + 1) as usize];
    for entry in &state.trail {
        let var = var_of(entry.literal);
        if var == 0 || var > state.num_vars {
            return Err(CdclError::InvalidVariable(var));
        }
        let index = var as usize;
        if seen[index] {
            return Err(CdclError::TrailInconsistency(var));
        }
        seen[index] = true;
    }
    Ok(())
}

fn run_s02_two_watched_check(state: &CdclState) -> Result<(), CdclError> {
    for (clause_idx, clause) in state.clauses.iter().enumerate() {
        if clause.len() < 2 {
            continue;
        }
        let Some((watch0, watch1)) = state.watches.get(clause_idx).copied() else {
            return Err(CdclError::WatchInvariantViolation(clause_idx));
        };
        if watch0 == watch1 || watch0 >= clause.len() || watch1 >= clause.len() {
            return Err(CdclError::WatchInvariantViolation(clause_idx));
        }
    }
    Ok(())
}

fn run_s04_backtrack_correctness_check(state: &CdclState) -> Result<(), CdclError> {
    for entry in &state.trail {
        if entry.decision_level > state.decision_level {
            return Err(CdclError::BacktrackInconsistency {
                entry_level: entry.decision_level,
                current_level: state.decision_level,
            });
        }
    }
    if state.trail_lim.len() as u32 != state.decision_level {
        return Err(CdclError::TrailLimMismatch {
            expected: state.decision_level,
            actual: state.trail_lim.len() as u32,
        });
    }
    Ok(())
}

fn run_s05_propagation_completeness_check(state: &CdclState) -> Result<(), CdclError> {
    for (clause_idx, clause) in state.clauses.iter().enumerate() {
        let mut unassigned_count = 0usize;
        let mut satisfied = false;
        for &lit in clause {
            match state.eval_literal(lit) {
                Some(true) => {
                    satisfied = true;
                    break;
                }
                Some(false) => {}
                None => unassigned_count += 1,
            }
        }
        if !satisfied && unassigned_count == 1 {
            return Err(CdclError::WatchInvariantViolation(clause_idx));
        }
    }
    Ok(())
}

fn run_s06_termination_check(state: &CdclState) -> Result<(), CdclError> {
    termination::verify_clause_uniqueness(&state.clauses)
}

fn find_duplicate_variable(trail_variables: &[u32], num_vars: u32) -> Option<u32> {
    let mut seen = vec![false; (num_vars + 1) as usize];
    for &var in trail_variables {
        if var == 0 || var > num_vars {
            return Some(var);
        }
        let index = var as usize;
        if seen[index] {
            return Some(var);
        }
        seen[index] = true;
    }
    None
}

fn latest_clause_candidate(state: &CdclState) -> Option<Vec<Literal>> {
    state.clauses.last().cloned()
}

fn supporting_clauses_for_latest(state: &CdclState) -> Vec<Vec<Literal>> {
    if state.clauses.len() <= 1 {
        state.clauses.clone()
    } else {
        state.clauses[..state.clauses.len() - 1].to_vec()
    }
}

fn normalize_clause(clause: &[Literal]) -> Vec<Literal> {
    let mut normalized = clause.to_vec();
    normalized.sort_unstable();
    normalized.dedup();
    normalized
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_verify_s01_trail_consistency_success() {
        let mut state = CdclState::new(3, vec![vec![1, -2], vec![2, 3]]);
        state
            .assign(1, None)
            .expect("first assignment should succeed");
        state
            .assign(-2, None)
            .expect("second assignment should succeed");

        let certificate = verify_s01_trail_consistency(&state);

        assert!(certificate.verified);
        assert_eq!(certificate.theorem_id, "S01");
        assert!(matches!(
            certificate.evidence,
            CertificateEvidence::TrailConsistency {
                num_vars: 3,
                trail_len: 2,
                all_unique: true,
            }
        ));
    }

    #[test]
    fn test_verify_s01_trail_consistency_failure() {
        let mut state = CdclState::new(3, vec![vec![1, -2]]);
        state
            .assign(1, None)
            .expect("first assignment should succeed");
        state.trail.push(super::super::TrailEntry {
            literal: -1,
            decision_level: 0,
            reason: None,
        });

        let certificate = verify_s01_trail_consistency(&state);

        assert!(!certificate.verified);
        assert_eq!(
            certificate.witness_data["duplicate_variable"],
            serde_json::json!(1u32)
        );
    }

    #[test]
    fn test_verify_s02_two_watched_literal_success() {
        let state = CdclState::new(3, vec![vec![1, -2, 3], vec![-1, 2]]);

        let certificate = verify_s02_two_watched_literal(&state);

        assert!(certificate.verified);
        assert!(matches!(
            certificate.evidence,
            CertificateEvidence::TwoWatchedLiteral {
                num_clauses: 2,
                all_valid: true,
            }
        ));
    }

    #[test]
    fn test_verify_s02_two_watched_literal_failure() {
        let mut state = CdclState::new(3, vec![vec![1, 2, 3]]);
        state.watches[0] = (1, 1);

        let certificate = verify_s02_two_watched_literal(&state);

        assert!(!certificate.verified);
        assert_eq!(
            certificate.witness_data["invalid_clause"],
            serde_json::json!(0)
        );
    }

    #[test]
    fn test_verify_s03_learned_clause_soundness_success() {
        let mut state = CdclState::new(3, vec![vec![1, -2], vec![2, 3]]);
        state.add_learned_clause(vec![-1, 3]);

        let certificate = verify_s03_learned_clause_soundness(&state);

        assert!(certificate.verified);
        assert!(matches!(
            certificate.evidence,
            CertificateEvidence::LearnedClauseSoundness {
                clause,
                all_vars_present: true,
            } if clause == vec![-1, 3]
        ));
    }

    #[test]
    fn test_verify_s03_learned_clause_soundness_failure() {
        let mut state = CdclState::new(3, vec![vec![1], vec![2]]);
        state.add_learned_clause(vec![3]);

        let certificate = verify_s03_learned_clause_soundness(&state);

        assert!(!certificate.verified);
        assert_eq!(
            certificate.witness_data["missing_variables"],
            serde_json::json!([3u32])
        );
    }

    #[test]
    fn test_verify_s04_backtrack_correctness_success() {
        let mut state = CdclState::new(3, vec![vec![1, 2]]);
        state.decide(1).expect("first decision should succeed");
        state.decide(2).expect("second decision should succeed");

        let certificate = verify_s04_backtrack_correctness(&state);

        assert!(certificate.verified);
        assert!(matches!(
            certificate.evidence,
            CertificateEvidence::BacktrackCorrectness {
                decision_level: 2,
                trail_consistent: true,
                trail_lim_matches: true,
            }
        ));
    }

    #[test]
    fn test_verify_s04_backtrack_correctness_failure() {
        let mut state = CdclState::new(3, vec![vec![1, 2]]);
        state.decide(1).expect("decision should succeed");
        state.trail_lim.clear();

        let certificate = verify_s04_backtrack_correctness(&state);

        assert!(!certificate.verified);
        assert_eq!(
            certificate.witness_data["check_error"],
            serde_json::json!("S04 violation: trail_lim 0 != 1")
        );
    }

    #[test]
    fn test_verify_s05_propagation_completeness_success() {
        let state = CdclState::new(3, vec![vec![1, 2], vec![-1, 3]]);

        let certificate = verify_s05_propagation_completeness(&state);

        assert!(certificate.verified);
        assert!(matches!(
            certificate.evidence,
            CertificateEvidence::PropagationCompleteness {
                num_clauses: 2,
                no_unpropagated_units: true,
            }
        ));
    }

    #[test]
    fn test_verify_s05_propagation_completeness_failure() {
        let mut state = CdclState::new(2, vec![vec![1, 2]]);
        state.assign(-1, None).expect("assignment should succeed");

        let certificate = verify_s05_propagation_completeness(&state);

        assert!(!certificate.verified);
        assert_eq!(
            certificate.witness_data["unpropagated_unit_clause_indices"],
            serde_json::json!([0])
        );
    }

    #[test]
    fn test_verify_s06_termination_success() {
        let state = CdclState::new(3, vec![vec![1, 2], vec![-1, 3]]);

        let certificate = verify_s06_termination(&state);

        assert!(certificate.verified);
        assert!(matches!(
            certificate.evidence,
            CertificateEvidence::Termination {
                num_clauses: 2,
                no_duplicates: true,
            }
        ));
    }

    #[test]
    fn test_verify_s06_termination_failure() {
        let state = CdclState::new(3, vec![vec![1, 2], vec![2, 1]]);

        let certificate = verify_s06_termination(&state);

        assert!(!certificate.verified);
        assert_eq!(
            certificate.witness_data["duplicate_pairs"],
            serde_json::json!([
                {
                    "left": 0,
                    "right": 1,
                    "normalized_clause": [1, 2]
                }
            ])
        );
    }

    #[test]
    fn test_cdcl_kernel_proofs_verify_all_returns_all_certificates() {
        let mut state = CdclState::new(3, vec![vec![1, -2], vec![2, 3]]);
        state.add_learned_clause(vec![-1, 3]);

        let certificates = verify_all(&state);

        assert_eq!(certificates.len(), 6);
        assert_eq!(
            certificates
                .iter()
                .map(|certificate| certificate.theorem_id)
                .collect::<Vec<_>>(),
            vec!["S01", "S02", "S03", "S04", "S05", "S06"]
        );
    }

    #[test]
    fn test_cdcl_kernel_proofs_struct_holds_each_certificate() {
        let mut state = CdclState::new(3, vec![vec![1, -2], vec![2, 3]]);
        state.add_learned_clause(vec![-1, 3]);

        let proofs = CdclKernelProofs::from_state(&state);

        assert_eq!(proofs.s01.theorem_name, "trail_consistency");
        assert_eq!(proofs.s06.theorem_name, "termination");
        assert_eq!(proofs.as_vec().len(), 6);
    }

    #[test]
    fn test_certificate_json_serialization() {
        let state = CdclState::new(2, vec![vec![1, 2]]);
        let certificate = verify_s02_two_watched_literal(&state);

        let json = certificate
            .to_json()
            .expect("certificate JSON serialization should succeed");
        let parsed: Value =
            serde_json::from_str(&json).expect("serialized certificate should parse");

        assert_eq!(parsed["theorem_id"], serde_json::json!("S02"));
        assert_eq!(
            parsed["theorem_name"],
            serde_json::json!("two_watched_literal")
        );
    }

    #[test]
    fn test_kernel_proofs_json_serialization() {
        let mut state = CdclState::new(3, vec![vec![1, -2], vec![2, 3]]);
        state.add_learned_clause(vec![-1, 3]);
        let proofs = CdclKernelProofs::from_state(&state);

        let json = proofs
            .to_json()
            .expect("proof bundle JSON serialization should succeed");
        let parsed: Value = serde_json::from_str(&json).expect("serialized bundle should parse");

        assert_eq!(parsed["s03"]["theorem_id"], serde_json::json!("S03"));
        assert_eq!(
            parsed["s03"]["evidence"]["kind"],
            serde_json::json!("learned_clause_soundness")
        );
    }
}
