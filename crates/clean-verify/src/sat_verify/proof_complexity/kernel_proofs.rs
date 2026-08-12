// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Kernel-level proof certificates for proof complexity theorems PC01-PC04.
//!
//! These certificates turn resolution and cutting-planes proof checks into
//! structured, serializable artifacts that can be consumed by the proof
//! promotion pipeline.

// 2026-07-31: the `pub(crate)` items in this module are exercised only by its
// own `#[cfg(test)]` tests, so only the non-test `lib` build sees them as dead.
// Scoped to `not(test)` on purpose: the `lib test` build still enforces
// `dead_code` in full, so an item with no caller anywhere still fails the gate.
#![cfg_attr(not(test), allow(dead_code))]

use std::collections::BTreeSet;

use crate::sat_verify::cdcl::{var_of, Clause, Literal};
use crate::sat_verify::proof_complexity::{
    cutting_planes::{CpInequality, CpStep, CuttingPlanesProof},
    resolution::{self, ResolutionProof, ResolutionStep},
};
use serde::Serialize;
use serde_json::{json, Value};
use thiserror::Error;

const MAX_EXHAUSTIVE_VARS: usize = 16;

#[derive(Debug, Error)]
pub(crate) enum PcKernelProofError {
    #[error("failed to serialize PC kernel proof data")]
    Serialize(#[from] serde_json::Error),
}

#[derive(Debug, Clone, PartialEq, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub(crate) enum PcCertificateEvidence {
    ResolutionSoundness {
        proof_steps: usize,
        resolve_steps: usize,
        all_resolve_steps_sound: bool,
        proof_width: usize,
        proof_space: usize,
        proof_depth: usize,
    },
    ResolutionCompleteness {
        num_clauses: usize,
        proof_steps: usize,
        inputs_covered: bool,
        derives_empty_clause: bool,
    },
    CuttingPlanesSoundness {
        proof_steps: usize,
        derived_steps: usize,
        all_rule_applications_sound: bool,
        derives_contradiction: bool,
    },
    CpSubsumesResolution {
        resolution_steps: usize,
        cp_steps: usize,
        simulation_valid: bool,
        derives_cp_contradiction: bool,
    },
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub(crate) struct PcProofCertificate {
    pub(crate) theorem_id: &'static str,
    pub(crate) theorem_name: &'static str,
    pub(crate) verified: bool,
    pub(crate) evidence: PcCertificateEvidence,
    pub(crate) witness_data: Value,
}

impl PcProofCertificate {
    #[must_use]
    fn new(
        theorem_id: &'static str,
        theorem_name: &'static str,
        verified: bool,
        evidence: PcCertificateEvidence,
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

    pub(crate) fn to_json(&self) -> Result<String, PcKernelProofError> {
        serde_json::to_string(self).map_err(PcKernelProofError::from)
    }
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub(crate) struct PcKernelProofs {
    pub(crate) pc01: PcProofCertificate,
    pub(crate) pc02: PcProofCertificate,
    pub(crate) pc03: PcProofCertificate,
    pub(crate) pc04: PcProofCertificate,
}

impl PcKernelProofs {
    #[must_use]
    pub(crate) fn from_proofs(
        clauses: &[Clause],
        resolution_proof: &ResolutionProof,
        cp_proof: &CuttingPlanesProof,
    ) -> Self {
        Self {
            pc01: verify_pc01_resolution_soundness(resolution_proof),
            pc02: verify_pc02_resolution_completeness(clauses, resolution_proof),
            pc03: verify_pc03_cp_soundness(cp_proof),
            pc04: verify_pc04_cp_subsumes_resolution(resolution_proof),
        }
    }

    #[must_use]
    pub(crate) fn as_vec(&self) -> Vec<PcProofCertificate> {
        vec![
            self.pc01.clone(),
            self.pc02.clone(),
            self.pc03.clone(),
            self.pc04.clone(),
        ]
    }

    #[must_use]
    pub(crate) fn verify_all(
        clauses: &[Clause],
        resolution_proof: &ResolutionProof,
        cp_proof: &CuttingPlanesProof,
    ) -> Vec<PcProofCertificate> {
        Self::from_proofs(clauses, resolution_proof, cp_proof).as_vec()
    }

    pub(crate) fn to_json(&self) -> Result<String, PcKernelProofError> {
        serde_json::to_string(self).map_err(PcKernelProofError::from)
    }
}

#[must_use]
pub(crate) fn verify_all(
    clauses: &[Clause],
    resolution_proof: &ResolutionProof,
    cp_proof: &CuttingPlanesProof,
) -> Vec<PcProofCertificate> {
    PcKernelProofs::verify_all(clauses, resolution_proof, cp_proof)
}

#[must_use]
pub(crate) fn verify_pc01_resolution_soundness(proof: &ResolutionProof) -> PcProofCertificate {
    let mut step_checks = Vec::with_capacity(proof.len());
    let mut resolve_steps = 0usize;
    let mut all_resolve_steps_sound = true;

    for (step_idx, step) in proof.steps().iter().enumerate() {
        match step {
            ResolutionStep::Input(clause) => {
                step_checks.push(json!({
                    "step_idx": step_idx,
                    "step_kind": "input",
                    "clause": clause,
                }));
            }
            ResolutionStep::Resolve { left, right, pivot } => {
                resolve_steps += 1;
                let left_clause = proof.clause_at(*left).cloned();
                let right_clause = proof.clause_at(*right).cloned();
                let derived_clause = proof.clause_at(step_idx).cloned();

                let (matches_expected, expected_clause, resolve_error, entailed, counterexample) =
                    match (&left_clause, &right_clause, &derived_clause) {
                        (Some(left_clause), Some(right_clause), Some(derived_clause)) => {
                            match resolution::resolve_clauses(left_clause, right_clause, *pivot) {
                                Ok(expected_clause) => {
                                    let matches_expected = expected_clause == *derived_clause;
                                    let (entailed, counterexample) = if matches_expected {
                                        clause_entailed_by_parents(
                                            left_clause,
                                            right_clause,
                                            derived_clause,
                                        )
                                    } else {
                                        (false, None)
                                    };
                                    (
                                        matches_expected,
                                        Some(expected_clause),
                                        None,
                                        entailed,
                                        counterexample,
                                    )
                                }
                                Err(err) => (false, None, Some(err), false, None),
                            }
                        }
                        _ => (
                            false,
                            None,
                            Some("missing parent or derived clause".to_string()),
                            false,
                            None,
                        ),
                    };

                let step_sound = matches_expected && entailed;
                all_resolve_steps_sound &= step_sound;

                step_checks.push(json!({
                    "step_idx": step_idx,
                    "step_kind": "resolve",
                    "left": left,
                    "right": right,
                    "pivot": pivot,
                    "left_clause": left_clause,
                    "right_clause": right_clause,
                    "derived_clause": derived_clause,
                    "expected_clause": expected_clause,
                    "matches_expected": matches_expected,
                    "entailed_by_parents": entailed,
                    "counterexample": counterexample,
                    "resolve_error": resolve_error,
                }));
            }
        }
    }

    PcProofCertificate::new(
        "PC01",
        "resolution_soundness",
        all_resolve_steps_sound,
        PcCertificateEvidence::ResolutionSoundness {
            proof_steps: proof.len(),
            resolve_steps,
            all_resolve_steps_sound,
            proof_width: proof.proof_width(),
            proof_space: proof.proof_space(),
            proof_depth: proof.proof_depth(),
        },
        json!({
            "proof_is_refutation": proof.verify(),
            "step_checks": step_checks,
        }),
    )
}

#[must_use]
pub(crate) fn verify_pc02_resolution_completeness(
    clauses: &[Clause],
    proof: &ResolutionProof,
) -> PcProofCertificate {
    let soundness_certificate = verify_pc01_resolution_soundness(proof);
    let mut missing_inputs = Vec::new();
    let normalized_formula: Vec<Vec<Literal>> = clauses
        .iter()
        .map(|clause| normalize_clause(clause))
        .collect();

    for step in proof.steps() {
        if let ResolutionStep::Input(clause) = step {
            let normalized_input = normalize_clause(clause);
            if !normalized_formula
                .iter()
                .any(|existing| existing == &normalized_input)
            {
                missing_inputs.push(clause.clone());
            }
        }
    }

    let inputs_covered = missing_inputs.is_empty();
    let derives_empty_clause = proof.verify();
    let verified = soundness_certificate.verified && inputs_covered && derives_empty_clause;
    let final_clause = if proof.is_empty() {
        None
    } else {
        proof.clause_at(proof.len() - 1).cloned()
    };

    PcProofCertificate::new(
        "PC02",
        "resolution_completeness",
        verified,
        PcCertificateEvidence::ResolutionCompleteness {
            num_clauses: clauses.len(),
            proof_steps: proof.len(),
            inputs_covered,
            derives_empty_clause,
        },
        json!({
            "formula_clauses": clauses,
            "normalized_formula_clauses": normalized_formula,
            "missing_inputs": missing_inputs,
            "final_clause": final_clause,
            "soundness_verified": soundness_certificate.verified,
            "assumption": "this certificate checks that the supplied proof is a valid resolution refutation of the supplied CNF",
        }),
    )
}

#[must_use]
pub(crate) fn verify_pc03_cp_soundness(proof: &CuttingPlanesProof) -> PcProofCertificate {
    let mut derived_steps = 0usize;
    let mut all_rule_applications_sound = true;
    let mut step_checks = Vec::with_capacity(proof.len());

    for step_idx in 0..proof.len() {
        let step = proof.step_at(step_idx).cloned();
        let derived = proof.inequality_at(step_idx).cloned();

        let Some(step) = step else {
            all_rule_applications_sound = false;
            step_checks.push(json!({
                "step_idx": step_idx,
                "step_kind": "missing",
                "valid": false,
            }));
            continue;
        };

        match step {
            CpStep::Input(ineq) => {
                step_checks.push(json!({
                    "step_idx": step_idx,
                    "step_kind": "input",
                    "inequality": ineq,
                    "is_trivially_valid": ineq.is_trivially_valid(),
                }));
            }
            CpStep::Add(left, right) => {
                derived_steps += 1;
                let left_ineq = proof.inequality_at(left).cloned();
                let right_ineq = proof.inequality_at(right).cloned();
                let (matches_expected, expected, counterexample) =
                    match (&left_ineq, &right_ineq, &derived) {
                        (Some(left_ineq), Some(right_ineq), Some(derived)) => {
                            let expected = add_inequalities(left_ineq, right_ineq);
                            let matches_expected = expected == *derived;
                            let (semantically_sound, counterexample) = if matches_expected {
                                inequalities_imply(&[left_ineq, right_ineq], derived)
                            } else {
                                (false, None)
                            };
                            (
                                matches_expected && semantically_sound,
                                Some(expected),
                                counterexample,
                            )
                        }
                        _ => (false, None, None),
                    };
                all_rule_applications_sound &= matches_expected;
                step_checks.push(json!({
                    "step_idx": step_idx,
                    "step_kind": "add",
                    "left": left,
                    "right": right,
                    "left_inequality": left_ineq,
                    "right_inequality": right_ineq,
                    "derived_inequality": derived,
                    "expected_inequality": expected,
                    "valid": matches_expected,
                    "counterexample": counterexample,
                }));
            }
            CpStep::Multiply(source, scalar) => {
                derived_steps += 1;
                let source_ineq = proof.inequality_at(source).cloned();
                let (matches_expected, expected, rule_error, counterexample) =
                    match (&source_ineq, &derived) {
                        (Some(source_ineq), Some(derived)) => {
                            match multiply_inequality(source_ineq, scalar) {
                                Ok(expected) => {
                                    let matches_expected = expected == *derived;
                                    let (semantically_sound, counterexample) = if matches_expected {
                                        inequalities_imply(&[source_ineq], derived)
                                    } else {
                                        (false, None)
                                    };
                                    (
                                        matches_expected && semantically_sound,
                                        Some(expected),
                                        None,
                                        counterexample,
                                    )
                                }
                                Err(err) => (false, None, Some(err), None),
                            }
                        }
                        _ => (
                            false,
                            None,
                            Some("missing source or derived inequality".to_string()),
                            None,
                        ),
                    };
                all_rule_applications_sound &= matches_expected;
                step_checks.push(json!({
                    "step_idx": step_idx,
                    "step_kind": "multiply",
                    "source": source,
                    "scalar": scalar,
                    "source_inequality": source_ineq,
                    "derived_inequality": derived,
                    "expected_inequality": expected,
                    "valid": matches_expected,
                    "counterexample": counterexample,
                    "rule_error": rule_error,
                }));
            }
            CpStep::Divide(source, divisor) => {
                derived_steps += 1;
                let source_ineq = proof.inequality_at(source).cloned();
                let (matches_expected, expected, rule_error, counterexample) =
                    match (&source_ineq, &derived) {
                        (Some(source_ineq), Some(derived)) => {
                            match divide_inequality(source_ineq, divisor) {
                                Ok(expected) => {
                                    let matches_expected = expected == *derived;
                                    let (semantically_sound, counterexample) = if matches_expected {
                                        inequalities_imply(&[source_ineq], derived)
                                    } else {
                                        (false, None)
                                    };
                                    (
                                        matches_expected && semantically_sound,
                                        Some(expected),
                                        None,
                                        counterexample,
                                    )
                                }
                                Err(err) => (false, None, Some(err), None),
                            }
                        }
                        _ => (
                            false,
                            None,
                            Some("missing source or derived inequality".to_string()),
                            None,
                        ),
                    };
                all_rule_applications_sound &= matches_expected;
                step_checks.push(json!({
                    "step_idx": step_idx,
                    "step_kind": "divide",
                    "source": source,
                    "divisor": divisor,
                    "source_inequality": source_ineq,
                    "derived_inequality": derived,
                    "expected_inequality": expected,
                    "valid": matches_expected,
                    "counterexample": counterexample,
                    "rule_error": rule_error,
                }));
            }
            CpStep::Saturate(source) => {
                derived_steps += 1;
                let source_ineq = proof.inequality_at(source).cloned();
                let (matches_expected, expected, counterexample) = match (&source_ineq, &derived) {
                    (Some(source_ineq), Some(derived)) => {
                        let expected = saturate_inequality(source_ineq);
                        let matches_expected = expected == *derived;
                        let (semantically_sound, counterexample) = if matches_expected {
                            inequalities_imply(&[source_ineq], derived)
                        } else {
                            (false, None)
                        };
                        (
                            matches_expected && semantically_sound,
                            Some(expected),
                            counterexample,
                        )
                    }
                    _ => (false, None, None),
                };
                all_rule_applications_sound &= matches_expected;
                step_checks.push(json!({
                    "step_idx": step_idx,
                    "step_kind": "saturate",
                    "source": source,
                    "source_inequality": source_ineq,
                    "derived_inequality": derived,
                    "expected_inequality": expected,
                    "valid": matches_expected,
                    "counterexample": counterexample,
                }));
            }
        }
    }

    PcProofCertificate::new(
        "PC03",
        "cutting_planes_soundness",
        all_rule_applications_sound,
        PcCertificateEvidence::CuttingPlanesSoundness {
            proof_steps: proof.len(),
            derived_steps,
            all_rule_applications_sound,
            derives_contradiction: proof.verify(),
        },
        json!({
            "proof_derives_contradiction": proof.verify(),
            "step_checks": step_checks,
            "assumption": "input inequalities are treated as CP axioms; only non-input rule applications are checked",
        }),
    )
}

#[must_use]
pub(crate) fn verify_pc04_cp_subsumes_resolution(proof: &ResolutionProof) -> PcProofCertificate {
    let max_var = max_var_in_resolution_proof(proof);
    let mut cp_proof = CuttingPlanesProof::new();
    let mut resolution_to_cp = Vec::with_capacity(proof.len());
    let mut step_checks = Vec::with_capacity(proof.len());
    let mut simulation_valid = true;

    for (step_idx, step) in proof.steps().iter().enumerate() {
        match step {
            ResolutionStep::Input(clause) => {
                let cp_clause = clause_to_cp_inequality(clause, max_var);
                let cp_idx = cp_proof.add_input(cp_clause.clone());
                resolution_to_cp.push(cp_idx);
                step_checks.push(json!({
                    "step_idx": step_idx,
                    "step_kind": "input",
                    "resolution_clause": clause,
                    "cp_index": cp_idx,
                    "cp_inequality": cp_clause,
                }));
            }
            ResolutionStep::Resolve { left, right, pivot } => {
                let target_clause = proof.clause_at(step_idx).cloned().unwrap_or_default();
                let target_ineq = clause_to_cp_inequality(&target_clause, max_var);
                let left_cp_idx = resolution_to_cp.get(*left).copied();
                let right_cp_idx = resolution_to_cp.get(*right).copied();
                let left_ineq = left_cp_idx.and_then(|idx| cp_proof.inequality_at(idx).cloned());
                let right_ineq = right_cp_idx.and_then(|idx| cp_proof.inequality_at(idx).cloned());

                let Some(left_cp_idx) = left_cp_idx else {
                    simulation_valid = false;
                    resolution_to_cp.push(0);
                    step_checks.push(json!({
                        "step_idx": step_idx,
                        "step_kind": "resolve",
                        "left": left,
                        "right": right,
                        "pivot": pivot,
                        "target_clause": target_clause,
                        "target_inequality": target_ineq,
                        "simulation_steps": Value::Array(Vec::new()),
                        "simulated": false,
                        "reason": "missing left CP parent",
                    }));
                    continue;
                };
                let Some(right_cp_idx) = right_cp_idx else {
                    simulation_valid = false;
                    resolution_to_cp.push(left_cp_idx);
                    step_checks.push(json!({
                        "step_idx": step_idx,
                        "step_kind": "resolve",
                        "left": left,
                        "right": right,
                        "pivot": pivot,
                        "target_clause": target_clause,
                        "target_inequality": target_ineq,
                        "simulation_steps": Value::Array(Vec::new()),
                        "simulated": false,
                        "reason": "missing right CP parent",
                    }));
                    continue;
                };

                let Some(left_ineq) = left_ineq else {
                    simulation_valid = false;
                    resolution_to_cp.push(left_cp_idx);
                    step_checks.push(json!({
                        "step_idx": step_idx,
                        "step_kind": "resolve",
                        "left": left,
                        "right": right,
                        "pivot": pivot,
                        "target_clause": target_clause,
                        "target_inequality": target_ineq,
                        "simulation_steps": Value::Array(Vec::new()),
                        "simulated": false,
                        "reason": "missing left CP inequality",
                    }));
                    continue;
                };
                let Some(right_ineq) = right_ineq else {
                    simulation_valid = false;
                    resolution_to_cp.push(left_cp_idx);
                    step_checks.push(json!({
                        "step_idx": step_idx,
                        "step_kind": "resolve",
                        "left": left,
                        "right": right,
                        "pivot": pivot,
                        "target_clause": target_clause,
                        "target_inequality": target_ineq,
                        "simulation_steps": Value::Array(Vec::new()),
                        "simulated": false,
                        "reason": "missing right CP inequality",
                    }));
                    continue;
                };

                let strategy =
                    choose_resolution_simulation_strategy(&left_ineq, &right_ineq, &target_ineq);

                if let Some(strategy) = strategy {
                    let add_idx = match cp_proof.add(left_cp_idx, right_cp_idx) {
                        Ok(idx) => idx,
                        Err(err) => {
                            simulation_valid = false;
                            resolution_to_cp.push(left_cp_idx);
                            step_checks.push(json!({
                                "step_idx": step_idx,
                                "step_kind": "resolve",
                                "left": left,
                                "right": right,
                                "pivot": pivot,
                                "target_clause": target_clause,
                                "target_inequality": target_ineq,
                                "simulation_steps": Value::Array(Vec::new()),
                                "simulated": false,
                                "reason": err,
                            }));
                            continue;
                        }
                    };

                    let mut simulation_steps = vec![json!({
                        "rule": "add",
                        "cp_index": add_idx,
                        "inequality": cp_proof.inequality_at(add_idx),
                    })];
                    let mut current_idx = add_idx;
                    let mut execution_ok = true;

                    for action in strategy {
                        match action {
                            CpSimulationAction::DivideByTwo => {
                                match cp_proof.divide(current_idx, 2) {
                                    Ok(next_idx) => {
                                        current_idx = next_idx;
                                        simulation_steps.push(json!({
                                            "rule": "divide",
                                            "divisor": 2,
                                            "cp_index": current_idx,
                                            "inequality": cp_proof.inequality_at(current_idx),
                                        }));
                                    }
                                    Err(err) => {
                                        execution_ok = false;
                                        simulation_steps.push(json!({
                                            "rule": "divide",
                                            "divisor": 2,
                                            "error": err,
                                        }));
                                        break;
                                    }
                                }
                            }
                            CpSimulationAction::Saturate => match cp_proof.saturate(current_idx) {
                                Ok(next_idx) => {
                                    current_idx = next_idx;
                                    simulation_steps.push(json!({
                                        "rule": "saturate",
                                        "cp_index": current_idx,
                                        "inequality": cp_proof.inequality_at(current_idx),
                                    }));
                                }
                                Err(err) => {
                                    execution_ok = false;
                                    simulation_steps.push(json!({
                                        "rule": "saturate",
                                        "error": err,
                                    }));
                                    break;
                                }
                            },
                        }
                    }

                    let simulated = execution_ok
                        && cp_proof
                            .inequality_at(current_idx)
                            .is_some_and(|ineq| *ineq == target_ineq);
                    simulation_valid &= simulated;
                    resolution_to_cp.push(current_idx);

                    step_checks.push(json!({
                        "step_idx": step_idx,
                        "step_kind": "resolve",
                        "left": left,
                        "right": right,
                        "pivot": pivot,
                        "target_clause": target_clause,
                        "target_inequality": target_ineq,
                        "simulation_steps": simulation_steps,
                        "simulated": simulated,
                    }));
                } else {
                    simulation_valid = false;
                    resolution_to_cp.push(left_cp_idx);
                    step_checks.push(json!({
                        "step_idx": step_idx,
                        "step_kind": "resolve",
                        "left": left,
                        "right": right,
                        "pivot": pivot,
                        "target_clause": target_clause,
                        "target_inequality": target_ineq,
                        "simulation_steps": [
                            {
                                "rule": "add",
                                "expected_result": add_inequalities(&left_ineq, &right_ineq),
                            }
                        ],
                        "simulated": false,
                        "reason": "no add/divide/saturate sequence produced the target clause encoding",
                    }));
                }
            }
        }
    }

    let derives_cp_contradiction = if proof.verify() {
        cp_proof.verify()
    } else {
        false
    };

    PcProofCertificate::new(
        "PC04",
        "cp_subsumes_resolution",
        simulation_valid && (!proof.verify() || derives_cp_contradiction),
        PcCertificateEvidence::CpSubsumesResolution {
            resolution_steps: proof.len(),
            cp_steps: cp_proof.len(),
            simulation_valid,
            derives_cp_contradiction,
        },
        json!({
            "resolution_is_refutation": proof.verify(),
            "cp_is_refutation": cp_proof.verify(),
            "step_checks": step_checks,
        }),
    )
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum CpSimulationAction {
    DivideByTwo,
    Saturate,
}

fn choose_resolution_simulation_strategy(
    left: &CpInequality,
    right: &CpInequality,
    target: &CpInequality,
) -> Option<Vec<CpSimulationAction>> {
    let added = add_inequalities(left, right);
    if added == *target {
        return Some(Vec::new());
    }

    let divided = divide_inequality(&added, 2).ok();
    if divided.as_ref().is_some_and(|ineq| *ineq == *target) {
        return Some(vec![CpSimulationAction::DivideByTwo]);
    }

    let saturated = saturate_inequality(&added);
    if saturated == *target {
        return Some(vec![CpSimulationAction::Saturate]);
    }

    if let Some(divided) = divided {
        let divided_then_saturated = saturate_inequality(&divided);
        if divided_then_saturated == *target {
            return Some(vec![
                CpSimulationAction::DivideByTwo,
                CpSimulationAction::Saturate,
            ]);
        }
    }

    let saturated_then_divided = divide_inequality(&saturated, 2).ok();
    if saturated_then_divided
        .as_ref()
        .is_some_and(|ineq| *ineq == *target)
    {
        return Some(vec![
            CpSimulationAction::Saturate,
            CpSimulationAction::DivideByTwo,
        ]);
    }

    None
}

fn clause_entailed_by_parents(
    left: &[Literal],
    right: &[Literal],
    resolvent: &[Literal],
) -> (bool, Option<Value>) {
    let vars = collect_clause_vars(&[left, right, resolvent]);
    if vars.len() > MAX_EXHAUSTIVE_VARS {
        return (true, None);
    }

    let total = 1u64 << vars.len();
    for mask in 0..total {
        let assignment = assignment_from_mask(&vars, mask);
        let left_holds = clause_holds(left, &assignment);
        let right_holds = clause_holds(right, &assignment);
        if left_holds && right_holds && !clause_holds(resolvent, &assignment) {
            return (false, Some(json!(assignment_pairs(&vars, mask))));
        }
    }
    (true, None)
}

fn inequalities_imply(
    premises: &[&CpInequality],
    conclusion: &CpInequality,
) -> (bool, Option<Value>) {
    let vars = collect_inequality_vars(premises, conclusion);
    if vars.len() > MAX_EXHAUSTIVE_VARS {
        return (true, None);
    }

    let total = 1u64 << vars.len();
    for mask in 0..total {
        let assignment = assignment_from_mask(&vars, mask);
        let premises_hold = premises.iter().all(|ineq| ineq.evaluate(&assignment));
        if premises_hold && !conclusion.evaluate(&assignment) {
            return (false, Some(json!(assignment_pairs(&vars, mask))));
        }
    }
    (true, None)
}

fn clause_holds(clause: &[Literal], assignment: &[bool]) -> bool {
    clause.iter().any(|&lit| {
        let var = var_of(lit) as usize;
        let value = assignment
            .get(var.saturating_sub(1))
            .copied()
            .unwrap_or(false);
        if lit > 0 {
            value
        } else {
            !value
        }
    })
}

fn collect_clause_vars(clauses: &[&[Literal]]) -> Vec<u32> {
    let mut vars = BTreeSet::new();
    for clause in clauses {
        for &lit in *clause {
            vars.insert(var_of(lit));
        }
    }
    vars.into_iter().collect()
}

fn collect_inequality_vars(premises: &[&CpInequality], conclusion: &CpInequality) -> Vec<u32> {
    let mut vars = BTreeSet::new();
    for ineq in premises.iter().copied().chain(std::iter::once(conclusion)) {
        for (idx, &coeff) in ineq.coeffs.iter().enumerate() {
            if coeff != 0 {
                vars.insert((idx + 1) as u32);
            }
        }
    }
    vars.into_iter().collect()
}

fn assignment_from_mask(vars: &[u32], mask: u64) -> Vec<bool> {
    let max_var = vars.iter().copied().max().unwrap_or(0) as usize;
    let mut assignment = vec![false; max_var];
    for (pos, &var) in vars.iter().enumerate() {
        assignment[(var - 1) as usize] = ((mask >> pos) & 1) == 1;
    }
    assignment
}

fn assignment_pairs(vars: &[u32], mask: u64) -> Vec<Value> {
    vars.iter()
        .enumerate()
        .map(|(pos, &var)| {
            json!({
                "var": var,
                "value": ((mask >> pos) & 1) == 1,
            })
        })
        .collect()
}

fn add_inequalities(left: &CpInequality, right: &CpInequality) -> CpInequality {
    let n = left.coeffs.len().max(right.coeffs.len());
    let mut coeffs = vec![0i64; n];
    for (idx, coeff) in coeffs.iter_mut().enumerate() {
        *coeff = left.coeffs.get(idx).copied().unwrap_or(0)
            + right.coeffs.get(idx).copied().unwrap_or(0);
    }
    CpInequality::new(coeffs, left.rhs + right.rhs)
}

fn multiply_inequality(base: &CpInequality, scalar: i64) -> Result<CpInequality, String> {
    if scalar <= 0 {
        return Err(format!("scalar must be positive, got {scalar}"));
    }
    Ok(CpInequality::new(
        base.coeffs.iter().map(|&coeff| coeff * scalar).collect(),
        base.rhs * scalar,
    ))
}

fn divide_inequality(base: &CpInequality, divisor: i64) -> Result<CpInequality, String> {
    if divisor <= 0 {
        return Err(format!("divisor must be positive, got {divisor}"));
    }
    Ok(CpInequality::new(
        base.coeffs
            .iter()
            .map(|&coeff| div_ceil(coeff, divisor))
            .collect(),
        div_ceil(base.rhs, divisor),
    ))
}

fn saturate_inequality(base: &CpInequality) -> CpInequality {
    let rhs = base.rhs;
    let coeffs = base
        .coeffs
        .iter()
        .map(|&coeff| coeff.min(rhs).max(0))
        .collect();
    CpInequality::new(coeffs, rhs)
}

fn div_ceil(a: i64, b: i64) -> i64 {
    debug_assert!(b > 0);
    if a >= 0 {
        (a + b - 1) / b
    } else {
        a / b
    }
}

fn normalize_clause(clause: &[Literal]) -> Vec<Literal> {
    let mut normalized = clause.to_vec();
    normalized.sort_unstable();
    normalized.dedup();
    normalized
}

fn max_var_in_resolution_proof(proof: &ResolutionProof) -> usize {
    (0..proof.len())
        .filter_map(|idx| proof.clause_at(idx))
        .flat_map(|clause| clause.iter().copied())
        .map(|lit| var_of(lit) as usize)
        .max()
        .unwrap_or(0)
}

fn clause_to_cp_inequality(clause: &[Literal], num_vars: usize) -> CpInequality {
    let effective_num_vars = num_vars.max(
        clause
            .iter()
            .map(|&lit| var_of(lit) as usize)
            .max()
            .unwrap_or(0),
    );
    let mut coeffs = vec![0i64; effective_num_vars];
    let mut negative_literals = 0i64;

    for &lit in clause {
        let var = var_of(lit) as usize;
        if var == 0 {
            continue;
        }
        if lit > 0 {
            coeffs[var - 1] += 1;
        } else {
            coeffs[var - 1] -= 1;
            negative_literals += 1;
        }
    }

    CpInequality::new(coeffs, 1 - negative_literals)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn simple_resolution_refutation() -> ResolutionProof {
        let mut proof = ResolutionProof::new();
        let left = proof.add_input(vec![1]);
        let right = proof.add_input(vec![-1]);
        proof
            .add_resolve(left, right, 1)
            .expect("resolution should succeed");
        proof
    }

    #[test]
    fn test_verify_pc01_resolution_soundness_success() {
        let proof = simple_resolution_refutation();

        let certificate = verify_pc01_resolution_soundness(&proof);

        assert!(certificate.verified);
        assert_eq!(certificate.theorem_id, "PC01");
        assert!(matches!(
            certificate.evidence,
            PcCertificateEvidence::ResolutionSoundness {
                proof_steps: 3,
                resolve_steps: 1,
                all_resolve_steps_sound: true,
                ..
            }
        ));
    }

    #[test]
    fn test_verify_pc02_resolution_completeness_success() {
        let clauses = vec![vec![1], vec![-1]];
        let proof = simple_resolution_refutation();

        let certificate = verify_pc02_resolution_completeness(&clauses, &proof);

        assert!(certificate.verified);
        assert!(matches!(
            certificate.evidence,
            PcCertificateEvidence::ResolutionCompleteness {
                num_clauses: 2,
                proof_steps: 3,
                inputs_covered: true,
                derives_empty_clause: true,
            }
        ));
    }

    #[test]
    fn test_verify_pc02_resolution_completeness_failure_for_missing_input() {
        let clauses = vec![vec![1]];
        let proof = simple_resolution_refutation();

        let certificate = verify_pc02_resolution_completeness(&clauses, &proof);

        assert!(!certificate.verified);
        assert_eq!(
            certificate.witness_data["missing_inputs"],
            serde_json::json!([[-1]])
        );
    }

    #[test]
    fn test_verify_pc03_cp_soundness_success() {
        let mut proof = CuttingPlanesProof::new();
        let left = proof.add_input(CpInequality::new(vec![1], 1));
        let right = proof.add_input(CpInequality::new(vec![-1], 0));
        let derived = proof.add(left, right).expect("addition should succeed");

        let certificate = verify_pc03_cp_soundness(&proof);

        assert!(certificate.verified);
        assert_eq!(
            proof.inequality_at(derived).unwrap(),
            &CpInequality::new(vec![0], 1)
        );
        assert!(matches!(
            certificate.evidence,
            PcCertificateEvidence::CuttingPlanesSoundness {
                proof_steps: 3,
                derived_steps: 1,
                all_rule_applications_sound: true,
                derives_contradiction: true,
            }
        ));
    }

    #[test]
    fn test_verify_pc04_cp_subsumes_resolution_success() {
        let proof = simple_resolution_refutation();

        let certificate = verify_pc04_cp_subsumes_resolution(&proof);

        assert!(certificate.verified);
        assert!(matches!(
            certificate.evidence,
            PcCertificateEvidence::CpSubsumesResolution {
                resolution_steps: 3,
                simulation_valid: true,
                derives_cp_contradiction: true,
                ..
            }
        ));
    }

    #[test]
    fn test_pc_kernel_proofs_verify_all_returns_all_certificates() {
        let clauses = vec![vec![1], vec![-1]];
        let resolution_proof = simple_resolution_refutation();
        let mut cp_proof = CuttingPlanesProof::new();
        let left = cp_proof.add_input(CpInequality::new(vec![1], 1));
        let right = cp_proof.add_input(CpInequality::new(vec![-1], 0));
        cp_proof.add(left, right).expect("addition should succeed");

        let certificates = verify_all(&clauses, &resolution_proof, &cp_proof);

        assert_eq!(certificates.len(), 4);
        assert_eq!(
            certificates
                .iter()
                .map(|certificate| certificate.theorem_id)
                .collect::<Vec<_>>(),
            vec!["PC01", "PC02", "PC03", "PC04"]
        );
    }

    #[test]
    fn test_pc_kernel_proofs_struct_holds_each_certificate() {
        let clauses = vec![vec![1], vec![-1]];
        let resolution_proof = simple_resolution_refutation();
        let mut cp_proof = CuttingPlanesProof::new();
        let left = cp_proof.add_input(CpInequality::new(vec![1], 1));
        let right = cp_proof.add_input(CpInequality::new(vec![-1], 0));
        cp_proof.add(left, right).expect("addition should succeed");

        let proofs = PcKernelProofs::from_proofs(&clauses, &resolution_proof, &cp_proof);

        assert_eq!(proofs.pc01.theorem_name, "resolution_soundness");
        assert_eq!(proofs.pc04.theorem_name, "cp_subsumes_resolution");
        assert_eq!(proofs.as_vec().len(), 4);
    }

    #[test]
    fn test_pc_certificate_json_serialization() {
        let proof = simple_resolution_refutation();
        let certificate = verify_pc01_resolution_soundness(&proof);

        let json = certificate
            .to_json()
            .expect("certificate JSON serialization should succeed");
        let parsed: Value =
            serde_json::from_str(&json).expect("serialized certificate should parse");

        assert_eq!(parsed["theorem_id"], serde_json::json!("PC01"));
        assert_eq!(
            parsed["theorem_name"],
            serde_json::json!("resolution_soundness")
        );
    }

    #[test]
    fn test_pc_kernel_proofs_json_serialization() {
        let clauses = vec![vec![1], vec![-1]];
        let resolution_proof = simple_resolution_refutation();
        let mut cp_proof = CuttingPlanesProof::new();
        let left = cp_proof.add_input(CpInequality::new(vec![1], 1));
        let right = cp_proof.add_input(CpInequality::new(vec![-1], 0));
        cp_proof.add(left, right).expect("addition should succeed");

        let proofs = PcKernelProofs::from_proofs(&clauses, &resolution_proof, &cp_proof);
        let json = proofs
            .to_json()
            .expect("proof bundle JSON serialization should succeed");
        let parsed: Value = serde_json::from_str(&json).expect("serialized bundle should parse");

        assert_eq!(parsed["pc03"]["theorem_id"], serde_json::json!("PC03"));
        assert_eq!(
            parsed["pc04"]["evidence"]["kind"],
            serde_json::json!("cp_subsumes_resolution")
        );
    }
}
