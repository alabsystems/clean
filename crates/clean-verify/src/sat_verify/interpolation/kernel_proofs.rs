// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Kernel-level proof certificates for interpolation invariants I01-I04.
//!
//! These certificates turn the runtime interpolation checks into structured,
//! serializable artifacts that can be consumed by the proof promotion pipeline.

use super::{
    mcmillan::{
        extract_mcmillan_interpolant, verify_shared_variable_property, Partition, ResolutionDag,
        ResolutionDagNode, VarClass,
    },
    PropFormula,
};
use crate::sat_verify::cdcl::{var_of, Clause, Literal};
use serde::Serialize;
use serde_json::{json, Value};
use std::collections::{HashMap, HashSet};
use thiserror::Error;

#[derive(Debug, Error)]
pub(crate) enum InterpKernelProofError {
    #[error("failed to serialize interpolation kernel proof data")]
    Serialize(#[from] serde_json::Error),
}

#[derive(Debug, Clone, PartialEq, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub(crate) enum InterpCertificateEvidence {
    CraigExistence {
        a_implies_i: bool,
        i_and_b_unsat: bool,
        a_and_b_unsat: bool,
        is_refutation_dag: bool,
    },
    McMillanExtraction {
        node_count: usize,
        clause_count: usize,
        node_count_matches: bool,
        formula_extracted: bool,
    },
    SharedVariables {
        interpolant_var_count: usize,
        all_shared: bool,
    },
    PudlakRule {
        shared_pivot_count: usize,
        all_shared_pivots_valid: bool,
    },
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub(crate) struct InterpProofCertificate {
    pub(crate) theorem_id: &'static str,
    pub(crate) theorem_name: &'static str,
    pub(crate) verified: bool,
    pub(crate) evidence: InterpCertificateEvidence,
    pub(crate) witness_data: Value,
}

impl InterpProofCertificate {
    #[must_use]
    fn new(
        theorem_id: &'static str,
        theorem_name: &'static str,
        verified: bool,
        evidence: InterpCertificateEvidence,
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

    pub(crate) fn to_json(&self) -> Result<String, InterpKernelProofError> {
        serde_json::to_string(self).map_err(InterpKernelProofError::from)
    }
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub(crate) struct InterpKernelProofs {
    pub(crate) i01: InterpProofCertificate,
    pub(crate) i02: InterpProofCertificate,
    pub(crate) i03: InterpProofCertificate,
    pub(crate) i04: InterpProofCertificate,
}

impl InterpKernelProofs {
    #[must_use]
    pub(crate) fn from_dag(dag: &ResolutionDag) -> Self {
        Self {
            i01: verify_i01_craig_existence(dag),
            i02: verify_i02_mcmillan_extraction(dag),
            i03: verify_i03_shared_variables(dag),
            i04: verify_i04_pudlak_rule(dag),
        }
    }

    #[must_use]
    pub(crate) fn as_vec(&self) -> Vec<InterpProofCertificate> {
        vec![
            self.i01.clone(),
            self.i02.clone(),
            self.i03.clone(),
            self.i04.clone(),
        ]
    }

    #[must_use]
    pub(crate) fn verify_all(dag: &ResolutionDag) -> Vec<InterpProofCertificate> {
        Self::from_dag(dag).as_vec()
    }

    pub(crate) fn to_json(&self) -> Result<String, InterpKernelProofError> {
        serde_json::to_string(self).map_err(InterpKernelProofError::from)
    }
}

#[must_use]
pub(crate) fn verify_all(dag: &ResolutionDag) -> Vec<InterpProofCertificate> {
    InterpKernelProofs::verify_all(dag)
}

#[must_use]
pub(crate) fn verify_i01_craig_existence(dag: &ResolutionDag) -> InterpProofCertificate {
    let shape_error = validate_dag_shape(dag).err();
    let interpolant = if shape_error.is_none() {
        Some(extract_mcmillan_interpolant(dag))
    } else {
        None
    };

    let a_clauses = partition_clauses(dag, Partition::A);
    let b_clauses = partition_clauses(dag, Partition::B);
    let variables = collect_input_variables(dag);
    let a_and_b_counterexample = find_assignment(&variables, &|assignment| {
        cnf_satisfied(&a_clauses, assignment) && cnf_satisfied(&b_clauses, assignment)
    });

    let a_implies_i_counterexample = interpolant.as_ref().and_then(|formula| {
        find_assignment(&variables, &|assignment| {
            cnf_satisfied(&a_clauses, assignment) && !formula.evaluate(assignment)
        })
    });
    let i_and_b_counterexample = interpolant.as_ref().and_then(|formula| {
        find_assignment(&variables, &|assignment| {
            formula.evaluate(assignment) && cnf_satisfied(&b_clauses, assignment)
        })
    });

    let a_and_b_unsat = a_and_b_counterexample.is_none();
    let a_implies_i = a_implies_i_counterexample.is_none() && interpolant.is_some();
    let i_and_b_unsat = i_and_b_counterexample.is_none() && interpolant.is_some();
    let is_refutation_dag = is_refutation_dag(dag);
    let verified =
        shape_error.is_none() && is_refutation_dag && a_and_b_unsat && a_implies_i && i_and_b_unsat;

    InterpProofCertificate::new(
        "I01",
        "craig_existence",
        verified,
        InterpCertificateEvidence::CraigExistence {
            a_implies_i,
            i_and_b_unsat,
            a_and_b_unsat,
            is_refutation_dag,
        },
        json!({
            "validation_error": shape_error,
            "interpolant": interpolant.as_ref().map(formula_to_string),
            "root_clause": dag.clauses.last().cloned(),
            "a_clause_count": a_clauses.len(),
            "b_clause_count": b_clauses.len(),
            "variables": variables,
            "a_and_b_counterexample": assignment_to_json(a_and_b_counterexample.as_deref()),
            "a_implies_i_counterexample": assignment_to_json(a_implies_i_counterexample.as_deref()),
            "i_and_b_counterexample": assignment_to_json(i_and_b_counterexample.as_deref()),
        }),
    )
}

#[must_use]
pub(crate) fn verify_i02_mcmillan_extraction(dag: &ResolutionDag) -> InterpProofCertificate {
    let shape_error = validate_dag_shape(dag).err();
    let (interpolant, prefix_interpolants) = if shape_error.is_none() {
        let extracted = extract_mcmillan_interpolant(dag);
        let prefixes = extract_prefix_interpolants(dag);
        (Some(extracted), prefixes)
    } else {
        (None, Vec::new())
    };

    let node_count = dag.nodes.len();
    let clause_count = dag.clauses.len();
    let node_count_matches = node_count == clause_count && prefix_interpolants.len() == node_count;
    let formula_extracted = interpolant.is_some() && is_refutation_dag(dag);
    let root_matches = interpolant.as_ref() == prefix_interpolants.last();
    let verified = shape_error.is_none()
        && is_refutation_dag(dag)
        && node_count_matches
        && formula_extracted
        && root_matches;

    InterpProofCertificate::new(
        "I02",
        "mcmillan_extraction",
        verified,
        InterpCertificateEvidence::McMillanExtraction {
            node_count,
            clause_count,
            node_count_matches,
            formula_extracted,
        },
        json!({
            "validation_error": shape_error,
            "is_refutation_dag": is_refutation_dag(dag),
            "interpolant": interpolant.as_ref().map(formula_to_string),
            "root_matches": root_matches,
            "per_node_interpolants": prefix_interpolants
                .iter()
                .enumerate()
                .map(|(index, formula)| {
                    json!({
                        "node_index": index,
                        "interpolant": formula_to_string(formula),
                    })
                })
                .collect::<Vec<_>>(),
        }),
    )
}

#[must_use]
pub(crate) fn verify_i03_shared_variables(dag: &ResolutionDag) -> InterpProofCertificate {
    let shape_error = validate_dag_shape(dag).err();
    let interpolant = if shape_error.is_none() {
        Some(extract_mcmillan_interpolant(dag))
    } else {
        None
    };

    let property_result = interpolant
        .as_ref()
        .map(|formula| verify_shared_variable_property(dag, formula));
    let violations = match property_result {
        Some(Err(ref violations)) => violations.clone(),
        _ => Vec::new(),
    };
    let interpolant_variables = interpolant
        .as_ref()
        .map_or_else(Vec::new, sorted_formula_variables);
    let all_shared =
        shape_error.is_none() && is_refutation_dag(dag) && property_result == Some(Ok(()));

    InterpProofCertificate::new(
        "I03",
        "shared_variables",
        all_shared,
        InterpCertificateEvidence::SharedVariables {
            interpolant_var_count: interpolant_variables.len(),
            all_shared,
        },
        json!({
            "validation_error": shape_error,
            "is_refutation_dag": is_refutation_dag(dag),
            "interpolant": interpolant.as_ref().map(formula_to_string),
            "interpolant_variables": interpolant_variables,
            "violations": violations,
            "variable_classes": classify_variables_json(dag),
        }),
    )
}

#[must_use]
pub(crate) fn verify_i04_pudlak_rule(dag: &ResolutionDag) -> InterpProofCertificate {
    let shape_error = validate_dag_shape(dag).err();
    let shared_pivot_checks = if shape_error.is_none() {
        collect_shared_pivot_checks(dag)
    } else {
        Vec::new()
    };
    let shared_pivot_count = shared_pivot_checks.len();
    let all_shared_pivots_valid =
        shared_pivot_count > 0 && shared_pivot_checks.iter().all(|check| check.valid);
    let verified = shape_error.is_none() && is_refutation_dag(dag) && all_shared_pivots_valid;

    InterpProofCertificate::new(
        "I04",
        "pudlak_rule",
        verified,
        InterpCertificateEvidence::PudlakRule {
            shared_pivot_count,
            all_shared_pivots_valid,
        },
        json!({
            "validation_error": shape_error,
            "is_refutation_dag": is_refutation_dag(dag),
            "shared_pivot_nodes": shared_pivot_checks
                .iter()
                .map(|check| {
                    json!({
                        "node_index": check.node_index,
                        "pivot": check.pivot,
                        "left": check.left,
                        "right": check.right,
                        "complementary_pivot": check.complementary_pivot,
                        "expected_formula": check.expected_formula,
                        "actual_formula": check.actual_formula,
                        "counterexample": assignment_to_json(check.counterexample.as_deref()),
                        "valid": check.valid,
                    })
                })
                .collect::<Vec<_>>(),
        }),
    )
}

fn validate_dag_shape(dag: &ResolutionDag) -> Result<(), String> {
    if dag.nodes.len() != dag.clauses.len() {
        return Err(format!(
            "node/clause count mismatch: {} nodes vs {} clauses",
            dag.nodes.len(),
            dag.clauses.len()
        ));
    }

    for (index, node) in dag.nodes.iter().enumerate() {
        if let ResolutionDagNode::Resolve { left, right, .. } = node {
            if *left >= index || *right >= index {
                return Err(format!(
                    "node {index} is not topologically ordered: left={left}, right={right}"
                ));
            }
        }
    }

    Ok(())
}

fn is_refutation_dag(dag: &ResolutionDag) -> bool {
    if validate_dag_shape(dag).is_err() {
        return false;
    }

    let has_a = dag.nodes.iter().any(|node| {
        matches!(
            node,
            ResolutionDagNode::Input {
                partition: Partition::A,
                ..
            }
        )
    });
    let has_b = dag.nodes.iter().any(|node| {
        matches!(
            node,
            ResolutionDagNode::Input {
                partition: Partition::B,
                ..
            }
        )
    });
    let root_is_empty = dag.clauses.last().is_some_and(Vec::is_empty);

    has_a && has_b && root_is_empty
}

fn partition_clauses(dag: &ResolutionDag, partition: Partition) -> Vec<Clause> {
    dag.nodes
        .iter()
        .filter_map(|node| match node {
            ResolutionDagNode::Input {
                clause,
                partition: node_partition,
            } if *node_partition == partition => Some(clause.clone()),
            _ => None,
        })
        .collect()
}

fn collect_input_variables(dag: &ResolutionDag) -> Vec<u32> {
    let mut variables = HashSet::new();
    for node in &dag.nodes {
        if let ResolutionDagNode::Input { clause, .. } = node {
            for &lit in clause {
                variables.insert(var_of(lit));
            }
        }
    }
    let mut sorted: Vec<u32> = variables.into_iter().collect();
    sorted.sort_unstable();
    sorted
}

fn extract_prefix_interpolants(dag: &ResolutionDag) -> Vec<PropFormula> {
    (0..dag.nodes.len())
        .map(|index| extract_mcmillan_interpolant(&dag_prefix(dag, index)))
        .collect()
}

fn dag_prefix(dag: &ResolutionDag, last_index: usize) -> ResolutionDag {
    ResolutionDag {
        nodes: dag.nodes[..=last_index].to_vec(),
        clauses: dag.clauses[..=last_index].to_vec(),
    }
}

fn formula_to_string(formula: &PropFormula) -> String {
    format!("{formula}")
}

fn sorted_formula_variables(formula: &PropFormula) -> Vec<u32> {
    let mut variables: Vec<u32> = formula.variables().into_iter().collect();
    variables.sort_unstable();
    variables
}

fn classify_variables_json(dag: &ResolutionDag) -> Vec<Value> {
    let mut entries: Vec<(u32, VarClass)> = dag.classify_variables().into_iter().collect();
    entries.sort_unstable_by_key(|(var, _)| *var);
    entries
        .into_iter()
        .map(|(var, class)| {
            json!({
                "var": var,
                "class": match class {
                    VarClass::AOnly => "a_only",
                    VarClass::BOnly => "b_only",
                    VarClass::Shared => "shared",
                },
            })
        })
        .collect()
}

fn cnf_satisfied(clauses: &[Clause], assignment: &HashMap<u32, bool>) -> bool {
    clauses
        .iter()
        .all(|clause| clause_satisfied(clause, assignment))
}

fn clause_satisfied(clause: &[Literal], assignment: &HashMap<u32, bool>) -> bool {
    clause
        .iter()
        .copied()
        .any(|lit| literal_satisfied(lit, assignment))
}

fn literal_satisfied(lit: Literal, assignment: &HashMap<u32, bool>) -> bool {
    assignment
        .get(&var_of(lit))
        .copied()
        .map(|value| if lit > 0 { value } else { !value })
        .unwrap_or(false)
}

fn find_assignment(
    variables: &[u32],
    predicate: &dyn Fn(&HashMap<u32, bool>) -> bool,
) -> Option<Vec<(u32, bool)>> {
    let mut assignment = HashMap::with_capacity(variables.len());
    search_assignment(variables, 0, &mut assignment, predicate)
}

fn search_assignment(
    variables: &[u32],
    index: usize,
    assignment: &mut HashMap<u32, bool>,
    predicate: &dyn Fn(&HashMap<u32, bool>) -> bool,
) -> Option<Vec<(u32, bool)>> {
    if index == variables.len() {
        if predicate(assignment) {
            return Some(
                variables
                    .iter()
                    .map(|var| (*var, assignment.get(var).copied().unwrap_or(false)))
                    .collect(),
            );
        }
        return None;
    }

    let variable = variables[index];
    assignment.insert(variable, false);
    if let Some(counterexample) = search_assignment(variables, index + 1, assignment, predicate) {
        return Some(counterexample);
    }

    assignment.insert(variable, true);
    if let Some(counterexample) = search_assignment(variables, index + 1, assignment, predicate) {
        return Some(counterexample);
    }

    assignment.remove(&variable);
    None
}

fn assignment_to_json(assignment: Option<&[(u32, bool)]>) -> Value {
    match assignment {
        Some(entries) => json!(entries
            .iter()
            .map(|(var, value)| json!({ "var": var, "value": value }))
            .collect::<Vec<_>>()),
        None => Value::Null,
    }
}

fn formulas_equivalent(left: &PropFormula, right: &PropFormula) -> Option<Vec<(u32, bool)>> {
    let left_variables = left.variables();
    let right_variables = right.variables();
    let mut variables: Vec<u32> = left_variables.union(&right_variables).copied().collect();
    variables.sort_unstable();
    variables.dedup();

    find_assignment(&variables, &|assignment| {
        left.evaluate(assignment) != right.evaluate(assignment)
    })
}

#[derive(Debug, Clone)]
struct SharedPivotCheck {
    node_index: usize,
    pivot: Literal,
    left: usize,
    right: usize,
    complementary_pivot: bool,
    expected_formula: Option<String>,
    actual_formula: String,
    counterexample: Option<Vec<(u32, bool)>>,
    valid: bool,
}

fn collect_shared_pivot_checks(dag: &ResolutionDag) -> Vec<SharedPivotCheck> {
    let var_classes = dag.classify_variables();
    let prefix_interpolants = extract_prefix_interpolants(dag);
    let mut checks = Vec::new();

    for (index, node) in dag.nodes.iter().enumerate() {
        let ResolutionDagNode::Resolve { left, right, pivot } = node else {
            continue;
        };
        if !matches!(var_classes.get(&var_of(*pivot)), Some(VarClass::Shared)) {
            continue;
        }

        let left_formula = prefix_interpolants[*left].clone();
        let right_formula = prefix_interpolants[*right].clone();
        let actual_formula = prefix_interpolants[index].clone();
        let expected =
            expected_shared_pivot_formula(dag, *left, *right, *pivot, left_formula, right_formula);
        let complementary_pivot = expected.is_some();
        let counterexample = expected
            .as_ref()
            .and_then(|expected_formula| formulas_equivalent(expected_formula, &actual_formula));
        let valid = complementary_pivot && counterexample.is_none();

        checks.push(SharedPivotCheck {
            node_index: index,
            pivot: *pivot,
            left: *left,
            right: *right,
            complementary_pivot,
            expected_formula: expected.as_ref().map(formula_to_string),
            actual_formula: formula_to_string(&actual_formula),
            counterexample,
            valid,
        });
    }

    checks
}

fn expected_shared_pivot_formula(
    dag: &ResolutionDag,
    left: usize,
    right: usize,
    pivot: Literal,
    left_formula: PropFormula,
    right_formula: PropFormula,
) -> Option<PropFormula> {
    let left_clause = dag.clauses.get(left)?;
    let right_clause = dag.clauses.get(right)?;
    let left_has_pivot = left_clause.contains(&pivot);
    let right_has_pivot = right_clause.contains(&pivot);
    let left_has_complement = left_clause.contains(&-pivot);
    let right_has_complement = right_clause.contains(&-pivot);

    let (i_pos, i_neg) = if left_has_pivot && right_has_complement {
        (left_formula, right_formula)
    } else if right_has_pivot && left_has_complement {
        (right_formula, left_formula)
    } else {
        return None;
    };

    let variable = PropFormula::Var(var_of(pivot));
    let not_variable = PropFormula::Not(Box::new(variable.clone()));
    Some(
        PropFormula::Or(
            Box::new(PropFormula::AndType(Box::new(variable), Box::new(i_neg))),
            Box::new(PropFormula::AndType(
                Box::new(not_variable),
                Box::new(i_pos),
            )),
        )
        .simplify(),
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::{json, Value};

    fn simple_refutation_dag() -> ResolutionDag {
        let mut dag = ResolutionDag::new();
        let a = dag.add_input(vec![1], Partition::A);
        let b = dag.add_input(vec![-1], Partition::B);
        dag.add_resolve(a, b, 1);
        dag
    }

    fn non_refutation_dag() -> ResolutionDag {
        let mut dag = ResolutionDag::new();
        dag.add_input(vec![1], Partition::A);
        dag
    }

    fn malformed_count_dag() -> ResolutionDag {
        let mut dag = simple_refutation_dag();
        dag.clauses.pop();
        dag
    }

    fn invalid_shared_pivot_dag() -> ResolutionDag {
        let mut dag = ResolutionDag::new();
        let a = dag.add_input(vec![1], Partition::A);
        let b = dag.add_input(vec![1], Partition::B);
        dag.add_resolve(a, b, 1);
        dag
    }

    #[test]
    fn test_verify_i01_craig_existence_success() {
        let certificate = verify_i01_craig_existence(&simple_refutation_dag());

        assert!(certificate.verified);
        assert_eq!(certificate.theorem_id, "I01");
        assert!(matches!(
            certificate.evidence,
            InterpCertificateEvidence::CraigExistence {
                a_implies_i: true,
                i_and_b_unsat: true,
                a_and_b_unsat: true,
                is_refutation_dag: true,
            }
        ));
    }

    #[test]
    fn test_verify_i01_craig_existence_failure() {
        let certificate = verify_i01_craig_existence(&non_refutation_dag());

        assert!(!certificate.verified);
        assert_eq!(
            certificate.witness_data["a_and_b_counterexample"][0]["var"],
            json!(1u32)
        );
    }

    #[test]
    fn test_verify_i02_mcmillan_extraction_success() {
        let certificate = verify_i02_mcmillan_extraction(&simple_refutation_dag());

        assert!(certificate.verified);
        assert!(matches!(
            certificate.evidence,
            InterpCertificateEvidence::McMillanExtraction {
                node_count: 3,
                clause_count: 3,
                node_count_matches: true,
                formula_extracted: true,
            }
        ));
    }

    #[test]
    fn test_verify_i02_mcmillan_extraction_failure() {
        let certificate = verify_i02_mcmillan_extraction(&malformed_count_dag());

        assert!(!certificate.verified);
        assert_eq!(
            certificate.witness_data["validation_error"],
            json!("node/clause count mismatch: 3 nodes vs 2 clauses")
        );
    }

    #[test]
    fn test_verify_i03_shared_variables_success() {
        let certificate = verify_i03_shared_variables(&simple_refutation_dag());

        assert!(certificate.verified);
        assert!(matches!(
            certificate.evidence,
            InterpCertificateEvidence::SharedVariables {
                interpolant_var_count: 1,
                all_shared: true,
            }
        ));
    }

    #[test]
    fn test_verify_i03_shared_variables_failure() {
        let certificate = verify_i03_shared_variables(&ResolutionDag::new());

        assert!(!certificate.verified);
        assert_eq!(certificate.witness_data["is_refutation_dag"], json!(false));
    }

    #[test]
    fn test_verify_i04_pudlak_rule_success() {
        let certificate = verify_i04_pudlak_rule(&simple_refutation_dag());

        assert!(certificate.verified);
        assert!(matches!(
            certificate.evidence,
            InterpCertificateEvidence::PudlakRule {
                shared_pivot_count: 1,
                all_shared_pivots_valid: true,
            }
        ));
    }

    #[test]
    fn test_verify_i04_pudlak_rule_failure() {
        let certificate = verify_i04_pudlak_rule(&invalid_shared_pivot_dag());

        assert!(!certificate.verified);
        assert_eq!(
            certificate.witness_data["shared_pivot_nodes"][0]["complementary_pivot"],
            json!(false)
        );
    }

    #[test]
    fn test_interp_kernel_proofs_verify_all_returns_all_certificates() {
        let certificates = verify_all(&simple_refutation_dag());

        assert_eq!(certificates.len(), 4);
        assert_eq!(
            certificates
                .iter()
                .map(|certificate| certificate.theorem_id)
                .collect::<Vec<_>>(),
            vec!["I01", "I02", "I03", "I04"]
        );
    }

    #[test]
    fn test_interp_certificate_json_serialization() {
        let certificate = verify_i03_shared_variables(&simple_refutation_dag());

        let json = certificate
            .to_json()
            .expect("certificate JSON serialization should succeed");
        let parsed: Value =
            serde_json::from_str(&json).expect("serialized certificate should parse");

        assert_eq!(parsed["theorem_id"], json!("I03"));
        assert_eq!(parsed["theorem_name"], json!("shared_variables"));
    }

    #[test]
    fn test_interp_kernel_proofs_json_serialization() {
        let proofs = InterpKernelProofs::from_dag(&simple_refutation_dag());

        let json = proofs
            .to_json()
            .expect("proof bundle JSON serialization should succeed");
        let parsed: Value = serde_json::from_str(&json).expect("serialized bundle should parse");

        assert_eq!(parsed["i04"]["theorem_id"], json!("I04"));
        assert_eq!(parsed["i04"]["evidence"]["kind"], json!("pudlak_rule"));
    }
}
