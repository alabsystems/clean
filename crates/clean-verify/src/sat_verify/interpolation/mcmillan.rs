// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! McMillan's Interpolation Algorithm
//!
//! Given a resolution refutation of A AND B, extract an interpolant I such that:
//! - A implies I
//! - I AND B is unsatisfiable
//! - Vars(I) is a subset of Vars(A) intersect Vars(B)
//!
//! The algorithm traverses the resolution DAG bottom-up, labeling each node's
//! interpolant based on whether the input clause is from partition A or B,
//! and whether pivot variables are shared.
//!
//! ## Reference
//!
//! McMillan (2003): "Interpolation and SAT-Based Model Checking", CAV 2003.

use super::PropFormula;
use crate::sat_verify::cdcl::{var_of, Clause, Literal};
use std::collections::HashSet;

/// Partition label for clauses in the A/B split.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Partition {
    A,
    B,
}

/// A node in a resolution DAG.
#[derive(Debug, Clone)]
pub enum ResolutionDagNode {
    /// An input clause from partition A or B.
    Input {
        clause: Clause,
        partition: Partition,
    },
    /// A resolution step combining two sub-proofs on a pivot variable.
    Resolve {
        left: usize,
        right: usize,
        pivot: Literal,
    },
}

/// A resolution DAG for interpolant extraction.
#[derive(Debug, Clone)]
pub struct ResolutionDag {
    pub nodes: Vec<ResolutionDagNode>,
    pub clauses: Vec<Clause>,
}

/// Classification of a variable relative to A/B partitioning.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VarClass {
    /// Appears only in A-clauses.
    AOnly,
    /// Appears only in B-clauses.
    BOnly,
    /// Appears in both A and B (shared).
    Shared,
}

impl ResolutionDag {
    #[must_use]
    pub fn new() -> Self {
        Self {
            nodes: Vec::new(),
            clauses: Vec::new(),
        }
    }

    /// Add an input clause. Returns its node index.
    pub fn add_input(&mut self, clause: Clause, partition: Partition) -> usize {
        let idx = self.nodes.len();
        self.clauses.push(clause.clone());
        self.nodes
            .push(ResolutionDagNode::Input { clause, partition });
        idx
    }

    /// Add a resolution step. Returns its node index.
    pub fn add_resolve(&mut self, left: usize, right: usize, pivot: Literal) -> usize {
        let idx = self.nodes.len();
        let pvar = var_of(pivot);
        let mut resolvent: Vec<Literal> = Vec::new();
        if let (Some(cl), Some(cr)) = (self.clauses.get(left), self.clauses.get(right)) {
            for &lit in cl.iter().chain(cr.iter()) {
                if var_of(lit) == pvar {
                    continue;
                }
                if !resolvent.contains(&lit) {
                    resolvent.push(lit);
                }
            }
        }
        resolvent.sort_by_key(|l| (var_of(*l), *l < 0));
        self.clauses.push(resolvent);
        self.nodes
            .push(ResolutionDagNode::Resolve { left, right, pivot });
        idx
    }

    /// Classify all variables as A-only, B-only, or shared.
    #[must_use]
    pub fn classify_variables(&self) -> std::collections::HashMap<u32, VarClass> {
        let mut a_vars = HashSet::new();
        let mut b_vars = HashSet::new();
        for node in &self.nodes {
            if let ResolutionDagNode::Input { clause, partition } = node {
                let set = match partition {
                    Partition::A => &mut a_vars,
                    Partition::B => &mut b_vars,
                };
                for &lit in clause {
                    set.insert(var_of(lit));
                }
            }
        }
        let mut result = std::collections::HashMap::new();
        for &v in a_vars.iter().chain(b_vars.iter()) {
            let in_a = a_vars.contains(&v);
            let in_b = b_vars.contains(&v);
            let class = match (in_a, in_b) {
                (true, true) => VarClass::Shared,
                (true, false) => VarClass::AOnly,
                (false, true) => VarClass::BOnly,
                (false, false) => unreachable!(),
            };
            result.insert(v, class);
        }
        result
    }
}

impl Default for ResolutionDag {
    fn default() -> Self {
        Self::new()
    }
}

/// Compute the partial interpolant for an A-partition input clause.
///
/// Returns the disjunction of shared-variable literals from the clause.
fn a_input_interpolant(
    clause: &[Literal],
    var_class: &std::collections::HashMap<u32, VarClass>,
) -> PropFormula {
    let shared_lits: Vec<PropFormula> = clause
        .iter()
        .filter(|&&lit| matches!(var_class.get(&var_of(lit)), Some(VarClass::Shared)))
        .map(|&lit| {
            let v = var_of(lit);
            if lit > 0 {
                PropFormula::Var(v)
            } else {
                PropFormula::Not(Box::new(PropFormula::Var(v)))
            }
        })
        .collect();
    match shared_lits.len() {
        0 => PropFormula::False,
        1 => shared_lits.into_iter().next().expect("checked len"),
        _ => shared_lits
            .into_iter()
            .reduce(|a, b| PropFormula::Or(Box::new(a), Box::new(b)))
            .expect("non-empty"),
    }
}

/// Compute the interpolant for a resolution step.
///
/// - Shared pivot: Pudlak's rule `(p AND I_neg) OR (NOT p AND I_pos)`
/// - A-only pivot: `I_left OR I_right`
/// - B-only pivot: `I_left AND I_right`
fn resolve_interpolant(
    dag: &ResolutionDag,
    left: usize,
    right: usize,
    pivot: &Literal,
    i_left: PropFormula,
    i_right: PropFormula,
    var_class: &std::collections::HashMap<u32, VarClass>,
) -> PropFormula {
    let pvar = var_of(*pivot);
    match var_class.get(&pvar) {
        Some(VarClass::Shared) => {
            let left_has_pos = dag.clauses.get(left).is_some_and(|c| c.contains(pivot));
            let (i_pos, i_neg) = if left_has_pos {
                (i_left, i_right)
            } else {
                (i_right, i_left)
            };
            let p = PropFormula::Var(pvar);
            let not_p = PropFormula::Not(Box::new(p.clone()));
            PropFormula::Or(
                Box::new(PropFormula::AndType(Box::new(p), Box::new(i_neg))),
                Box::new(PropFormula::AndType(Box::new(not_p), Box::new(i_pos))),
            )
        }
        Some(VarClass::AOnly) | None => PropFormula::Or(Box::new(i_left), Box::new(i_right)),
        Some(VarClass::BOnly) => PropFormula::AndType(Box::new(i_left), Box::new(i_right)),
    }
}

/// Extract a McMillan interpolant from a resolution DAG.
///
/// Traverses the DAG bottom-up, computing partial interpolants per node.
/// See [`a_input_interpolant`] and [`resolve_interpolant`] for per-node rules.
#[must_use]
pub fn extract_mcmillan_interpolant(dag: &ResolutionDag) -> PropFormula {
    let var_class = dag.classify_variables();
    if dag.nodes.is_empty() {
        return PropFormula::True;
    }
    let mut interpolants: Vec<PropFormula> = Vec::with_capacity(dag.nodes.len());

    for node in &dag.nodes {
        let interp = match node {
            ResolutionDagNode::Input { clause, partition } => match partition {
                Partition::A => a_input_interpolant(clause, &var_class),
                Partition::B => PropFormula::True,
            },
            ResolutionDagNode::Resolve { left, right, pivot } => {
                let i_left = interpolants[*left].clone();
                let i_right = interpolants[*right].clone();
                resolve_interpolant(dag, *left, *right, pivot, i_left, i_right, &var_class)
            }
        };
        interpolants.push(interp);
    }

    interpolants.pop().unwrap_or(PropFormula::True).simplify()
}

/// Verify the shared-variable property: all variables in the interpolant
/// appear in both A-clauses and B-clauses.
pub fn verify_shared_variable_property(
    dag: &ResolutionDag,
    interpolant: &PropFormula,
) -> Result<(), Vec<u32>> {
    let var_class = dag.classify_variables();
    let interp_vars = interpolant.variables();
    let violations: Vec<u32> = interp_vars
        .into_iter()
        .filter(|v| !matches!(var_class.get(v), Some(VarClass::Shared)))
        .collect();
    if violations.is_empty() {
        Ok(())
    } else {
        Err(violations)
    }
}

// Re-export tree interpolation types and functions from the split module.
pub use super::mcmillan_tree::{
    count_interpolant_models, interpolant_size, strengthen_interpolant, tree_interpolant,
    verify_interpolant_property, weaken_interpolant, InterpolantVerifyResult, NodeKind,
};

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_dag_classify_variables() {
        let mut dag = ResolutionDag::new();
        dag.add_input(vec![1, 2], Partition::A);
        dag.add_input(vec![-2, 3], Partition::B);
        let classes = dag.classify_variables();
        assert_eq!(classes[&1], VarClass::AOnly);
        assert_eq!(classes[&2], VarClass::Shared);
        assert_eq!(classes[&3], VarClass::BOnly);
    }

    #[test]
    fn test_mcmillan_trivial_a_only() {
        let mut dag = ResolutionDag::new();
        let a = dag.add_input(vec![1], Partition::A);
        let b = dag.add_input(vec![-1], Partition::B);
        dag.add_resolve(a, b, 1);
        let interp = extract_mcmillan_interpolant(&dag);
        let vars = interp.variables();
        assert!(vars.is_subset(&HashSet::from([1])));
    }

    #[test]
    fn test_mcmillan_b_input_is_true() {
        let mut dag = ResolutionDag::new();
        dag.add_input(vec![1, 2], Partition::B);
        let interp = extract_mcmillan_interpolant(&dag);
        assert_eq!(interp, PropFormula::True);
    }

    #[test]
    fn test_shared_variable_property_valid() {
        let mut dag = ResolutionDag::new();
        let a = dag.add_input(vec![1, 2], Partition::A);
        let b = dag.add_input(vec![-2, 3], Partition::B);
        dag.add_resolve(a, b, 2);
        let interp = extract_mcmillan_interpolant(&dag);
        verify_shared_variable_property(&dag, &interp)
            .expect("should satisfy shared-variable property");
    }

    #[test]
    fn test_resolution_dag_default() {
        let dag = ResolutionDag::default();
        assert!(dag.nodes.is_empty());
    }

    #[test]
    fn test_var_class_enum_values() {
        assert_ne!(VarClass::AOnly, VarClass::BOnly);
        assert_ne!(VarClass::AOnly, VarClass::Shared);
        assert_ne!(VarClass::BOnly, VarClass::Shared);
    }
}
