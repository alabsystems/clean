// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Reverse (Pudlak) Interpolation
//!
//! Pudlak's algorithm computes interpolants bottom-up from a resolution DAG,
//! using a different rule than McMillan's for leaf nodes from partition B.
//!
//! For leaf nodes:
//!   - A-clause: interpolant = disjunction of shared literals
//!   - B-clause: interpolant = conjunction of negations of shared literals
//!
//! For internal nodes (resolution on pivot p):
//!   - Shared pivot: I = (p AND I_neg) OR (NOT p AND I_pos)
//!   - A-local pivot: I = I_pos OR I_neg
//!   - B-local pivot: I = I_pos AND I_neg
//!
//! The key difference from McMillan is the B-leaf rule: McMillan uses True,
//! Pudlak uses the conjunction of negated shared literals. This typically
//! produces smaller interpolants for certain proof structures.
//!
//! ## Reference
//!
//! Pudlak (1997): "Lower bounds on the size of interpolants"

use super::mcmillan::{Partition, ResolutionDag, ResolutionDagNode};
use super::PropFormula;
use crate::sat_verify::cdcl::var_of;
use crate::spec::ProofStatus;
use std::collections::{HashMap, HashSet};

/// Errors from reverse interpolation.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum ReverseInterpolationError {
    /// The DAG has no nodes.
    EmptyDag,
    /// A node at `index` has an invalid structure.
    InvalidNode { index: usize },
    /// A resolution node references a child that does not exist.
    MissingChild { node: usize, child: usize },
}

impl std::fmt::Display for ReverseInterpolationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::EmptyDag => write!(f, "empty DAG"),
            Self::InvalidNode { index } => write!(f, "invalid node at index {index}"),
            Self::MissingChild { node, child } => {
                write!(f, "node {node} references missing child {child}")
            }
        }
    }
}

impl std::error::Error for ReverseInterpolationError {}

/// Classify variables as A-only, B-only, or shared using the DAG's input clauses.
fn classify_vars(dag: &ResolutionDag) -> HashMap<u32, VarLocation> {
    let mut a_vars = HashSet::new();
    let mut b_vars = HashSet::new();
    for node in &dag.nodes {
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
    let mut result = HashMap::new();
    for &v in a_vars.iter().chain(b_vars.iter()) {
        let loc = match (a_vars.contains(&v), b_vars.contains(&v)) {
            (true, true) => VarLocation::Shared,
            (true, false) => VarLocation::AOnly,
            (false, _) => VarLocation::BOnly,
        };
        result.insert(v, loc);
    }
    result
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum VarLocation {
    AOnly,
    BOnly,
    Shared,
}

/// Compute the Pudlak interpolant for an A-partition leaf clause.
///
/// Returns the disjunction of shared-variable literals.
fn a_leaf_interpolant(clause: &[i32], var_loc: &HashMap<u32, VarLocation>) -> PropFormula {
    let shared: Vec<PropFormula> = clause
        .iter()
        .filter(|&&lit| matches!(var_loc.get(&var_of(lit)), Some(VarLocation::Shared)))
        .map(|&lit| {
            let v = var_of(lit);
            if lit > 0 {
                PropFormula::Var(v)
            } else {
                PropFormula::Not(Box::new(PropFormula::Var(v)))
            }
        })
        .collect();
    match shared.len() {
        0 => PropFormula::False,
        1 => shared.into_iter().next().expect("invariant: checked len"),
        _ => shared
            .into_iter()
            .reduce(|a, b| PropFormula::Or(Box::new(a), Box::new(b)))
            .expect("invariant: non-empty"),
    }
}

/// Compute the Pudlak interpolant for a B-partition leaf clause.
///
/// Returns the conjunction of negations of shared-variable literals.
/// This is the dual of the A-leaf rule.
fn b_leaf_interpolant(clause: &[i32], var_loc: &HashMap<u32, VarLocation>) -> PropFormula {
    let negated_shared: Vec<PropFormula> = clause
        .iter()
        .filter(|&&lit| matches!(var_loc.get(&var_of(lit)), Some(VarLocation::Shared)))
        .map(|&lit| {
            let v = var_of(lit);
            // Negate the literal: if clause has +v, interpolant gets NOT v
            if lit > 0 {
                PropFormula::Not(Box::new(PropFormula::Var(v)))
            } else {
                PropFormula::Var(v)
            }
        })
        .collect();
    match negated_shared.len() {
        0 => PropFormula::True,
        1 => negated_shared
            .into_iter()
            .next()
            .expect("invariant: checked len"),
        _ => negated_shared
            .into_iter()
            .reduce(|a, b| PropFormula::AndType(Box::new(a), Box::new(b)))
            .expect("invariant: non-empty"),
    }
}

/// Compute a Pudlak (reverse) interpolant from a resolution DAG.
///
/// Traverses the DAG bottom-up. For each node:
///   - A-leaf: disjunction of shared literals
///   - B-leaf: conjunction of negated shared literals
///   - Resolution on shared pivot p: (p AND I_neg) OR (NOT p AND I_pos)
///   - Resolution on A-local pivot: I_left OR I_right
///   - Resolution on B-local pivot: I_left AND I_right
///
/// # Errors
///
/// Returns `ReverseInterpolationError::EmptyDag` if the DAG has no nodes.
/// Returns `ReverseInterpolationError::MissingChild` if a resolution node
/// references a child index that does not exist.
pub fn pudlak_interpolation(
    dag: &ResolutionDag,
    _partition: &Partition,
    _shared_vars: &HashSet<u32>,
) -> Result<PropFormula, ReverseInterpolationError> {
    if dag.nodes.is_empty() {
        return Err(ReverseInterpolationError::EmptyDag);
    }

    let var_loc = classify_vars(dag);
    let mut interpolants: Vec<PropFormula> = Vec::with_capacity(dag.nodes.len());

    for (idx, node) in dag.nodes.iter().enumerate() {
        let interp = match node {
            ResolutionDagNode::Input { clause, partition } => match partition {
                Partition::A => a_leaf_interpolant(clause, &var_loc),
                Partition::B => b_leaf_interpolant(clause, &var_loc),
            },
            ResolutionDagNode::Resolve { left, right, pivot } => {
                if *left >= interpolants.len() {
                    return Err(ReverseInterpolationError::MissingChild {
                        node: idx,
                        child: *left,
                    });
                }
                if *right >= interpolants.len() {
                    return Err(ReverseInterpolationError::MissingChild {
                        node: idx,
                        child: *right,
                    });
                }
                let i_left = interpolants[*left].clone();
                let i_right = interpolants[*right].clone();
                let pvar = var_of(*pivot);

                match var_loc.get(&pvar) {
                    Some(VarLocation::Shared) => {
                        // Determine which child has the positive pivot
                        let left_has_pos =
                            dag.clauses.get(*left).is_some_and(|c| c.contains(pivot));
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
                    Some(VarLocation::AOnly) | None => {
                        PropFormula::Or(Box::new(i_left), Box::new(i_right))
                    }
                    Some(VarLocation::BOnly) => {
                        PropFormula::AndType(Box::new(i_left), Box::new(i_right))
                    }
                }
            }
        };
        interpolants.push(interp);
    }

    Ok(interpolants.pop().unwrap_or(PropFormula::True).simplify())
}

/// Compare the sizes of two interpolants (number of logical connectives).
///
/// Returns `(mcmillan_size, pudlak_size)`.
#[must_use]
pub fn compare_interpolant_size(mcmillan: &PropFormula, pudlak: &PropFormula) -> (usize, usize) {
    (formula_size(mcmillan), formula_size(pudlak))
}

/// Count the number of logical connectives (AndType, Or, Not, Implies) in a formula.
///
/// Variables and constants contribute 0.
#[must_use]
pub fn formula_size(formula: &PropFormula) -> usize {
    match formula {
        PropFormula::Var(_) | PropFormula::True | PropFormula::False => 0,
        PropFormula::Not(inner) => 1 + formula_size(inner),
        PropFormula::AndType(l, r) | PropFormula::Or(l, r) | PropFormula::Implies(l, r) => {
            1 + formula_size(l) + formula_size(r)
        }
    }
}

/// I04 implementation: Pudlak rule for shared pivots.
pub const I04_PUDLAK_IMPL: ProofStatus = ProofStatus::DerivedPending;
