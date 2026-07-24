// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Interpolation Sequence Extraction for Bounded Model Checking
//!
//! Given a BMC unrolling Init AND T_0 AND T_1 AND ... AND T_{k-1} AND NOT Bad,
//! extract a sequence of interpolants I_0, I_1, ..., I_k such that:
//!
//! 1. I_0 is implied by Init (initial states)
//! 2. For each i: I_i AND T_i implies I_{i+1} (transition preservation)
//! 3. I_k AND Bad is unsatisfiable (safety)
//! 4. All I_i use only state variables (shared between consecutive time steps)
//!
//! When a fixed point is reached (I_i implies I_{i+1}), the sequence
//! constitutes an inductive invariant proving the property for all depths.
//!
//! ## Reference
//!
//! McMillan (2003): "Interpolation and SAT-Based Model Checking", CAV 2003.

use super::mcmillan::{extract_mcmillan_interpolant, Partition, ResolutionDag, ResolutionDagNode};
use super::PropFormula;
use crate::sat_verify::cdcl::var_of;
use crate::spec::ProofStatus;
use std::collections::{HashMap, HashSet};

/// An interpolation sequence for BMC unrolling.
#[derive(Debug, Clone)]
pub struct InterpolationSequence {
    /// Interpolants I_0, I_1, ..., I_k.
    pub interpolants: Vec<PropFormula>,
    /// State variables (shared between consecutive time steps).
    pub state_vars: HashSet<u32>,
    /// Length of the BMC unrolling.
    pub depth: usize,
}

/// Result of verifying an interpolation sequence's properties.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum SequenceVerifyResult {
    /// All properties hold.
    Valid,
    /// I_0 is not implied by Init.
    InitNotImplied,
    /// I_i AND T_i does not imply I_{i+1} at the given step.
    TransitionGap { step: usize },
    /// I_k AND Bad is satisfiable.
    BadNotExcluded,
    /// Interpolant at `step` mentions a non-state variable.
    NonStateVariable { var: u32, step: usize },
}

/// Errors that can occur during interpolation sequence extraction.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum InterpolationError {
    /// No partitions were provided.
    EmptyPartitions,
    /// The DAG structure is inconsistent with the partition count.
    DagInconsistent,
    /// Extraction failed at a particular step.
    ExtractionFailed { step: usize },
}

impl std::fmt::Display for InterpolationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::EmptyPartitions => write!(f, "empty partition list"),
            Self::DagInconsistent => write!(f, "DAG inconsistent with partition count"),
            Self::ExtractionFailed { step } => write!(f, "extraction failed at step {step}"),
        }
    }
}

impl std::error::Error for InterpolationError {}

/// Partition a BMC formula into A/B pairs for each time step.
///
/// Given: Init AND T_0 AND T_1 AND ... AND T_{k-1} AND NOT Bad
///
/// For partition i (0 <= i < k):
///   A_i = Init AND T_0 AND ... AND T_{i-1}   (prefix up to step i)
///   B_i = T_i AND ... AND T_{k-1} AND NOT Bad (suffix from step i)
///
/// For i=0, A_0 = Init alone.
#[must_use]
pub fn bmc_partitions(
    init: &PropFormula,
    transitions: &[PropFormula],
    bad: &PropFormula,
) -> Vec<(PropFormula, PropFormula)> {
    let k = transitions.len();
    let neg_bad = PropFormula::Not(Box::new(bad.clone()));
    let mut partitions = Vec::with_capacity(k);

    for i in 0..k {
        // Build A_i = Init AND T_0 AND ... AND T_{i-1}
        let a_part = if i == 0 {
            init.clone()
        } else {
            let prefix = transitions[..i].iter().fold(init.clone(), |acc, t| {
                PropFormula::AndType(Box::new(acc), Box::new(t.clone()))
            });
            prefix
        };

        // Build B_i = T_i AND ... AND T_{k-1} AND NOT Bad
        let b_part = transitions[i..].iter().fold(neg_bad.clone(), |acc, t| {
            PropFormula::AndType(Box::new(t.clone()), Box::new(acc))
        });

        partitions.push((a_part, b_part));
    }

    partitions
}

/// Build a sub-DAG for a given partition by re-labeling input clauses.
///
/// Clauses whose variables are all in `a_vars` get partition A;
/// all others get partition B. Resolution structure is preserved.
fn build_partitioned_dag(dag: &ResolutionDag, a_vars: &HashSet<u32>) -> ResolutionDag {
    let mut new_dag = ResolutionDag::new();
    for node in &dag.nodes {
        match node {
            ResolutionDagNode::Input { clause, .. } => {
                let clause_vars: HashSet<u32> = clause.iter().map(|&lit| var_of(lit)).collect();
                let partition = if clause_vars.iter().all(|v| a_vars.contains(v)) {
                    Partition::A
                } else {
                    Partition::B
                };
                new_dag.add_input(clause.clone(), partition);
            }
            ResolutionDagNode::Resolve { left, right, pivot } => {
                new_dag.add_resolve(*left, *right, *pivot);
            }
        }
    }
    new_dag
}

/// Extract an interpolation sequence from a BMC refutation.
///
/// Each interpolant is extracted from the resolution DAG using McMillan's
/// algorithm with the corresponding A/B partition derived from the
/// set of variables in each partition's formula.
///
/// # Errors
///
/// Returns `InterpolationError::EmptyPartitions` if the partition list is empty.
/// Returns `InterpolationError::DagInconsistent` if the DAG has no nodes.
pub fn extract_interpolation_sequence(
    dag: &ResolutionDag,
    partitions: &[(PropFormula, PropFormula)],
    state_vars: &HashSet<u32>,
) -> Result<InterpolationSequence, InterpolationError> {
    if partitions.is_empty() {
        return Err(InterpolationError::EmptyPartitions);
    }
    if dag.nodes.is_empty() {
        return Err(InterpolationError::DagInconsistent);
    }

    let mut interpolants = Vec::with_capacity(partitions.len());

    for (i, (a_formula, _b_formula)) in partitions.iter().enumerate() {
        let a_vars = a_formula.variables();
        let partitioned = build_partitioned_dag(dag, &a_vars);

        if partitioned.nodes.is_empty() {
            return Err(InterpolationError::ExtractionFailed { step: i });
        }

        let interp = extract_mcmillan_interpolant(&partitioned);
        interpolants.push(interp);
    }

    Ok(InterpolationSequence {
        interpolants,
        state_vars: state_vars.clone(),
        depth: partitions.len(),
    })
}

/// Verify the interpolation sequence properties using brute-force enumeration
/// over all assignments to the state variables.
///
/// Checks:
/// 1. I_0 is implied by Init (every assignment satisfying Init also satisfies I_0)
/// 2. For each i: I_i AND T_i implies I_{i+1}
/// 3. I_k AND Bad is unsatisfiable (last interpolant excludes bad states)
/// 4. All interpolants only use state variables
#[must_use]
pub fn verify_sequence_properties(
    seq: &InterpolationSequence,
    init: &PropFormula,
    transitions: &[PropFormula],
    bad: &PropFormula,
) -> SequenceVerifyResult {
    // Property 4: state variable containment
    for (i, interp) in seq.interpolants.iter().enumerate() {
        for &v in &interp.variables() {
            if !seq.state_vars.contains(&v) {
                return SequenceVerifyResult::NonStateVariable { var: v, step: i };
            }
        }
    }

    // Enumerate all assignments over state variables
    let vars: Vec<u32> = seq.state_vars.iter().copied().collect();
    let num_assignments = 1u64 << vars.len();

    for bits in 0..num_assignments {
        let asgn = assignment_from_bits(&vars, bits);

        // Property 1: Init implies I_0
        if !seq.interpolants.is_empty()
            && init.evaluate(&asgn)
            && !seq.interpolants[0].evaluate(&asgn)
        {
            return SequenceVerifyResult::InitNotImplied;
        }

        // Property 2: I_i AND T_i implies I_{i+1}
        for i in 0..seq.interpolants.len().saturating_sub(1) {
            if i < transitions.len()
                && seq.interpolants[i].evaluate(&asgn)
                && transitions[i].evaluate(&asgn)
                && !seq.interpolants[i + 1].evaluate(&asgn)
            {
                return SequenceVerifyResult::TransitionGap { step: i };
            }
        }

        // Property 3: I_k AND Bad is unsatisfiable
        if let Some(last) = seq.interpolants.last() {
            if last.evaluate(&asgn) && bad.evaluate(&asgn) {
                return SequenceVerifyResult::BadNotExcluded;
            }
        }
    }

    SequenceVerifyResult::Valid
}

/// Check if a fixed point is reached at the given step.
///
/// A fixed point occurs when I_{step} implies I_{step+1} for all assignments,
/// meaning the interpolant sequence has converged to an inductive invariant.
///
/// Returns `false` if `step + 1` is out of bounds.
#[must_use]
pub fn check_fixed_point(seq: &InterpolationSequence, step: usize) -> bool {
    if step + 1 >= seq.interpolants.len() {
        return false;
    }

    let vars: Vec<u32> = seq.state_vars.iter().copied().collect();
    let num_assignments = 1u64 << vars.len();

    for bits in 0..num_assignments {
        let asgn = assignment_from_bits(&vars, bits);
        // Check I_{step} implies I_{step+1}
        if seq.interpolants[step].evaluate(&asgn) && !seq.interpolants[step + 1].evaluate(&asgn) {
            return false;
        }
    }

    true
}

/// Build a variable assignment from a bit pattern.
fn assignment_from_bits(vars: &[u32], bits: u64) -> HashMap<u32, bool> {
    vars.iter()
        .enumerate()
        .map(|(i, &v)| (v, (bits >> i) & 1 == 1))
        .collect()
}

/// I05: Sequence interpolation for BMC.
pub const I05_SEQUENCE_INTERPOLATION: ProofStatus = ProofStatus::DerivedPending;

/// I06: Fixed point detection (inductive invariant).
pub const I06_FIXED_POINT_DETECTION: ProofStatus = ProofStatus::DerivedPending;
