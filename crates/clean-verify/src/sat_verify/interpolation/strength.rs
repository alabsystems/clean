// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Interpolation Strength Metrics and Comparison
//!
//! Provides quality metrics for comparing interpolants: size, depth,
//! variable counts, relative strength testing, and basic simplification.
//!
//! Strength is defined semantically: interpolant A is stronger than B
//! when A implies B (fewer satisfying assignments). The brute-force
//! implication check is only practical for formulas with a small number
//! of shared variables.

use super::PropFormula;
use crate::spec::ProofStatus;
use std::collections::{BTreeSet, HashMap};

/// I09: Interpolant strength comparison and metrics.
pub const I09_INTERPOLANT_STRENGTH: ProofStatus = ProofStatus::DerivedPending;

/// Comparison result between two interpolants.
#[derive(Debug, Clone, PartialEq)]
pub struct InterpolantComparison {
    /// Ratio of candidate size to reference size (< 1.0 means candidate is smaller).
    pub size_ratio: f64,
    /// Ratio of candidate depth to reference depth.
    pub depth_ratio: f64,
    /// Ratio of candidate variable count to reference variable count.
    pub var_count_ratio: f64,
    /// Whether the candidate is structurally simpler (smaller size and depth).
    pub is_simpler: bool,
}

/// Count the number of nodes in a formula tree.
///
/// Each `Var`, `True`, and `False` counts as 1 node. Unary connectives
/// (`Not`) add 1 plus the child. Binary connectives (`AndType`, `Or`, `Implies`)
/// add 1 plus both children.
#[must_use]
pub fn interpolant_size(formula: &PropFormula) -> usize {
    match formula {
        PropFormula::Var(_) | PropFormula::True | PropFormula::False => 1,
        PropFormula::Not(inner) => 1 + interpolant_size(inner),
        PropFormula::AndType(l, r) | PropFormula::Or(l, r) | PropFormula::Implies(l, r) => {
            1 + interpolant_size(l) + interpolant_size(r)
        }
    }
}

/// Compute the maximum nesting depth of a formula.
///
/// Atoms (`Var`, `True`, `False`) have depth 0. Each connective adds 1.
#[must_use]
pub fn interpolant_depth(formula: &PropFormula) -> usize {
    match formula {
        PropFormula::Var(_) | PropFormula::True | PropFormula::False => 0,
        PropFormula::Not(inner) => 1 + interpolant_depth(inner),
        PropFormula::AndType(l, r) | PropFormula::Or(l, r) | PropFormula::Implies(l, r) => {
            1 + interpolant_depth(l).max(interpolant_depth(r))
        }
    }
}

/// Collect the unique variable indices appearing in a formula, sorted.
#[must_use]
pub fn interpolant_variables(formula: &PropFormula) -> Vec<usize> {
    let mut vars = BTreeSet::new();
    collect_vars(formula, &mut vars);
    vars.into_iter().collect()
}

/// Recursively collect variable indices from a formula.
fn collect_vars(formula: &PropFormula, vars: &mut BTreeSet<usize>) {
    match formula {
        PropFormula::Var(v) => {
            vars.insert(*v as usize);
        }
        PropFormula::Not(inner) => collect_vars(inner, vars),
        PropFormula::AndType(l, r) | PropFormula::Or(l, r) | PropFormula::Implies(l, r) => {
            collect_vars(l, vars);
            collect_vars(r, vars);
        }
        PropFormula::True | PropFormula::False => {}
    }
}

/// Compare two interpolants on structural metrics.
///
/// Returns an `InterpolantComparison` describing the relative size, depth,
/// and variable count of `a` versus `b`. Ratios are `a / b`; a ratio below
/// 1.0 means `a` is smaller/shallower.
#[must_use]
pub fn compare_interpolants(a: &PropFormula, b: &PropFormula) -> InterpolantComparison {
    let size_a = interpolant_size(a);
    let size_b = interpolant_size(b);
    let depth_a = interpolant_depth(a);
    let depth_b = interpolant_depth(b);
    let vars_a = interpolant_variables(a).len();
    let vars_b = interpolant_variables(b).len();

    let size_ratio = safe_ratio(size_a, size_b);
    let depth_ratio = safe_ratio(depth_a, depth_b);
    let var_count_ratio = safe_ratio(vars_a, vars_b);

    let is_simpler = size_a < size_b && depth_a <= depth_b;

    InterpolantComparison {
        size_ratio,
        depth_ratio,
        var_count_ratio,
        is_simpler,
    }
}

/// Compute the ratio `a / b`, returning 1.0 when `b` is zero.
fn safe_ratio(a: usize, b: usize) -> f64 {
    if b == 0 {
        if a == 0 {
            1.0
        } else {
            f64::INFINITY
        }
    } else {
        a as f64 / b as f64
    }
}

/// Check whether `candidate` is a stronger interpolant than `reference`
/// over the given shared variables.
///
/// "Stronger" means: for every assignment to `shared_vars`, if `candidate`
/// is true then `reference` is also true (candidate implies reference).
/// A stronger interpolant is more restrictive (fewer satisfying assignments).
///
/// Uses brute-force enumeration; only practical for `shared_vars.len() <= 20`.
#[must_use]
pub fn is_stronger_interpolant(
    candidate: &PropFormula,
    reference: &PropFormula,
    shared_vars: &[usize],
) -> bool {
    let num_vars = shared_vars.len();
    if num_vars > 20 {
        return false;
    }
    let total = 1u64 << num_vars;

    for bits in 0..total {
        let asgn = build_assignment(shared_vars, bits);
        let cand_val = candidate.evaluate(&asgn);
        let ref_val = reference.evaluate(&asgn);
        // candidate implies reference: whenever candidate is true, reference must be true
        if cand_val && !ref_val {
            return false;
        }
    }
    true
}

/// Build a variable assignment mapping from a bit pattern.
fn build_assignment(vars: &[usize], bits: u64) -> HashMap<u32, bool> {
    vars.iter()
        .enumerate()
        .map(|(i, &v)| (v as u32, (bits >> i) & 1 == 1))
        .collect()
}

/// Apply basic simplification rules to an interpolant formula.
///
/// Simplification rules applied (bottom-up):
/// - Double negation elimination: `NOT (NOT p)` -> `p`
/// - Identity laws: `p AND True` -> `p`, `p OR False` -> `p`
/// - Annihilation: `p AND False` -> `False`, `p OR True` -> `True`
/// - Implication with constants: `False -> p` -> `True`, `True -> p` -> `p`
/// - Absorption: `p AND p` -> `p`, `p OR p` -> `p`
/// - Complementation: `p AND (NOT p)` -> `False`, `p OR (NOT p)` -> `True`
#[must_use]
pub fn simplify_interpolant(formula: &PropFormula) -> PropFormula {
    match formula {
        PropFormula::Var(_) | PropFormula::True | PropFormula::False => formula.clone(),
        PropFormula::Not(inner) => simplify_not(inner),
        PropFormula::AndType(l, r) => simplify_and(l, r),
        PropFormula::Or(l, r) => simplify_or(l, r),
        PropFormula::Implies(l, r) => simplify_implies(l, r),
    }
}

/// Simplify a negation node.
fn simplify_not(inner: &PropFormula) -> PropFormula {
    let s = simplify_interpolant(inner);
    match s {
        PropFormula::True => PropFormula::False,
        PropFormula::False => PropFormula::True,
        PropFormula::Not(x) => *x,
        other => PropFormula::Not(Box::new(other)),
    }
}

/// Simplify a conjunction node.
fn simplify_and(l: &PropFormula, r: &PropFormula) -> PropFormula {
    let sl = simplify_interpolant(l);
    let sr = simplify_interpolant(r);
    match (&sl, &sr) {
        (PropFormula::True, _) => sr,
        (_, PropFormula::True) => sl,
        (PropFormula::False, _) | (_, PropFormula::False) => PropFormula::False,
        _ if sl == sr => sl,
        _ if is_negation_of(&sl, &sr) => PropFormula::False,
        _ => PropFormula::AndType(Box::new(sl), Box::new(sr)),
    }
}

/// Simplify a disjunction node.
fn simplify_or(l: &PropFormula, r: &PropFormula) -> PropFormula {
    let sl = simplify_interpolant(l);
    let sr = simplify_interpolant(r);
    match (&sl, &sr) {
        (PropFormula::False, _) => sr,
        (_, PropFormula::False) => sl,
        (PropFormula::True, _) | (_, PropFormula::True) => PropFormula::True,
        _ if sl == sr => sl,
        _ if is_negation_of(&sl, &sr) => PropFormula::True,
        _ => PropFormula::Or(Box::new(sl), Box::new(sr)),
    }
}

/// Simplify an implication node.
fn simplify_implies(l: &PropFormula, r: &PropFormula) -> PropFormula {
    let sl = simplify_interpolant(l);
    let sr = simplify_interpolant(r);
    match (&sl, &sr) {
        (PropFormula::False, _) | (_, PropFormula::True) => PropFormula::True,
        (PropFormula::True, _) => sr,
        _ if sl == sr => PropFormula::True,
        _ => PropFormula::Implies(Box::new(sl), Box::new(sr)),
    }
}

/// Check whether `a` is the negation of `b` (or vice versa).
fn is_negation_of(a: &PropFormula, b: &PropFormula) -> bool {
    match (a, b) {
        (PropFormula::Not(inner), other) | (other, PropFormula::Not(inner)) => {
            inner.as_ref() == other
        }
        _ => false,
    }
}
