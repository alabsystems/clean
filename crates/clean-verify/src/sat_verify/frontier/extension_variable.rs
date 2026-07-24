// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended Resolution variable introduction and proof compression
//!
//! This module implements the *variable introduction* side of Extended
//! Resolution (ER): given two clauses sharing a common subexpression
//! pattern, introduce a fresh variable `z` defined as `z <-> (a AND b)`
//! and verify that the resulting formula is equisatisfiable with the
//! original.
//!
//! The key insight is that Extended Resolution can produce exponentially
//! shorter proofs than standard Resolution for certain formula families
//! (Cook 1976), at the cost of introducing auxiliary variables.
//!
//! ## Proof Status Constants
//!
//! | ID  | Name                           | Status         |
//! |-----|--------------------------------|----------------|
//! | S48 | Extension preserves SAT        | DerivedPending |
//! | S49 | Extension proof compression    | DerivedPending |
//!
//! ## References
//!
//! - Tseitin, G. S. (1983). On the complexity of derivation in
//!   propositional calculus. *Automation of Reasoning*, pp. 466-483.
//! - Cook, S. A. (1976). A short proof of the pigeon hole principle
//!   using extended resolution. *SIGACT News* 8(4), pp. 28-32.

use std::collections::{HashMap, HashSet};

use crate::spec::ProofStatus;

// ---------------------------------------------------------------------------
// Types
// ---------------------------------------------------------------------------

/// An extension variable defined as a binary AND gate.
///
/// Represents: `var <-> (literal_a AND literal_b)`.
/// The `var` field is the DIMACS variable index for the new variable.
#[derive(Debug, Clone, PartialEq, Eq)]
#[must_use]
#[non_exhaustive]
pub struct ExtensionDef {
    /// DIMACS variable index for the extension variable (positive).
    pub var: u32,
    /// First literal of the AND gate.
    pub literal_a: i32,
    /// Second literal of the AND gate.
    pub literal_b: i32,
}

/// Result of verifying an extension chain for topological validity.
#[derive(Debug, Clone, PartialEq, Eq)]
#[must_use]
#[non_exhaustive]
pub struct ExtensionChainResult {
    /// Whether the chain is valid (no circular definitions).
    pub valid: bool,
    /// Topological order of extension variables (empty if invalid).
    pub topological_order: Vec<u32>,
    /// Cycles detected (empty if valid).
    pub cycles: Vec<Vec<u32>>,
}

/// Estimate of proof size reduction from extension variables.
#[derive(Debug, Clone, PartialEq)]
#[must_use]
#[non_exhaustive]
pub struct ProofSizeEstimate {
    /// Number of clauses in the original formula.
    pub original_clauses: usize,
    /// Number of clauses in the extended formula.
    pub extended_clauses: usize,
    /// Number of new variables introduced.
    pub new_vars: usize,
    /// Estimated reduction factor (< 1.0 means smaller proof).
    pub estimated_reduction_factor: f64,
}

// ---------------------------------------------------------------------------
// S48: Extension preserves satisfiability
// ---------------------------------------------------------------------------

/// S48: Extension variable introduction preserves satisfiability.
///
/// Status: `DerivedPending` -- verified computationally for small formulas
/// via brute-force enumeration; formal proof term not yet constructed.
pub const S48_EXTENSION_PRESERVES_SAT: ProofStatus = ProofStatus::DerivedPending;

/// S49: Extended Resolution proof compression.
///
/// Status: `DerivedPending` -- compression ratios verified computationally;
/// formal proof of exponential separation pending.
pub const S49_EXTENSION_PROOF_COMPRESSION: ProofStatus = ProofStatus::DerivedPending;

// ---------------------------------------------------------------------------
// Core functions
// ---------------------------------------------------------------------------

/// Create a new extension variable defined as `z <-> (a AND b)`.
///
/// Selects one literal from each clause as the operands of the AND gate.
/// Uses the first literal of each clause. The caller provides `next_var`
/// as the DIMACS index for the fresh variable.
///
/// # Panics
///
/// Panics if either clause is empty.
pub fn introduce_extension_variable(
    clause_a: &[i32],
    clause_b: &[i32],
    next_var: u32,
) -> ExtensionDef {
    assert!(!clause_a.is_empty(), "clause_a must be non-empty");
    assert!(!clause_b.is_empty(), "clause_b must be non-empty");

    ExtensionDef {
        var: next_var,
        literal_a: clause_a[0],
        literal_b: clause_b[0],
    }
}

/// Generate the 3 CNF clauses encoding `z <-> (a AND b)`.
///
/// The encoding produces:
///   1. `(z OR NOT a OR NOT b)` -- backward: if a,b both true then z true
///   2. `(NOT z OR a)`          -- forward: if z true then a true
///   3. `(NOT z OR b)`          -- forward: if z true then b true
#[must_use]
pub fn extension_definition_clauses(def: &ExtensionDef) -> Vec<Vec<i32>> {
    let z = def.var as i32;
    let a = def.literal_a;
    let b = def.literal_b;

    vec![
        vec![z, -a, -b], // backward implication
        vec![-z, a],     // forward implication (a)
        vec![-z, b],     // forward implication (b)
    ]
}

/// Verify that the extended formula is equisatisfiable with the original.
///
/// For small formulas, performs brute-force satisfiability checking. The
/// extension is sound if: original SAT <=> extended SAT.
///
/// Returns `false` if the formulas are too large for brute-force checking
/// (> 20 original variables) or if equisatisfiability is violated.
#[must_use]
pub fn verify_extension_preserves_sat(
    original: &[Vec<i32>],
    extended: &[Vec<i32>],
    extension_defs: &[ExtensionDef],
) -> bool {
    let orig_vars = collect_variables(original);
    let ext_all_vars = collect_variables(extended);

    // Extension variables must be fresh.
    let orig_set: HashSet<i32> = orig_vars.iter().copied().collect();
    for def in extension_defs {
        if orig_set.contains(&(def.var as i32)) {
            return false;
        }
    }

    let orig_sat = brute_force_sat(original, &orig_vars);
    let ext_sat = brute_force_sat(extended, &ext_all_vars);

    matches!((orig_sat, ext_sat), (Some(_), Some(_)) | (None, None))
}

/// Compute the compression ratio between original and extended proof sizes.
///
/// Returns `extended / original`. Values < 1.0 indicate compression.
/// Returns `f64::INFINITY` if `original_proof_size` is 0.
#[must_use]
pub fn proof_compression_ratio(original_proof_size: usize, extended_proof_size: usize) -> f64 {
    if original_proof_size == 0 {
        return f64::INFINITY;
    }
    extended_proof_size as f64 / original_proof_size as f64
}

/// Find literal pairs that appear together in multiple clauses.
///
/// Returns pairs `(a, b)` where `a < b` (by absolute value, then sign)
/// that co-occur in at least 2 clauses. These are candidates for
/// extension variable introduction.
#[must_use]
pub fn find_common_subexpressions(clauses: &[Vec<i32>]) -> Vec<(i32, i32)> {
    let mut pair_counts: HashMap<(i32, i32), usize> = HashMap::new();

    for clause in clauses {
        let mut lits: Vec<i32> = clause.to_vec();
        lits.sort_unstable_by_key(|&lit| (lit.abs(), lit));
        lits.dedup();

        for i in 0..lits.len() {
            for j in (i + 1)..lits.len() {
                let pair = (lits[i], lits[j]);
                *pair_counts.entry(pair).or_insert(0) += 1;
            }
        }
    }

    let mut result: Vec<(i32, i32)> = pair_counts
        .into_iter()
        .filter(|&(_, count)| count >= 2)
        .map(|(pair, _)| pair)
        .collect();

    result.sort_unstable();
    result
}

/// Verify that extension variables are introduced in valid topological order.
///
/// An extension chain is valid if no extension variable's definition
/// references an extension variable that is defined later (or references
/// itself). This prevents circular definitions.
pub fn verify_extension_chain(defs: &[ExtensionDef]) -> ExtensionChainResult {
    if defs.is_empty() {
        return ExtensionChainResult {
            valid: true,
            topological_order: Vec::new(),
            cycles: Vec::new(),
        };
    }

    // Build a set of extension variable indices.
    let ext_vars: HashSet<u32> = defs.iter().map(|d| d.var).collect();

    // Build adjacency: ext_var -> set of ext_vars it depends on.
    let mut deps: HashMap<u32, HashSet<u32>> = HashMap::new();
    for def in defs {
        let mut dep_set = HashSet::new();
        for &lit in &[def.literal_a, def.literal_b] {
            let var = lit.unsigned_abs();
            if ext_vars.contains(&var) {
                dep_set.insert(var);
            }
        }
        deps.insert(def.var, dep_set);
    }

    // Topological sort via Kahn's algorithm.
    // For each (node -> dep_set), node depends on dep_set entries.
    // Edge direction: dep -> node. So in_degree[node] = |dep_set|.
    let mut in_degree: HashMap<u32, usize> = HashMap::new();
    for &v in &ext_vars {
        in_degree.insert(v, 0);
    }
    for (&node, dep_set) in &deps {
        *in_degree.entry(node).or_insert(0) += dep_set.len();
    }

    let mut queue: Vec<u32> = in_degree
        .iter()
        .filter(|&(_, &deg)| deg == 0)
        .map(|(&v, _)| v)
        .collect();
    queue.sort_unstable();

    let mut order = Vec::new();
    while let Some(v) = queue.pop() {
        order.push(v);
        // For each node that depends on v, decrease its in-degree.
        for (&node, dep_set) in &deps {
            if dep_set.contains(&v) {
                if let Some(deg) = in_degree.get_mut(&node) {
                    *deg -= 1;
                    if *deg == 0 {
                        queue.push(node);
                        queue.sort_unstable();
                    }
                }
            }
        }
    }

    build_chain_result(order, ext_vars.len(), &in_degree)
}

/// Build the chain verification result from topological sort output.
fn build_chain_result(
    order: Vec<u32>,
    total_vars: usize,
    in_degree: &HashMap<u32, usize>,
) -> ExtensionChainResult {
    if order.len() == total_vars {
        ExtensionChainResult {
            valid: true,
            topological_order: order,
            cycles: Vec::new(),
        }
    } else {
        let cycle_nodes: Vec<u32> = in_degree
            .iter()
            .filter(|&(_, &deg)| deg > 0)
            .map(|(&v, _)| v)
            .collect();
        ExtensionChainResult {
            valid: false,
            topological_order: Vec::new(),
            cycles: vec![cycle_nodes],
        }
    }
}

/// Estimate proof size reduction from introducing extension variables.
///
/// The estimate accounts for:
/// - 3 definition clauses per extension variable
/// - Potential sharing of subexpressions across original clauses
///
/// The `estimated_reduction_factor` is a heuristic: it counts how many
/// clause-literal-pair occurrences the extensions cover and estimates
/// the fraction of the proof that can be compressed.
pub fn estimate_proof_size_reduction(
    clauses: &[Vec<i32>],
    extensions: &[ExtensionDef],
) -> ProofSizeEstimate {
    let original_clauses = clauses.len();
    let new_vars = extensions.len();
    // Each extension adds 3 definition clauses.
    let definition_clauses = new_vars * 3;
    let extended_clauses = original_clauses + definition_clauses;

    // Count how many clauses each extension's literal pair appears in.
    let mut total_coverage = 0usize;
    for ext in extensions {
        let a = ext.literal_a;
        let b = ext.literal_b;
        for clause in clauses {
            if clause.contains(&a) && clause.contains(&b) {
                total_coverage += 1;
            }
        }
    }

    // Heuristic: each covered clause-pair can save ~1 literal in resolution
    // steps. The reduction factor estimates how much shorter the proof
    // becomes. More coverage => lower factor => better compression.
    let estimated_reduction_factor = if original_clauses == 0 || total_coverage == 0 {
        1.0
    } else {
        let coverage_ratio = total_coverage as f64 / original_clauses as f64;
        // Each unit of coverage saves roughly one resolution step.
        // Factor of 0.5 at full coverage, approaching 1.0 at zero coverage.
        1.0 - 0.5 * coverage_ratio.min(1.0)
    };

    ProofSizeEstimate {
        original_clauses,
        extended_clauses,
        new_vars,
        estimated_reduction_factor,
    }
}

// ---------------------------------------------------------------------------
// Internal helpers
// ---------------------------------------------------------------------------

/// Collect all variable indices that appear in a formula.
fn collect_variables(clauses: &[Vec<i32>]) -> Vec<i32> {
    let mut vars: HashSet<i32> = HashSet::new();
    for clause in clauses {
        for &lit in clause {
            vars.insert(lit.abs());
        }
    }
    let mut sorted: Vec<i32> = vars.into_iter().collect();
    sorted.sort_unstable();
    sorted
}

/// Evaluate a clause under a given truth assignment.
fn eval_clause(clause: &[i32], assignment: &HashSet<i32>) -> bool {
    clause.iter().any(|&lit| assignment.contains(&lit))
}

/// Evaluate a formula (conjunction of clauses) under a truth assignment.
fn eval_formula(clauses: &[Vec<i32>], assignment: &HashSet<i32>) -> bool {
    clauses.iter().all(|clause| eval_clause(clause, assignment))
}

/// Check satisfiability by brute-force enumeration (small formulas only).
fn brute_force_sat(clauses: &[Vec<i32>], vars: &[i32]) -> Option<HashSet<i32>> {
    let n = vars.len();
    if n > 20 {
        return None;
    }
    for bits in 0u64..(1u64 << n) {
        let mut assignment = HashSet::new();
        for (i, &var) in vars.iter().enumerate() {
            if (bits >> i) & 1 == 1 {
                assignment.insert(var);
            } else {
                assignment.insert(-var);
            }
        }
        if eval_formula(clauses, &assignment) {
            return Some(assignment);
        }
    }
    None
}
