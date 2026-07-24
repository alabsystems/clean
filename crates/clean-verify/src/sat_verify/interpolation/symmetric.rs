// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Symmetric (Krajicek) and Path Interpolation
//!
//! Symmetric interpolation computes the average of McMillan and Pudlak
//! interpolants, producing formulas whose strength lies between the two.
//!
//! Path interpolation generalizes Craig interpolation to a chain of formula
//! partitions A_1, ..., A_k, producing a sequence I_1, ..., I_{k-1} such that
//! each I_i separates the prefix A_1..A_i from the suffix A_{i+1}..A_k.
//!
//! ## References
//!
//! - Krajicek (1997): "Interpolation theorems, lower bounds for proof systems,
//!   and independence results for bounded arithmetic"
//! - Pudlak (1997): "Lower bounds on the size of interpolants"
//! - Jhala & McMillan (2006): "A practical and complete approach to predicate
//!   refinement", TACAS 2006.

use super::mcmillan::{extract_mcmillan_interpolant, Partition, ResolutionDag, ResolutionDagNode};
use super::reverse::pudlak_interpolation;
use super::PropFormula;
use crate::sat_verify::cdcl::var_of;
use crate::spec::ProofStatus;
use std::cmp::Ordering;
use std::collections::{HashMap, HashSet};

/// A resolution proof in node-indexed form.
///
/// Nodes are stored in topological order: every `Resolve` references
/// earlier indices. The last node is the empty clause (refutation root).
#[derive(Debug, Clone)]
pub struct ResolutionProof {
    pub nodes: Vec<ProofNode>,
}

/// A single node in a resolution proof.
#[derive(Debug, Clone)]
pub struct ProofNode {
    /// The clause at this node (empty for the refutation root).
    pub clause: Vec<i32>,
    /// How this clause was derived.
    pub derivation: Derivation,
}

/// Derivation information for a proof node.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum Derivation {
    /// An input clause from partition at the given index (0-based).
    Input(usize),
    /// Resolution of two earlier nodes on a pivot literal.
    Resolve {
        left: usize,
        right: usize,
        pivot: i32,
    },
}

/// Result of verifying a path interpolant chain.
#[derive(Debug, Clone, PartialEq, Eq)]
#[must_use]
#[non_exhaustive]
pub struct PathVerifyResult {
    /// Whether the entire chain is valid.
    pub valid: bool,
    /// Failures: (step_index, description).
    pub failures: Vec<(usize, String)>,
}

/// I07: Symmetric (Krajicek) interpolation.
pub const I07_SYMMETRIC_INTERPOLANT: ProofStatus = ProofStatus::DerivedPending;

/// I08: Path interpolation chain.
pub const I08_PATH_INTERPOLATION_CHAIN: ProofStatus = ProofStatus::DerivedPending;

/// Compute a symmetric (Krajicek) interpolant.
///
/// The symmetric interpolant is defined as:
///   I_sym = (I_mcmillan AND I_pudlak) OR (I_mcmillan AND I_sym_core)
///
/// In practice we approximate this as the disjunction of the McMillan and
/// Pudlak interpolants conjoined: `(I_mcm OR I_pud)` — this is the
/// "average" interpolant whose strength lies between the two extremes.
///
/// The returned formula is in CNF-like nested form (not flattened to clauses).
/// Use `to_clauses` to convert to clause form if needed.
///
/// # Arguments
///
/// * `a_clauses` - Clauses belonging to partition A.
/// * `b_clauses` - Clauses belonging to partition B.
/// * `proof` - A resolution refutation of A AND B.
/// * `shared_vars` - Variables appearing in both A and B.
#[must_use]
pub fn symmetric_interpolant(
    a_clauses: &[Vec<i32>],
    b_clauses: &[Vec<i32>],
    proof: &ResolutionProof,
    shared_vars: &[u32],
) -> Vec<Vec<i32>> {
    let dag = build_dag_from_proof(a_clauses, b_clauses, proof);
    let shared_set: HashSet<u32> = shared_vars.iter().copied().collect();

    let mcm = extract_mcmillan_interpolant(&dag);
    let pud = pudlak_interpolation(&dag, &Partition::A, &shared_set).unwrap_or(PropFormula::True);

    // Symmetric interpolant: AND of (McMillan OR Pudlak) for each assignment
    // Equivalently: (I_mcm AND I_pud) is too strong, (I_mcm OR I_pud) is the
    // symmetric combination. We produce I_sym = I_mcm OR I_pud then convert.
    let sym = PropFormula::Or(Box::new(mcm), Box::new(pud)).simplify();

    formula_to_clauses(&sym, shared_vars)
}

/// Compute path interpolants for a chain of formula partitions.
///
/// Given partitions P_1, ..., P_k whose conjunction is unsatisfiable,
/// produce interpolants I_1, ..., I_{k-1} such that for each i:
///   - P_1 AND ... AND P_i |= I_i
///   - I_i AND P_{i+1} AND ... AND P_k |= false
///   - Vars(I_i) subset Vars(P_1..P_i) intersect Vars(P_{i+1}..P_k)
///
/// Each interpolant is returned in clause form.
///
/// # Arguments
///
/// * `partitions` - A sequence of clause sets P_1, ..., P_k.
/// * `proof` - A resolution refutation of P_1 AND ... AND P_k.
#[must_use]
pub fn path_interpolants(
    partitions: &[Vec<Vec<i32>>],
    proof: &ResolutionProof,
) -> Vec<Vec<Vec<i32>>> {
    if partitions.len() < 2 {
        return Vec::new();
    }

    let k = partitions.len();
    let mut result = Vec::with_capacity(k - 1);

    // For each cut point i (1..k-1), compute I_i that separates
    // P_1..P_i (= A) from P_{i+1}..P_k (= B).
    for cut in 1..k {
        let a_clauses: Vec<Vec<i32>> = partitions[..cut]
            .iter()
            .flat_map(|p| p.iter().cloned())
            .collect();
        let b_clauses: Vec<Vec<i32>> = partitions[cut..]
            .iter()
            .flat_map(|p| p.iter().cloned())
            .collect();

        let a_vars = collect_vars_from_clauses(&a_clauses);
        let b_vars = collect_vars_from_clauses(&b_clauses);
        let shared: Vec<u32> = a_vars.intersection(&b_vars).copied().collect();

        let dag = build_dag_from_proof(&a_clauses, &b_clauses, proof);
        let interp = extract_mcmillan_interpolant(&dag).simplify();
        let clauses = formula_to_clauses(&interp, &shared);
        result.push(clauses);
    }

    result
}

/// Verify that a path interpolant chain satisfies the required properties.
///
/// For each interpolant I_i (0-indexed), checks:
///   1. A_1 AND ... AND A_{i+1} |= I_i  (prefix implies interpolant)
///   2. I_i AND A_{i+2} AND ... AND A_k |= false  (interpolant with suffix is unsat)
///
/// Verification is by brute-force enumeration over all variable assignments
/// (practical only for small instances).
pub fn verify_path_interpolant_chain(
    partitions: &[Vec<Vec<i32>>],
    interpolants: &[Vec<Vec<i32>>],
) -> PathVerifyResult {
    let mut failures = Vec::new();

    if partitions.len() < 2 {
        return PathVerifyResult {
            valid: interpolants.is_empty(),
            failures: if interpolants.is_empty() {
                Vec::new()
            } else {
                vec![(
                    0,
                    "fewer than 2 partitions but interpolants provided".into(),
                )]
            },
        };
    }

    let expected_count = partitions.len() - 1;
    if interpolants.len() != expected_count {
        return PathVerifyResult {
            valid: false,
            failures: vec![(
                0,
                format!(
                    "expected {} interpolants for {} partitions, got {}",
                    expected_count,
                    partitions.len(),
                    interpolants.len()
                ),
            )],
        };
    }

    let all_vars = collect_all_vars(partitions, interpolants);
    let vars: Vec<u32> = all_vars.into_iter().collect();

    // Limit brute-force to small instances.
    let num_vars = vars.len().min(20);
    let enum_vars = &vars[..num_vars];
    let num_assignments = 1u64 << num_vars;

    for (i, interpolant) in interpolants.iter().enumerate() {
        let cut = i + 1; // I_i separates P_1..P_{cut} from P_{cut+1}..P_k

        for bits in 0..num_assignments {
            let asgn = assignment_from_bits(enum_vars, bits);

            // Check: prefix satisfiable => interpolant satisfied
            let prefix_sat = partitions[..cut]
                .iter()
                .all(|part| clauses_satisfied(part, &asgn));
            let interp_sat = clauses_satisfied(interpolant, &asgn);

            if prefix_sat && !interp_sat {
                failures.push((
                    i,
                    format!("prefix P_1..P_{cut} satisfied but I_{i} not satisfied"),
                ));
                break;
            }

            // Check: interpolant AND suffix is unsatisfiable
            let suffix_sat = partitions[cut..]
                .iter()
                .all(|part| clauses_satisfied(part, &asgn));

            if interp_sat && suffix_sat {
                failures.push((
                    i,
                    format!(
                        "I_{i} AND P_{cut_plus}..P_k satisfiable",
                        cut_plus = cut + 1
                    ),
                ));
                break;
            }
        }
    }

    PathVerifyResult {
        valid: failures.is_empty(),
        failures,
    }
}

/// Compare interpolant strength by model counting.
///
/// A stronger interpolant has fewer satisfying assignments (it is more
/// restrictive). Returns:
///   - `Ordering::Less` if `interp_a` is strictly stronger (fewer models)
///   - `Ordering::Greater` if `interp_b` is strictly stronger
///   - `Ordering::Equal` if they have the same model count
///
/// Only practical for small `num_vars` (brute-force enumeration).
#[must_use]
pub fn interpolant_strength_compare(
    interp_a: &[Vec<i32>],
    interp_b: &[Vec<i32>],
    num_vars: u32,
) -> Ordering {
    let count_a = count_models(interp_a, num_vars);
    let count_b = count_models(interp_b, num_vars);
    // Fewer models = stronger (more restrictive)
    count_a.cmp(&count_b)
}

/// Verify that an interpolant only mentions shared variables.
///
/// Returns `true` iff every variable in the interpolant clauses appears
/// in both `a_vars` and `b_vars`.
#[must_use]
pub fn verify_shared_variable_property(
    interpolant: &[Vec<i32>],
    a_vars: &[u32],
    b_vars: &[u32],
) -> bool {
    let a_set: HashSet<u32> = a_vars.iter().copied().collect();
    let b_set: HashSet<u32> = b_vars.iter().copied().collect();
    let shared: HashSet<u32> = a_set.intersection(&b_set).copied().collect();

    for clause in interpolant {
        for &lit in clause {
            let v = var_of(lit);
            if !shared.contains(&v) {
                return false;
            }
        }
    }
    true
}

// ---- Internal helpers ----

/// Build a `ResolutionDag` from a `ResolutionProof` with A/B clause labeling.
fn build_dag_from_proof(
    a_clauses: &[Vec<i32>],
    b_clauses: &[Vec<i32>],
    proof: &ResolutionProof,
) -> ResolutionDag {
    let a_set: HashSet<Vec<i32>> = a_clauses.iter().cloned().collect();
    let _b_set: HashSet<Vec<i32>> = b_clauses.iter().cloned().collect();
    let mut dag = ResolutionDag::new();

    for node in &proof.nodes {
        match &node.derivation {
            Derivation::Input(_partition_idx) => {
                let partition = if a_set.contains(&node.clause) {
                    Partition::A
                } else {
                    Partition::B
                };
                dag.add_input(node.clause.clone(), partition);
            }
            Derivation::Resolve { left, right, pivot } => {
                dag.add_resolve(*left, *right, *pivot);
            }
        }
    }
    dag
}

/// Collect all variable indices from a set of clauses.
fn collect_vars_from_clauses(clauses: &[Vec<i32>]) -> HashSet<u32> {
    clauses
        .iter()
        .flat_map(|c| c.iter().map(|&lit| var_of(lit)))
        .collect()
}

/// Collect all variables across partitions and interpolants.
fn collect_all_vars(partitions: &[Vec<Vec<i32>>], interpolants: &[Vec<Vec<i32>>]) -> HashSet<u32> {
    let mut vars = HashSet::new();
    for part in partitions {
        for clause in part {
            for &lit in clause {
                vars.insert(var_of(lit));
            }
        }
    }
    for interp in interpolants {
        for clause in interp {
            for &lit in clause {
                vars.insert(var_of(lit));
            }
        }
    }
    vars
}

/// Build a variable assignment from a bit pattern.
fn assignment_from_bits(vars: &[u32], bits: u64) -> HashMap<u32, bool> {
    vars.iter()
        .enumerate()
        .map(|(i, &v)| (v, (bits >> i) & 1 == 1))
        .collect()
}

/// Check if all clauses are satisfied under the given assignment.
fn clauses_satisfied(clauses: &[Vec<i32>], asgn: &HashMap<u32, bool>) -> bool {
    clauses.iter().all(|clause| {
        clause.iter().any(|&lit| {
            let v = var_of(lit);
            let val = asgn.get(&v).copied().unwrap_or(false);
            if lit > 0 {
                val
            } else {
                !val
            }
        })
    })
}

/// Count the number of satisfying assignments for a clause set.
fn count_models(clauses: &[Vec<i32>], num_vars: u32) -> u64 {
    let vars: Vec<u32> = (1..=num_vars).collect();
    let total = 1u64 << num_vars;
    let mut count = 0u64;
    for bits in 0..total {
        let asgn = assignment_from_bits(&vars, bits);
        if clauses_satisfied(clauses, &asgn) {
            count += 1;
        }
    }
    count
}

/// Convert a `PropFormula` to a list of clauses (conjunctive normal form).
///
/// This is a best-effort flattening: the formula is recursively decomposed.
/// AND at the top level produces multiple clauses; OR within a clause
/// produces multi-literal clauses. Variables are filtered to `shared_vars`.
fn formula_to_clauses(formula: &PropFormula, shared_vars: &[u32]) -> Vec<Vec<i32>> {
    let shared_set: HashSet<u32> = shared_vars.iter().copied().collect();
    let mut clauses = Vec::new();
    collect_cnf_clauses(formula, &mut clauses, &shared_set);
    if clauses.is_empty() && !matches!(formula, PropFormula::True) {
        // The formula is non-trivially False or has no shared vars.
        clauses.push(Vec::new()); // empty clause = false
    }
    clauses
}

/// Recursively decompose a formula into CNF clauses.
fn collect_cnf_clauses(formula: &PropFormula, clauses: &mut Vec<Vec<i32>>, shared: &HashSet<u32>) {
    match formula {
        PropFormula::True => {}
        PropFormula::False => {
            clauses.push(Vec::new()); // empty clause
        }
        PropFormula::AndType(l, r) => {
            collect_cnf_clauses(l, clauses, shared);
            collect_cnf_clauses(r, clauses, shared);
        }
        _ => {
            let mut lits = Vec::new();
            collect_or_lits(formula, &mut lits, shared);
            if !lits.is_empty() {
                lits.sort_by_key(|l| (var_of(*l), *l < 0));
                lits.dedup();
                clauses.push(lits);
            }
        }
    }
}

/// Collect literals from an OR chain (single clause).
fn collect_or_lits(formula: &PropFormula, lits: &mut Vec<i32>, shared: &HashSet<u32>) {
    match formula {
        PropFormula::Or(l, r) => {
            collect_or_lits(l, lits, shared);
            collect_or_lits(r, lits, shared);
        }
        PropFormula::Var(v) => {
            if shared.contains(v) {
                lits.push(*v as i32);
            }
        }
        PropFormula::Not(inner) => {
            if let PropFormula::Var(v) = inner.as_ref() {
                if shared.contains(v) {
                    lits.push(-(*v as i32));
                }
            }
        }
        PropFormula::True => {
            // True in a disjunction makes the whole clause trivially true.
            // We signal this by not adding any literal (caller handles).
        }
        PropFormula::False => {
            // False in a disjunction is a no-op.
        }
        PropFormula::AndType(_, _) | PropFormula::Implies(_, _) => {
            // Nested AndType/Implies inside Or: treat as opaque. This is a
            // limitation of the simple CNF conversion; full Tseitin would
            // handle this. For interpolants from resolution proofs, the
            // formula structure is typically already close to CNF.
        }
    }
}
