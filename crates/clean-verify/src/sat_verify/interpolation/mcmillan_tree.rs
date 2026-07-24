// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tree interpolation extensions for McMillan's algorithm.
//!
//! Provides tree interpolant extraction from proof DAGs, interpolant
//! strengthening/weakening, brute-force verification of Craig interpolation
//! properties, and formula analysis utilities.
//!
//! ## References
//!
//! - McMillan (2003): "Interpolation and SAT-Based Model Checking", CAV 2003.
//! - Pudlak (1997): "Lower bounds on the size of interpolants"

use super::PropFormula;
use std::collections::{HashMap, HashSet};

/// Classification of a proof DAG node for tree interpolation.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum NodeKind {
    /// An input clause from the original problem. The `usize` is the clause
    /// index into the original clause list used to determine A/B membership.
    Input(usize),
    /// A resolution step combining two child proofs on a pivot literal.
    Resolve {
        left: usize,
        right: usize,
        pivot: i32,
    },
}

/// Result of brute-force Craig interpolation property verification.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub struct InterpolantVerifyResult {
    /// Whether A implies I (every model of A satisfies I).
    pub a_implies_i: bool,
    /// Whether I AND B is unsatisfiable.
    pub i_and_b_unsat: bool,
    /// Whether all variables in I appear in both A and B.
    pub vars_shared: bool,
    /// Conjunction of all three properties.
    pub valid: bool,
}

/// Extract a tree interpolant from a proof DAG using McMillan's algorithm.
///
/// Each node in `proof_dag` is a pair of (clause literals, node kind).
/// `a_clause_indices` identifies which input clause indices belong to partition A.
/// `shared_vars` lists variables appearing in both A and B partitions.
///
/// For A-input nodes, the partial interpolant is the disjunction of shared-variable
/// literals. For B-input nodes, it is `True`. For resolution nodes:
/// - Shared pivot: Pudlak's rule `(p AND I_right) OR (NOT p AND I_left)`
/// - A-only pivot: `I_left OR I_right`
/// - B-only pivot: `I_left AND I_right`
#[must_use]
pub fn tree_interpolant(
    proof_dag: &[(Vec<i32>, NodeKind)],
    a_clause_indices: &[usize],
    shared_vars: &[u32],
) -> PropFormula {
    if proof_dag.is_empty() {
        return PropFormula::True;
    }

    let a_set: HashSet<usize> = a_clause_indices.iter().copied().collect();
    let shared_set: HashSet<u32> = shared_vars.iter().copied().collect();

    let mut interpolants: Vec<PropFormula> = Vec::with_capacity(proof_dag.len());

    for (clause, kind) in proof_dag {
        let interp = match kind {
            NodeKind::Input(clause_idx) => {
                if a_set.contains(clause_idx) {
                    // A-input: disjunction of shared-variable literals
                    shared_lit_disjunction(clause, &shared_set)
                } else {
                    PropFormula::True
                }
            }
            NodeKind::Resolve { left, right, pivot } => {
                let pvar = pivot.unsigned_abs();
                let i_left = interpolants[*left].clone();
                let i_right = interpolants[*right].clone();

                if shared_set.contains(&pvar) {
                    // Shared pivot: Pudlak's rule
                    let p = PropFormula::Var(pvar);
                    let not_p = PropFormula::Not(Box::new(p.clone()));
                    PropFormula::Or(
                        Box::new(PropFormula::AndType(Box::new(p), Box::new(i_right.clone()))),
                        Box::new(PropFormula::AndType(
                            Box::new(not_p),
                            Box::new(i_left.clone()),
                        )),
                    )
                } else if is_a_only_var(pvar, proof_dag, &a_set) {
                    // A-only pivot: disjunction
                    PropFormula::Or(Box::new(i_left), Box::new(i_right))
                } else {
                    // B-only pivot: conjunction
                    PropFormula::AndType(Box::new(i_left), Box::new(i_right))
                }
            }
        };
        interpolants.push(interp);
    }

    interpolants.pop().unwrap_or(PropFormula::True).simplify()
}

/// Strengthen an interpolant by conjoining with A-implied unit literals.
///
/// For each unit clause `[l]` in `a_clauses` whose variable appears in the
/// interpolant's variable set, conjoin the literal with the interpolant. This
/// produces a logically stronger (more restrictive) formula that is still
/// implied by A.
#[must_use]
pub fn strengthen_interpolant(interp: &PropFormula, a_clauses: &[Vec<i32>]) -> PropFormula {
    let interp_vars = interp.variables();
    let mut result = interp.clone();

    for clause in a_clauses {
        if clause.len() == 1 {
            let lit = clause[0];
            let var = lit.unsigned_abs();
            if interp_vars.contains(&var) {
                let lit_formula = lit_to_formula(lit);
                result = PropFormula::AndType(Box::new(result), Box::new(lit_formula));
            }
        }
    }

    result.simplify()
}

/// Weaken an interpolant by disjoining with B-contradicted unit literals.
///
/// For each unit clause `[l]` in `b_clauses` whose variable appears in the
/// interpolant's variable set, disjoin the negation of that literal with the
/// interpolant. This produces a logically weaker (more permissive) formula
/// that still makes I AND B unsatisfiable.
#[must_use]
pub fn weaken_interpolant(interp: &PropFormula, b_clauses: &[Vec<i32>]) -> PropFormula {
    let interp_vars = interp.variables();
    let mut result = interp.clone();

    for clause in b_clauses {
        if clause.len() == 1 {
            let lit = clause[0];
            let var = lit.unsigned_abs();
            if interp_vars.contains(&var) {
                // Disjoin with the negation of the B unit literal
                let neg_lit_formula = lit_to_formula(-lit);
                result = PropFormula::Or(Box::new(result), Box::new(neg_lit_formula));
            }
        }
    }

    result.simplify()
}

/// Brute-force verify all three Craig interpolation properties.
///
/// 1. A implies I: for every assignment satisfying all A-clauses, I is true.
/// 2. I AND B is unsatisfiable: no assignment satisfies both I and all B-clauses.
/// 3. Vars(I) is a subset of Vars(A) intersect Vars(B).
///
/// Enumerates all `2^num_vars` assignments. Only practical for small `num_vars`.
#[must_use]
pub fn verify_interpolant_property(
    interp: &PropFormula,
    a_clauses: &[Vec<i32>],
    b_clauses: &[Vec<i32>],
    num_vars: u32,
) -> InterpolantVerifyResult {
    let a_vars = collect_clause_vars(a_clauses);
    let b_vars = collect_clause_vars(b_clauses);
    let shared: HashSet<u32> = a_vars.intersection(&b_vars).copied().collect();

    let interp_vars = interp.variables();
    let vars_shared = interp_vars.iter().all(|v| shared.contains(v));

    let mut a_implies_i = true;
    let mut i_and_b_unsat = true;

    for bits in 0u64..(1u64 << num_vars) {
        let asgn = bits_to_assignment(bits, num_vars);

        let a_sat = clauses_satisfied(a_clauses, &asgn);
        let i_val = interp.evaluate(&asgn);
        let b_sat = clauses_satisfied(b_clauses, &asgn);

        if a_sat && !i_val {
            a_implies_i = false;
        }
        if i_val && b_sat {
            i_and_b_unsat = false;
        }
    }

    InterpolantVerifyResult {
        a_implies_i,
        i_and_b_unsat,
        vars_shared,
        valid: a_implies_i && i_and_b_unsat && vars_shared,
    }
}

/// Count the number of satisfying assignments for a propositional formula.
///
/// Enumerates all `2^num_vars` assignments. Variables are indexed 1..=num_vars.
#[must_use]
pub fn count_interpolant_models(interp: &PropFormula, num_vars: u32) -> u64 {
    let mut count = 0u64;
    for bits in 0u64..(1u64 << num_vars) {
        let asgn = bits_to_assignment(bits, num_vars);
        if interp.evaluate(&asgn) {
            count += 1;
        }
    }
    count
}

/// Count the number of nodes in a formula tree.
///
/// Each `Var`, `True`, and `False` is 1 node. `Not` adds 1 plus its child.
/// Binary connectives (`AndType`, `Or`, `Implies`) add 1 plus both children.
#[must_use]
pub fn interpolant_size(interp: &PropFormula) -> usize {
    match interp {
        PropFormula::Var(_) | PropFormula::True | PropFormula::False => 1,
        PropFormula::Not(inner) => 1 + interpolant_size(inner),
        PropFormula::AndType(l, r) | PropFormula::Or(l, r) | PropFormula::Implies(l, r) => {
            1 + interpolant_size(l) + interpolant_size(r)
        }
    }
}

// --- Internal helpers ---

/// Build a disjunction of shared-variable literals from a clause.
fn shared_lit_disjunction(clause: &[i32], shared: &HashSet<u32>) -> PropFormula {
    let shared_lits: Vec<PropFormula> = clause
        .iter()
        .filter(|&&lit| shared.contains(&lit.unsigned_abs()))
        .map(|&lit| lit_to_formula(lit))
        .collect();

    match shared_lits.len() {
        0 => PropFormula::False,
        1 => shared_lits
            .into_iter()
            .next()
            .expect("invariant: checked len"),
        _ => shared_lits
            .into_iter()
            .reduce(|a, b| PropFormula::Or(Box::new(a), Box::new(b)))
            .expect("invariant: non-empty"),
    }
}

/// Convert a DIMACS literal to a `PropFormula`.
fn lit_to_formula(lit: i32) -> PropFormula {
    let var = lit.unsigned_abs();
    if lit > 0 {
        PropFormula::Var(var)
    } else {
        PropFormula::Not(Box::new(PropFormula::Var(var)))
    }
}

/// Check whether a variable appears only in A-partition input clauses.
fn is_a_only_var(var: u32, proof_dag: &[(Vec<i32>, NodeKind)], a_set: &HashSet<usize>) -> bool {
    let mut in_a = false;
    let mut in_b = false;
    for (clause, kind) in proof_dag {
        if let NodeKind::Input(idx) = kind {
            let has_var = clause.iter().any(|&l| l.unsigned_abs() == var);
            if has_var {
                if a_set.contains(idx) {
                    in_a = true;
                } else {
                    in_b = true;
                }
            }
        }
    }
    in_a && !in_b
}

/// Collect all variables from a set of clauses.
fn collect_clause_vars(clauses: &[Vec<i32>]) -> HashSet<u32> {
    clauses
        .iter()
        .flat_map(|c| c.iter().map(|&l| l.unsigned_abs()))
        .collect()
}

/// Convert a bit pattern to a variable assignment (vars 1..=num_vars).
fn bits_to_assignment(bits: u64, num_vars: u32) -> HashMap<u32, bool> {
    let mut asgn = HashMap::new();
    for v in 1..=num_vars {
        asgn.insert(v, (bits >> (v - 1)) & 1 == 1);
    }
    asgn
}

/// Check whether all clauses are satisfied under an assignment.
fn clauses_satisfied(clauses: &[Vec<i32>], asgn: &HashMap<u32, bool>) -> bool {
    clauses.iter().all(|clause| {
        clause.iter().any(|&lit| {
            let var = lit.unsigned_abs();
            let val = asgn.get(&var).copied().unwrap_or(false);
            if lit > 0 {
                val
            } else {
                !val
            }
        })
    })
}
