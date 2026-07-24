// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended Resolution (ER) -- S40: `extension_rule_sound`
//!
//! Extended Resolution augments standard resolution by allowing the
//! introduction of new "extension" variables, each defined as a function
//! of existing variables. The key soundness property (S40) is that
//! adding extension definitions preserves satisfiability:
//!
//!   F is satisfiable  <=>  F ^ Def(z1) ^ ... ^ Def(zk) is satisfiable
//!
//! where Def(z) encodes z <-> f(x1,...,xn) as CNF clauses.
//!
//! ## Representation
//!
//! Variables are signed integers (DIMACS convention): positive = true,
//! negative = negation. Clauses are disjunctions represented as `Vec<i32>`.
//!
//! An extension variable z defined as z <-> (x1 AND x2 AND ... AND xn)
//! is encoded as the CNF clauses:
//!   (z OR NOT x1 OR NOT x2 OR ... OR NOT xn)   -- backward implication
//!   (NOT z OR x1)                                -- forward implication
//!   (NOT z OR x2)
//!   ...
//!   (NOT z OR xn)
//!
//! ## References
//!
//! - Tseitin, G. S. (1983). On the complexity of derivation in
//!   propositional calculus. *Automation of Reasoning*, pp. 466-483.
//! - Cook, S. A. (1976). A short proof of the pigeon hole principle
//!   using extended resolution. *SIGACT News* 8(4), pp. 28-32.

use std::collections::HashSet;

/// An extension variable defined as a conjunction of existing literals.
///
/// Represents: `name <-> (definition[0] AND definition[1] AND ...)`.
/// The `name` field is the DIMACS variable index for the new variable.
/// The `definition` field contains the literals whose conjunction defines it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExtensionVariable {
    /// DIMACS variable index for the new variable (must be positive).
    pub name: i32,
    /// Literals whose conjunction defines this variable.
    pub definition: Vec<i32>,
}

/// Encode an extension variable definition as CNF clauses.
///
/// For z <-> (l1 AND l2 AND ... AND lk):
///   Clause 1: (z OR NOT l1 OR NOT l2 OR ... OR NOT lk)
///   Clause 2..k+1: (NOT z OR li) for each li
#[must_use]
fn extension_to_clauses(ext: &ExtensionVariable) -> Vec<Vec<i32>> {
    let z = ext.name;
    let mut clauses = Vec::with_capacity(ext.definition.len() + 1);

    // Backward: if all definition lits are true, z must be true.
    // (z OR NOT l1 OR NOT l2 OR ... OR NOT lk)
    let mut backward = Vec::with_capacity(ext.definition.len() + 1);
    backward.push(z);
    for &lit in &ext.definition {
        backward.push(-lit);
    }
    clauses.push(backward);

    // Forward: if z is true, each definition lit must be true.
    // (NOT z OR li) for each li
    for &lit in &ext.definition {
        clauses.push(vec![-z, lit]);
    }

    clauses
}

/// Add extension variable definitions as clauses to a formula.
///
/// Returns a new formula consisting of the original clauses plus the
/// CNF encoding of each extension variable definition.
#[must_use]
pub fn apply_extension(clauses: &[Vec<i32>], extensions: &[ExtensionVariable]) -> Vec<Vec<i32>> {
    let mut result = clauses.to_vec();
    for ext in extensions {
        result.extend(extension_to_clauses(ext));
    }
    result
}

/// Evaluate a clause under a given truth assignment.
///
/// Returns `true` if at least one literal in the clause is satisfied.
/// An empty clause is always false (unsatisfied).
fn eval_clause(clause: &[i32], assignment: &HashSet<i32>) -> bool {
    clause.iter().any(|&lit| assignment.contains(&lit))
}

/// Evaluate a formula (conjunction of clauses) under a truth assignment.
///
/// Returns `true` if every clause is satisfied.
fn eval_formula(clauses: &[Vec<i32>], assignment: &HashSet<i32>) -> bool {
    clauses.iter().all(|clause| eval_clause(clause, assignment))
}

/// Collect all variable indices that appear in a formula.
#[must_use]
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

/// Check satisfiability of a formula by brute-force enumeration.
///
/// Enumerates all 2^n truth assignments for n variables. Only feasible
/// for small formulas (n <= 20 or so).
///
/// Returns `Some(assignment)` if satisfiable, `None` if unsatisfiable.
/// The assignment is a set of true literals (positive = true, negative = false).
#[must_use]
fn brute_force_sat(clauses: &[Vec<i32>], vars: &[i32]) -> Option<HashSet<i32>> {
    let n = vars.len();
    if n > 24 {
        // Safety bound: 2^24 = 16M assignments, beyond that is too slow.
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

/// S40: Verify that an extended formula is equisatisfiable with the original.
///
/// For small formulas, performs brute-force satisfiability checking on both
/// the original and extended formulas. The extension is sound if:
///   original SAT <=> extended SAT
///
/// This is the core soundness property of extended resolution.
///
/// Returns `true` if equisatisfiability holds, `false` if violated or if
/// the formula is too large for brute-force checking.
#[must_use]
pub fn verify_extension_equisatisfiable(
    original: &[Vec<i32>],
    extended: &[Vec<i32>],
    ext_vars: &[ExtensionVariable],
) -> bool {
    let orig_vars = collect_variables(original);
    let ext_all_vars = collect_variables(extended);

    // Check that extension variables are fresh (not in original).
    let orig_set: HashSet<i32> = orig_vars.iter().copied().collect();
    for ext in ext_vars {
        if orig_set.contains(&ext.name) {
            return false; // Extension variable collides with original.
        }
    }

    let orig_sat = brute_force_sat(original, &orig_vars);
    let ext_sat = brute_force_sat(extended, &ext_all_vars);

    match (orig_sat, ext_sat) {
        (Some(_), Some(_)) => true, // Both SAT.
        (None, None) => true,       // Both UNSAT.
        _ => false,                 // Mismatch -- soundness violation.
    }
}

/// Perform a single extended resolution step (binary resolution on a pivot).
///
/// Given clause1 containing `pivot` and clause2 containing `-pivot`,
/// produces the resolvent: (clause1 \ {pivot}) U (clause2 \ {-pivot}).
///
/// Returns the resolvent clause with duplicates removed.
#[must_use]
pub fn er_proof_step(clause1: &[i32], clause2: &[i32], pivot: i32) -> Vec<i32> {
    let mut resolvent = HashSet::new();

    for &lit in clause1 {
        if lit != pivot {
            resolvent.insert(lit);
        }
    }
    for &lit in clause2 {
        if lit != -pivot {
            resolvent.insert(lit);
        }
    }

    let mut result: Vec<i32> = resolvent.into_iter().collect();
    result.sort_unstable_by_key(|&lit| (lit.abs(), lit));
    result
}

/// Verify a sequence of resolution steps produces the empty clause.
///
/// Each step is (clause_index_1, clause_index_2, pivot). The initial
/// clauses are numbered 0..clauses.len(). Derived clauses are appended
/// in order. The proof is valid if the final derived clause is empty.
#[must_use]
pub fn verify_resolution_proof(clauses: &[Vec<i32>], steps: &[(usize, usize, i32)]) -> bool {
    let mut all_clauses: Vec<Vec<i32>> = clauses.to_vec();

    for &(idx1, idx2, pivot) in steps {
        if idx1 >= all_clauses.len() || idx2 >= all_clauses.len() {
            return false;
        }
        // Verify pivot appears correctly.
        if !all_clauses[idx1].contains(&pivot) {
            return false;
        }
        if !all_clauses[idx2].contains(&(-pivot)) {
            return false;
        }
        let resolvent = er_proof_step(&all_clauses[idx1], &all_clauses[idx2], pivot);
        all_clauses.push(resolvent);
    }

    // Proof succeeds if final clause is empty (contradiction derived).
    all_clauses.last().is_some_and(|clause| clause.is_empty())
}
