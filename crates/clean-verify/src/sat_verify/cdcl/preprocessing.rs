// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! CNF preprocessing verification for SAT solvers.
//!
//! Implements standard preprocessing techniques (subsumption elimination,
//! pure literal elimination, failed literal probing, self-subsumption)
//! with equisatisfiability verification for small instances.
//!
//! References:
//! - Handbook of Satisfiability, Ch. 9 (Preprocessing)
//! - Een & Biere, "Effective Preprocessing in SAT through Variable and Clause Elimination" (SAT 2005)

use std::collections::HashSet;

use crate::spec::ProofStatus;

use super::{negate, var_of, CdclState};

/// Statistics comparing original and preprocessed CNF formulae.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub struct PreprocessingStats {
    pub original_clauses: usize,
    pub preprocessed_clauses: usize,
    pub original_literals: usize,
    pub preprocessed_literals: usize,
    pub clauses_removed: usize,
    pub literals_removed: usize,
}

/// S11: Subsumption elimination preserves satisfiability.
pub const S11_SUBSUMPTION_PRESERVES_SAT: ProofStatus = ProofStatus::DerivedPending;

/// S12: Pure literal elimination preserves satisfiability.
pub const S12_PURE_LITERAL_PRESERVES_SAT: ProofStatus = ProofStatus::DerivedPending;

/// Remove subsumed clauses: if clause A is a subset of clause B, remove B.
///
/// A clause C subsumes D iff every literal in C also appears in D.
/// Removing subsumed clauses preserves satisfiability because D is
/// logically implied by C (C => D in propositional logic).
#[must_use]
pub fn subsumption_elimination(clauses: &[Vec<i32>]) -> Vec<Vec<i32>> {
    let clause_sets: Vec<HashSet<i32>> = clauses
        .iter()
        .map(|c| c.iter().copied().collect())
        .collect();

    let mut subsumed = vec![false; clauses.len()];

    for (i, set_i) in clause_sets.iter().enumerate() {
        if subsumed[i] {
            continue;
        }
        for (j, set_j) in clause_sets.iter().enumerate() {
            if i == j || subsumed[j] {
                continue;
            }
            // If i is a proper subset or equal to j, and i != j in content, subsume j.
            // If they are equal sets, subsume the later one.
            if set_i.len() <= set_j.len()
                && set_i.is_subset(set_j)
                && (set_i.len() < set_j.len() || i < j)
            {
                subsumed[j] = true;
            }
        }
    }

    clauses
        .iter()
        .enumerate()
        .filter(|(i, _)| !subsumed[*i])
        .map(|(_, c)| c.clone())
        .collect()
}

/// Identify pure literals and remove clauses containing them.
///
/// A literal is "pure" if it appears in the formula but its negation does not.
/// Setting a pure literal to true satisfies all clauses containing it without
/// falsifying any clause (since the negation never appears).
///
/// Returns `(reduced_clauses, pure_assignments)` where `pure_assignments`
/// contains the pure literals that should be set to true.
#[must_use]
pub fn pure_literal_elimination(clauses: &[Vec<i32>], num_vars: u32) -> (Vec<Vec<i32>>, Vec<i32>) {
    // Track polarity: 0 = unseen, 1 = positive only, 2 = negative only, 3 = both
    let mut polarity = vec![0u8; (num_vars + 1) as usize];

    for clause in clauses {
        for &lit in clause {
            let var = var_of(lit) as usize;
            if var == 0 || var > num_vars as usize {
                continue;
            }
            let bit = if lit > 0 { 1 } else { 2 };
            polarity[var] |= bit;
        }
    }

    let mut pure_lits: Vec<i32> = Vec::new();

    for var in 1..=num_vars {
        match polarity[var as usize] {
            1 => pure_lits.push(var as i32),    // only positive
            2 => pure_lits.push(-(var as i32)), // only negative
            _ => {}
        }
    }

    let pure_set: HashSet<i32> = pure_lits.iter().copied().collect();

    let reduced = clauses
        .iter()
        .filter(|clause| !clause.iter().any(|lit| pure_set.contains(lit)))
        .cloned()
        .collect();

    (reduced, pure_lits)
}

/// Test if assuming `literal` leads to immediate conflict via unit propagation.
///
/// Creates a temporary CDCL state, assumes the literal, runs BCP. If a
/// conflict is detected, the literal's negation is forced. Returns
/// `Some(negated_literal)` if conflict found, `None` otherwise.
#[must_use]
pub fn failed_literal_probe(clauses: &[Vec<i32>], literal: i32) -> Option<i32> {
    let max_var = clauses
        .iter()
        .flat_map(|c| c.iter())
        .map(|&l| var_of(l))
        .max()
        .unwrap_or(0);

    let mut state = CdclState::new(max_var, clauses.to_vec());

    // Assign the probe literal at decision level 1.
    if state.decide(literal).is_err() {
        return None;
    }

    // Run BCP; conflict means the literal is failed.
    match super::bcp::bcp_loop(&mut state) {
        Err(super::CdclError::Conflict(_)) => Some(negate(literal)),
        _ => None,
    }
}

/// Strengthen clauses by self-subsumption resolution.
///
/// If resolving clause C with clause D on pivot literal p produces a
/// resolvent R that is a subset of (C minus p), then C can be
/// strengthened by removing p from C.
///
/// Example: C = {a, b, p}, D = {a, ~p}. Resolvent R = {a, b}.
/// R is a subset of C \ {p} = {a, b}, so we can replace C with {a, b}.
#[must_use]
pub fn self_subsumption_elimination(clauses: &[Vec<i32>]) -> Vec<Vec<i32>> {
    let mut result: Vec<Vec<i32>> = clauses.to_vec();
    let mut changed = true;

    while changed {
        changed = false;
        let snapshot = result.clone();
        let clause_sets: Vec<HashSet<i32>> = snapshot
            .iter()
            .map(|c| c.iter().copied().collect())
            .collect();

        for i in 0..snapshot.len() {
            for j in 0..snapshot.len() {
                if i == j {
                    continue;
                }
                // Find pivot: a literal in C_i whose negation is in C_j,
                // and C_j \ {~pivot} is a subset of C_i.
                let strengthened = try_self_subsume(&clause_sets[i], &clause_sets[j]);
                if let Some(new_clause) = strengthened {
                    if new_clause.len() < result[i].len() {
                        result[i] = new_clause.into_iter().collect();
                        result[i].sort_unstable();
                        changed = true;
                    }
                }
            }
        }
    }

    result
}

/// Try to self-subsume clause_i using clause_j.
/// Returns a strengthened version of clause_i if possible.
fn try_self_subsume(set_i: &HashSet<i32>, set_j: &HashSet<i32>) -> Option<HashSet<i32>> {
    // Look for a single pivot literal p in set_i such that ~p is in set_j,
    // and (set_j \ {~p}) is a subset of set_i.
    for &lit in set_j {
        let neg = negate(lit);
        if set_i.contains(&neg) {
            // Check: set_j \ {lit} subset of set_i \ {neg}?
            let j_without_pivot: HashSet<i32> =
                set_j.iter().copied().filter(|&l| l != lit).collect();
            let i_without_pivot: HashSet<i32> =
                set_i.iter().copied().filter(|&l| l != neg).collect();
            if j_without_pivot.is_subset(&i_without_pivot) {
                // Strengthen: remove neg from set_i
                return Some(i_without_pivot);
            }
        }
    }
    None
}

/// Brute-force verify equisatisfiability for small instances.
///
/// Enumerates all 2^n assignments (only practical for small num_vars)
/// and checks that original and preprocessed formulae agree on
/// satisfiability. Returns `true` if both are satisfiable or both
/// are unsatisfiable.
///
/// # Panics
///
/// May run for a very long time if `num_vars` is large. Intended for
/// testing with num_vars <= 20.
#[must_use]
pub fn verify_preprocessing_equisat(
    original: &[Vec<i32>],
    preprocessed: &[Vec<i32>],
    num_vars: u32,
) -> bool {
    let orig_sat = is_satisfiable_brute(original, num_vars);
    let prep_sat = is_satisfiable_brute(preprocessed, num_vars);
    orig_sat == prep_sat
}

/// Check satisfiability by enumerating all assignments.
fn is_satisfiable_brute(clauses: &[Vec<i32>], num_vars: u32) -> bool {
    if clauses.is_empty() {
        return true;
    }
    let total = 1u64 << num_vars;
    for assignment in 0..total {
        if eval_under_assignment(clauses, num_vars, assignment) {
            return true;
        }
    }
    false
}

/// Evaluate a CNF formula under a specific assignment encoded as a bitmask.
/// Bit i (0-indexed) represents variable (i+1): 1 = true, 0 = false.
fn eval_under_assignment(clauses: &[Vec<i32>], num_vars: u32, assignment: u64) -> bool {
    for clause in clauses {
        let mut clause_sat = false;
        for &lit in clause {
            let var = var_of(lit);
            if var == 0 || var > num_vars {
                continue;
            }
            let var_true = (assignment >> (var - 1)) & 1 == 1;
            let lit_true = if lit > 0 { var_true } else { !var_true };
            if lit_true {
                clause_sat = true;
                break;
            }
        }
        if !clause_sat {
            return false;
        }
    }
    true
}

/// Count total literals across all clauses.
#[must_use]
pub fn count_literals(clauses: &[Vec<i32>]) -> usize {
    clauses.iter().map(Vec::len).sum()
}

/// Compute reduction statistics between original and preprocessed formulae.
#[must_use]
pub fn preprocessing_stats(original: &[Vec<i32>], preprocessed: &[Vec<i32>]) -> PreprocessingStats {
    let original_clauses = original.len();
    let preprocessed_clauses = preprocessed.len();
    let original_literals = count_literals(original);
    let preprocessed_literals = count_literals(preprocessed);
    PreprocessingStats {
        original_clauses,
        preprocessed_clauses,
        original_literals,
        preprocessed_literals,
        clauses_removed: original_clauses.saturating_sub(preprocessed_clauses),
        literals_removed: original_literals.saturating_sub(preprocessed_literals),
    }
}
