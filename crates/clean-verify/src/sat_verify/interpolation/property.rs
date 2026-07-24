// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Verification of Craig interpolation properties.
//!
//! Given formulas A, B (as sets of clauses) and an interpolant I (as a
//! [`PropFormula`]), this module provides routines to verify the three
//! defining properties of Craig interpolation:
//!
//! 1. **Implication**: A implies I.
//! 2. **Contradiction**: I AND B is unsatisfiable.
//! 3. **Variable restriction**: Vars(I) ⊆ Vars(A) ∩ Vars(B).
//!
//! The verification is brute-force (enumerating all 2^n assignments) and
//! therefore only practical for small variable counts.

use super::PropFormula;
use crate::sat_verify::cdcl::var_of;
use crate::spec::ProofStatus;
use std::collections::{BTreeSet, HashMap, HashSet};

/// I10: Interpolant implication property (A ⊢ I).
pub const I10_INTERPOLANT_IMPLICATION: ProofStatus = ProofStatus::DerivedPending;

/// I11: Interpolant contradiction property (I ∧ B is unsat).
pub const I11_INTERPOLANT_CONTRADICTION: ProofStatus = ProofStatus::DerivedPending;

/// I12: Interpolant variable restriction (Vars(I) ⊆ Vars(A) ∩ Vars(B)).
pub const I12_INTERPOLANT_VARIABLES: ProofStatus = ProofStatus::DerivedPending;

/// Which Craig interpolation property to check.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum InterpolantProperty {
    /// A implies I: every satisfying assignment of A also satisfies I.
    Implication,
    /// I AND B is unsatisfiable: no assignment satisfies both I and B.
    Contradiction,
    /// Vars(I) ⊆ Vars(A) ∩ Vars(B).
    VariableRestriction,
}

/// Detailed result of verifying all three interpolation properties.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PropertyVerifyResult {
    /// Whether the implication property holds.
    pub implication_holds: bool,
    /// Whether the contradiction property holds.
    pub contradiction_holds: bool,
    /// Whether the variable restriction holds.
    pub variable_restriction_holds: bool,
    /// True when all three properties hold.
    pub all_valid: bool,
    /// Variables in I that violate the restriction (empty when valid).
    pub violating_variables: BTreeSet<u32>,
    /// If the implication check failed, one counterexample assignment.
    pub implication_counterexample: Option<HashMap<u32, bool>>,
    /// If the contradiction check failed, one witness assignment.
    pub contradiction_witness: Option<HashMap<u32, bool>>,
}

/// Relative strength classification.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum InterpolantStrengthClass {
    /// I is equivalent to A (strongest possible).
    EquivalentToA,
    /// I is equivalent to NOT B (weakest possible).
    EquivalentToNotB,
    /// I is strictly between A and NOT B.
    Intermediate,
    /// Could not classify (e.g. I is trivially True/False).
    Trivial,
}

/// Size metrics for an interpolant.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct InterpolantSizeInfo {
    /// Number of nodes in the formula tree.
    pub node_count: usize,
    /// Number of distinct variables.
    pub variable_count: usize,
}

// ---------------------------------------------------------------------------
// Core verification functions
// ---------------------------------------------------------------------------

/// Verify Property 1: A implies I.
///
/// For every assignment that satisfies all clauses of A, the interpolant
/// must also evaluate to true. Returns `Ok(())` on success, or `Err` with
/// a counterexample assignment.
pub fn verify_implication(
    a_clauses: &[Vec<i32>],
    interpolant: &PropFormula,
    num_vars: u32,
) -> Result<(), HashMap<u32, bool>> {
    for bits in 0u64..(1u64 << num_vars) {
        let asgn = bits_to_assignment(bits, num_vars);
        if clauses_satisfied(a_clauses, &asgn) && !interpolant.evaluate(&asgn) {
            return Err(asgn);
        }
    }
    Ok(())
}

/// Verify Property 2: I AND B is unsatisfiable.
///
/// No assignment may simultaneously satisfy I and all B-clauses. Returns
/// `Ok(())` on success, or `Err` with a witness assignment.
pub fn verify_contradiction(
    b_clauses: &[Vec<i32>],
    interpolant: &PropFormula,
    num_vars: u32,
) -> Result<(), HashMap<u32, bool>> {
    for bits in 0u64..(1u64 << num_vars) {
        let asgn = bits_to_assignment(bits, num_vars);
        if interpolant.evaluate(&asgn) && clauses_satisfied(b_clauses, &asgn) {
            return Err(asgn);
        }
    }
    Ok(())
}

/// Verify Property 3: Vars(I) ⊆ Vars(A) ∩ Vars(B).
///
/// Returns `Ok(())` when the restriction holds, or `Err` with the set of
/// variables in I that are not shared between A and B.
pub fn verify_variable_restriction(
    a_clauses: &[Vec<i32>],
    b_clauses: &[Vec<i32>],
    interpolant: &PropFormula,
) -> Result<(), BTreeSet<u32>> {
    let shared = compute_shared_variables(a_clauses, b_clauses);
    let interp_vars = interpolant.variables();
    let violations: BTreeSet<u32> = interp_vars
        .iter()
        .filter(|v| !shared.contains(v))
        .copied()
        .collect();
    if violations.is_empty() {
        Ok(())
    } else {
        Err(violations)
    }
}

/// Verify all three Craig interpolation properties and return a composite
/// result with diagnostic information.
#[must_use]
pub fn verify_all_properties(
    a_clauses: &[Vec<i32>],
    b_clauses: &[Vec<i32>],
    interpolant: &PropFormula,
    num_vars: u32,
) -> PropertyVerifyResult {
    let impl_result = verify_implication(a_clauses, interpolant, num_vars);
    let contra_result = verify_contradiction(b_clauses, interpolant, num_vars);
    let var_result = verify_variable_restriction(a_clauses, b_clauses, interpolant);

    let implication_holds = impl_result.is_ok();
    let contradiction_holds = contra_result.is_ok();
    let variable_restriction_holds = var_result.is_ok();

    PropertyVerifyResult {
        implication_holds,
        contradiction_holds,
        variable_restriction_holds,
        all_valid: implication_holds && contradiction_holds && variable_restriction_holds,
        violating_variables: var_result.err().unwrap_or_default(),
        implication_counterexample: impl_result.err(),
        contradiction_witness: contra_result.err(),
    }
}

// ---------------------------------------------------------------------------
// Variable set operations
// ---------------------------------------------------------------------------

/// Extract the set of propositional variables from a CNF formula (set of
/// clauses). Each literal `l` contributes variable `|l|`.
#[must_use]
pub fn extract_variables(clauses: &[Vec<i32>]) -> HashSet<u32> {
    clauses
        .iter()
        .flat_map(|c| c.iter().map(|&l| var_of(l)))
        .collect()
}

/// Compute Vars(A) ∩ Vars(B).
#[must_use]
pub fn compute_shared_variables(a_clauses: &[Vec<i32>], b_clauses: &[Vec<i32>]) -> HashSet<u32> {
    let a_vars = extract_variables(a_clauses);
    let b_vars = extract_variables(b_clauses);
    a_vars.intersection(&b_vars).copied().collect()
}

// ---------------------------------------------------------------------------
// Formula evaluation helpers
// ---------------------------------------------------------------------------

/// Evaluate a CNF formula (conjunction of clauses) under a variable
/// assignment. A clause is satisfied when at least one of its literals is
/// true. The formula is satisfied when every clause is satisfied.
#[must_use]
pub fn evaluate_formula(clauses: &[Vec<i32>], assignment: &HashMap<u32, bool>) -> bool {
    clauses_satisfied(clauses, assignment)
}

/// Enumerate all satisfying assignments of a CNF formula over variables
/// `1..=num_vars`. Only practical for small `num_vars`.
#[must_use]
pub fn enumerate_satisfying_assignments(
    clauses: &[Vec<i32>],
    num_vars: u32,
) -> Vec<HashMap<u32, bool>> {
    let mut results = Vec::new();
    for bits in 0u64..(1u64 << num_vars) {
        let asgn = bits_to_assignment(bits, num_vars);
        if clauses_satisfied(clauses, &asgn) {
            results.push(asgn);
        }
    }
    results
}

// ---------------------------------------------------------------------------
// Strength and size analysis
// ---------------------------------------------------------------------------

/// Classify the relative strength of the interpolant.
///
/// * **EquivalentToA** when I has exactly the same satisfying assignments
///   as A (over shared variables).
/// * **EquivalentToNotB** when I has exactly the same satisfying assignments
///   as NOT-B.
/// * **Intermediate** when I is strictly between A and NOT-B.
/// * **Trivial** when I is a constant (`True` or `False`).
#[must_use]
pub fn verify_interpolant_strength(
    a_clauses: &[Vec<i32>],
    b_clauses: &[Vec<i32>],
    interpolant: &PropFormula,
    num_vars: u32,
) -> InterpolantStrengthClass {
    // Detect trivial interpolants.
    match interpolant {
        PropFormula::True | PropFormula::False => return InterpolantStrengthClass::Trivial,
        _ => {}
    }

    let mut equiv_a = true;
    let mut equiv_not_b = true;

    for bits in 0u64..(1u64 << num_vars) {
        let asgn = bits_to_assignment(bits, num_vars);
        let a_sat = clauses_satisfied(a_clauses, &asgn);
        let b_sat = clauses_satisfied(b_clauses, &asgn);
        let i_val = interpolant.evaluate(&asgn);

        // A implies I and I implies A ⟹ I ≡ A (over all assignments).
        if a_sat != i_val {
            equiv_a = false;
        }
        // NOT-B means ¬(all B-clauses satisfied) = !b_sat.
        if b_sat == i_val {
            equiv_not_b = false;
        }
    }

    if equiv_a {
        InterpolantStrengthClass::EquivalentToA
    } else if equiv_not_b {
        InterpolantStrengthClass::EquivalentToNotB
    } else {
        InterpolantStrengthClass::Intermediate
    }
}

/// Compute size metrics for an interpolant formula.
#[must_use]
pub fn interpolant_size_info(interpolant: &PropFormula) -> InterpolantSizeInfo {
    InterpolantSizeInfo {
        node_count: count_nodes(interpolant),
        variable_count: interpolant.variables().len(),
    }
}

// ---------------------------------------------------------------------------
// Internal helpers
// ---------------------------------------------------------------------------

/// Convert a bit-pattern to a variable assignment over `1..=num_vars`.
fn bits_to_assignment(bits: u64, num_vars: u32) -> HashMap<u32, bool> {
    let mut asgn = HashMap::new();
    for v in 1..=num_vars {
        asgn.insert(v, (bits >> (v - 1)) & 1 == 1);
    }
    asgn
}

/// Check whether every clause in a CNF formula is satisfied.
fn clauses_satisfied(clauses: &[Vec<i32>], asgn: &HashMap<u32, bool>) -> bool {
    clauses.iter().all(|clause| {
        clause.iter().any(|&lit| {
            let var = var_of(lit);
            let val = asgn.get(&var).copied().unwrap_or(false);
            if lit > 0 {
                val
            } else {
                !val
            }
        })
    })
}

/// Count formula tree nodes.
fn count_nodes(f: &PropFormula) -> usize {
    match f {
        PropFormula::Var(_) | PropFormula::True | PropFormula::False => 1,
        PropFormula::Not(inner) => 1 + count_nodes(inner),
        PropFormula::AndType(l, r) | PropFormula::Or(l, r) | PropFormula::Implies(l, r) => {
            1 + count_nodes(l) + count_nodes(r)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_proof_status_constants() {
        assert_eq!(I10_INTERPOLANT_IMPLICATION, ProofStatus::DerivedPending);
        assert_eq!(I11_INTERPOLANT_CONTRADICTION, ProofStatus::DerivedPending);
        assert_eq!(I12_INTERPOLANT_VARIABLES, ProofStatus::DerivedPending);
    }
}
