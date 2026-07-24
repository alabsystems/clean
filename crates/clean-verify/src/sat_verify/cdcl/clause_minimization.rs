// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Learned clause minimization verification.
//!
//! After CDCL conflict analysis produces a learned clause, minimization
//! techniques attempt to shorten it while preserving logical entailment.
//! Shorter clauses propagate sooner and prune more search space.
//!
//! Techniques implemented:
//! - **Self-subsumption**: resolve the learned clause with an existing clause;
//!   if the resolvent is a subset, keep the shorter version.
//! - **Vivification**: tentatively assign negations of literals and propagate;
//!   if a conflict arises, the corresponding literal is redundant.
//! - **LBD (Literal Block Distance)**: measure clause quality by the number
//!   of distinct decision levels it spans.
//!
//! References:
//! - Sorensson & Biere, "Minimizing Learned Clauses", SAT 2009.
//! - Piette, Hamadi & Sais, "Vivification of Learned Clauses", ECAI 2008.
//! - Audemard & Simon, "Predicting Learnt Clauses Quality in Modern SAT
//!   Solvers", IJCAI 2009 (LBD / glucose metric).

use super::var_of;
use crate::spec::ProofStatus;

/// Result of minimizing a learned clause.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct MinimizationResult {
    pub original_size: usize,
    pub minimized_size: usize,
    pub reduction: usize,
    pub sound: bool,
}

/// Self-subsumption: resolve `clause` with `resolvent` on some pivot.
///
/// If there exists a variable `v` such that `clause` contains `+v` and
/// `resolvent` contains `-v` (or vice versa), and the resolution result
/// is a subset of `clause`, then return the minimized (shorter) clause.
///
/// Returns `None` if no self-subsumption is applicable.
#[must_use]
pub fn self_subsumption(clause: &[i32], resolvent: &[i32]) -> Option<Vec<i32>> {
    if clause.is_empty() || resolvent.is_empty() {
        return None;
    }

    // Try each variable that appears with opposite polarity in the two clauses.
    for &lit_c in clause {
        let neg = -lit_c;
        if resolvent.contains(&neg) {
            // Resolve on var_of(lit_c): union minus the pivot pair.
            let pivot_var = var_of(lit_c);
            let mut result: Vec<i32> = Vec::with_capacity(clause.len() + resolvent.len());
            let mut seen_vars: Vec<u32> = Vec::new();

            for &lit in clause.iter().chain(resolvent.iter()) {
                let v = var_of(lit);
                if v == pivot_var {
                    continue;
                }
                if !seen_vars.contains(&v) {
                    seen_vars.push(v);
                    result.push(lit);
                }
            }

            // Check if result is a subset of clause (every literal in result
            // appears in clause). If so, self-subsumption applies.
            if result.iter().all(|r| clause.contains(r)) && result.len() < clause.len() {
                return Some(result);
            }
        }
    }

    None
}

/// Check whether clause `a` subsumes clause `b`.
///
/// Clause `a` subsumes `b` iff every literal in `a` also appears in `b`.
/// An empty clause subsumes everything (it represents falsity).
#[must_use]
pub fn clause_subsumes(a: &[i32], b: &[i32]) -> bool {
    a.iter().all(|lit| b.contains(lit))
}

/// Minimize a learned clause by attempting self-subsumption with each
/// clause in the database. Applies greedily: the first successful
/// self-subsumption shortens the clause, then we continue scanning.
#[must_use]
pub fn minimize_learned_clause(clause: &[i32], clauses_db: &[Vec<i32>]) -> Vec<i32> {
    let mut current = clause.to_vec();

    for db_clause in clauses_db {
        if let Some(minimized) = self_subsumption(&current, db_clause) {
            current = minimized;
        }
    }

    current
}

/// One step of vivification: try negating each literal and propagating.
///
/// For each literal `l` in the clause, negate it and call `unit_propagate`.
/// If propagation derives a conflict (returns `Some(conflicting_lit)` where
/// `conflicting_lit` is already in the clause with opposite sign), then `l`
/// is redundant and can be removed.
///
/// The `unit_propagate` callback takes a partial assignment (as a slice of
/// unit literals) and returns `Some(implied_lit)` if a new unit is implied,
/// or `None` if no further propagation occurs.
#[must_use]
pub fn vivification_step(
    clause: &[i32],
    unit_propagate: &dyn Fn(&[i32]) -> Option<i32>,
) -> Vec<i32> {
    if clause.is_empty() {
        return Vec::new();
    }

    let mut result = clause.to_vec();
    let mut i = 0;

    while i < result.len() {
        let lit = result[i];
        let negated = -lit;

        // Try propagating with this literal negated.
        if let Some(implied) = unit_propagate(&[negated]) {
            // If propagation implies a literal whose negation is in the clause,
            // then `lit` is redundant (the other literals already force the clause true).
            let neg_implied = -implied;
            if result.contains(&neg_implied) && neg_implied != lit {
                result.remove(i);
                continue;
            }
        }
        i += 1;
    }

    result
}

/// Brute-force verification that `minimized` logically implies `original`.
///
/// For clause minimization, the minimized clause is *stronger* than the
/// original (fewer literals in the disjunction). The soundness property is:
/// every satisfying assignment of `minimized` also satisfies `original`.
/// Equivalently, `minimized => original` is a tautology.
///
/// For small instances (num_vars <= 20), enumerates all 2^n assignments.
///
/// Returns `false` if `num_vars > 20` (too expensive) or if the check fails.
#[must_use]
pub fn verify_minimization_sound(original: &[i32], minimized: &[i32], num_vars: u32) -> bool {
    if num_vars > 20 {
        return false;
    }

    let total = 1u64 << num_vars;

    for assignment_bits in 0..total {
        let orig_sat = eval_clause_under(original, assignment_bits, num_vars);
        let min_sat = eval_clause_under(minimized, assignment_bits, num_vars);

        // If minimized is satisfied but original is not, soundness fails.
        // (The minimized clause must imply the original.)
        if min_sat && !orig_sat {
            return false;
        }
    }

    true
}

/// Evaluate a clause under a given assignment (encoded as a bitmask).
///
/// Bit `i` of `assignment_bits` encodes variable `i+1`:
/// - bit set => variable is true
/// - bit clear => variable is false
#[must_use]
fn eval_clause_under(clause: &[i32], assignment_bits: u64, num_vars: u32) -> bool {
    for &lit in clause {
        let var = var_of(lit);
        if var == 0 || var > num_vars {
            continue;
        }
        let var_true = (assignment_bits >> (var - 1)) & 1 == 1;
        let lit_true = if lit > 0 { var_true } else { !var_true };
        if lit_true {
            return true;
        }
    }
    false
}

/// Compute Literal Block Distance (LBD) of a clause.
///
/// LBD is the number of distinct decision levels among the clause's literals.
/// Low LBD indicates a "glue clause" that connects different parts of the
/// search space and is highly valuable to keep.
///
/// The `decision_levels` array maps variable index to its decision level.
/// Index 0 is unused (variables are 1-indexed).
///
/// Reference: Audemard & Simon, IJCAI 2009.
#[must_use]
pub fn clause_lbd(clause: &[i32], decision_levels: &[u32]) -> u32 {
    let mut seen_levels: Vec<u32> = Vec::new();

    for &lit in clause {
        let var = var_of(lit) as usize;
        if var < decision_levels.len() {
            let level = decision_levels[var];
            if !seen_levels.contains(&level) {
                seen_levels.push(level);
            }
        }
    }

    seen_levels.len() as u32
}

/// Sort literals in a clause by their VSIDS activity score (descending).
///
/// Higher-activity literals appear first. This is useful for watched literal
/// selection: watching the most active literals reduces watch-list updates.
///
/// The `activity` array maps variable index to its VSIDS score.
/// Index 0 is unused (variables are 1-indexed).
pub fn sort_by_activity(clause: &mut [i32], activity: &[f64]) {
    clause.sort_by(|&a, &b| {
        let act_a = activity.get(var_of(a) as usize).copied().unwrap_or(0.0);
        let act_b = activity.get(var_of(b) as usize).copied().unwrap_or(0.0);
        // Sort descending by activity. Use total_cmp for deterministic NaN handling.
        act_b.total_cmp(&act_a)
    });
}

/// S09: Self-subsumption is sound -- if `self_subsumption(C, D)` returns `C'`,
/// then `C'` is logically entailed by the conjunction of `C` and `D`.
///
/// Proof sketch: Self-subsumption is a restricted form of resolution.
/// If resolving C with D on pivot p yields R, and R is a subset of C,
/// then C logically entails R (since R has fewer disjuncts, every model
/// of C satisfies at least one literal in R which is also in C).
/// More precisely: R = (C \ {p}) union (D \ {-p}). If R subset C,
/// then every literal in R is in C, so every model of C satisfies R.
pub const S09_SELF_SUBSUMPTION_SOUND: ProofStatus = ProofStatus::DerivedPending;

/// S10: Vivification preserves entailment -- removing a literal from a clause
/// via vivification yields a clause still entailed by the original formula.
///
/// Proof sketch (Piette et al., ECAI 2008): If negating literal l and
/// propagating derives a conflict with the existing clause database, then
/// the remaining literals in the clause already force the clause to be
/// satisfied under any model of the formula. Therefore removing l preserves
/// entailment with respect to the full clause database.
pub const S10_VIVIFICATION_PRESERVES_ENTAILMENT: ProofStatus = ProofStatus::DerivedPending;
