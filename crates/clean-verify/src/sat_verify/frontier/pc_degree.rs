// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Polynomial Calculus degree bounds and resolution simulation.
//!
//! Provides tools for:
//! - Translating resolution proofs into Polynomial Calculus derivations
//!   over GF(2).
//! - Computing and verifying degree bounds on PC derivations.
//!
//! ## Resolution-to-PC Translation
//!
//! A resolution proof step resolves two clauses C1 and C2 on a pivot
//! variable x, producing the resolvent C1 \ {x} union C2 \ {-x}.
//!
//! In the polynomial encoding, each clause becomes a polynomial via
//! [`clause_to_polynomial`]. Resolution corresponds to polynomial
//! addition in GF(2): when two clause polynomials share a complementary
//! literal factor, their sum cancels the pivot and yields the resolvent
//! polynomial.
//!
//! ## References
//!
//! - Razborov (1998). Lower bounds for the polynomial calculus.
//! - Impagliazzo, Pudlak, Sgall (1999). Lower bounds for the PC
//!   and Nullstellensatz proof systems.

use super::polynomial_calculus::{clause_to_polynomial, GF2Polynomial};

/// Resolve two clauses on a pivot variable, returning the resolvent.
///
/// Given clause C1 containing literal `+pivot` and clause C2 containing
/// literal `-pivot`, the resolvent is `(C1 \ {+pivot}) union (C2 \ {-pivot})`.
/// If the pivot does not appear with complementary signs, returns `None`.
fn resolve_clauses(c1: &[i32], c2: &[i32], pivot: i32) -> Option<Vec<i32>> {
    let pivot_abs = pivot.abs();
    let has_pos_in_c1 = c1.contains(&pivot_abs);
    let has_neg_in_c1 = c1.iter().any(|&l| l == -pivot_abs);
    let has_pos_in_c2 = c2.contains(&pivot_abs);
    let has_neg_in_c2 = c2.iter().any(|&l| l == -pivot_abs);

    // One clause must contain +pivot, the other -pivot.
    let (pos_clause, neg_clause) = if has_pos_in_c1 && has_neg_in_c2 {
        (c1, c2)
    } else if has_neg_in_c1 && has_pos_in_c2 {
        (c2, c1)
    } else {
        return None;
    };

    let mut resolvent: Vec<i32> = Vec::new();
    for &lit in pos_clause {
        if lit != pivot_abs && !resolvent.contains(&lit) {
            resolvent.push(lit);
        }
    }
    for &lit in neg_clause {
        if lit != -pivot_abs && !resolvent.contains(&lit) {
            resolvent.push(lit);
        }
    }
    resolvent.sort_by_key(|l| l.abs());
    Some(resolvent)
}

/// Translate a resolution proof into a Polynomial Calculus derivation
/// over GF(2).
///
/// # Arguments
///
/// * `clauses` -- initial clause database in DIMACS format. Each inner
///   `Vec<i32>` is a clause where positive/negative integers represent
///   positive/negative literals.
/// * `proof_steps` -- sequence of resolution steps `(i, j, pivot)` where
///   `i` and `j` are indices into the growing derivation (initial clauses
///   followed by derived clauses), and `pivot` is the DIMACS variable
///   resolved upon (sign ignored; the absolute value is used).
///
/// # Returns
///
/// A vector of GF(2) polynomials: the initial clause polynomials
/// followed by derived polynomials. Each resolution step computes the
/// resolvent clause and encodes it as a polynomial. The empty clause
/// (contradiction) is encoded as the constant polynomial 1.
#[must_use]
pub fn resolution_to_pc(
    clauses: &[Vec<i32>],
    proof_steps: &[(usize, usize, i32)],
) -> Vec<GF2Polynomial> {
    // Track both clause and polynomial representations.
    let mut clause_db: Vec<Vec<i32>> = clauses.to_vec();
    let mut derivation: Vec<GF2Polynomial> =
        clauses.iter().map(|c| clause_to_polynomial(c)).collect();

    for &(idx1, idx2, pivot) in proof_steps {
        if idx1 < clause_db.len() && idx2 < clause_db.len() {
            if let Some(resolvent) = resolve_clauses(&clause_db[idx1], &clause_db[idx2], pivot) {
                if resolvent.is_empty() {
                    // Empty clause = contradiction = constant 1 in GF(2).
                    derivation.push(GF2Polynomial::one());
                } else {
                    derivation.push(clause_to_polynomial(&resolvent));
                }
                clause_db.push(resolvent);
            } else {
                // Invalid resolution: pivot not complementary.
                derivation.push(GF2Polynomial::zero());
                clause_db.push(vec![]);
            }
        } else {
            // Invalid index: push zero polynomial as sentinel.
            derivation.push(GF2Polynomial::zero());
            clause_db.push(vec![]);
        }
    }

    derivation
}

/// Maximum degree across all polynomials in a derivation.
#[must_use]
pub fn pc_proof_degree(derivation: &[GF2Polynomial]) -> usize {
    derivation
        .iter()
        .map(GF2Polynomial::degree)
        .max()
        .unwrap_or(0)
}

/// Verify that every polynomial in a derivation respects a claimed
/// degree bound.
///
/// Returns `true` iff every polynomial in `derivation` has degree at
/// most `claimed_bound`, AND every initial clause polynomial (from
/// `clauses`) also respects the bound.
#[must_use]
pub fn verify_pc_degree_bound(
    clauses: &[Vec<i32>],
    derivation: &[GF2Polynomial],
    claimed_bound: usize,
) -> bool {
    // Check initial clauses.
    for clause in clauses {
        let poly = clause_to_polynomial(clause);
        if poly.degree() > claimed_bound {
            return false;
        }
    }
    // Check all derived polynomials.
    derivation.iter().all(|p| p.degree() <= claimed_bound)
}
