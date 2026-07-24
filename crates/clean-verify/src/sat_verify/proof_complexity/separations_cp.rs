// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Cutting Planes proof construction and verification for separation witnesses.
//!
//! Provides standalone CP derivation verification and a concrete polynomial-size
//! CP proof of the pigeonhole principle PHP(n+1, n), demonstrating the
//! exponential separation from resolution (Haken 1985 vs Cook et al. 1987).

use super::cutting_planes::CpInequality;

/// A step in a standalone Cutting Planes derivation.
///
/// Indices reference previously derived inequalities (0-indexed into the
/// accumulated list of input + derived inequalities).
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum SepCpStep {
    /// Add two inequalities coefficient-wise.
    Addition(usize, usize),
    /// Multiply an inequality by a positive integer scalar.
    Multiplication(usize, i64),
    /// Divide an inequality by a positive integer (ceiling on RHS).
    Division(usize, i64),
    /// Weaken: drop variable `var` (set its coefficient to 0, keep RHS).
    Weakening(usize, u32),
    /// Boolean axiom: x_var >= 0 (variable is in {0,1}).
    BooleanAxiom(u32),
}

// ---------------------------------------------------------------------------
// CP derivation verification
// ---------------------------------------------------------------------------

/// Verify a Cutting Planes derivation step by step.
///
/// `inequalities` are the initial axioms. `steps` derive new inequalities.
/// Returns `true` if every step is valid according to CP rules.
#[must_use]
pub fn verify_cp_derivation(inequalities: &[CpInequality], steps: &[SepCpStep]) -> bool {
    let mut all: Vec<CpInequality> = inequalities.to_vec();

    for step in steps {
        match step {
            SepCpStep::Addition(a, b) => {
                let (Some(la), Some(lb)) = (all.get(*a), all.get(*b)) else {
                    return false;
                };
                let n = la.coeffs.len().max(lb.coeffs.len());
                let coeffs: Vec<i64> = (0..n).map(|i| coeff_at(la, i) + coeff_at(lb, i)).collect();
                let rhs = la.rhs + lb.rhs;
                all.push(CpInequality::new(coeffs, rhs));
            }
            SepCpStep::Multiplication(a, scalar) => {
                if *scalar <= 0 {
                    return false;
                }
                let Some(base) = all.get(*a) else {
                    return false;
                };
                let coeffs: Vec<i64> = base.coeffs.iter().map(|c| c * scalar).collect();
                all.push(CpInequality::new(coeffs, base.rhs * scalar));
            }
            SepCpStep::Division(a, divisor) => {
                if *divisor <= 0 {
                    return false;
                }
                let Some(base) = all.get(*a) else {
                    return false;
                };
                let coeffs: Vec<i64> = base.coeffs.iter().map(|c| div_ceil(*c, *divisor)).collect();
                all.push(CpInequality::new(coeffs, div_ceil(base.rhs, *divisor)));
            }
            SepCpStep::Weakening(a, var) => {
                let Some(base) = all.get(*a) else {
                    return false;
                };
                let vi = *var as usize;
                let mut coeffs = base.coeffs.clone();
                if vi < coeffs.len() {
                    coeffs[vi] = 0;
                }
                all.push(CpInequality::new(coeffs, base.rhs));
            }
            SepCpStep::BooleanAxiom(var) => {
                let vi = *var as usize;
                let n = vi + 1;
                let mut coeffs = vec![0i64; n];
                coeffs[vi] = 1;
                all.push(CpInequality::new(coeffs, 0)); // x_var >= 0
            }
        }
    }

    // A valid refutation ends with 0 >= c where c > 0.
    all.last()
        .is_some_and(|ineq| ineq.coeffs.iter().all(|&c| c == 0) && ineq.rhs > 0)
}

/// Construct a polynomial-size CP proof of PHP(n+1, n).
///
/// Strategy (Cook, Coullard, Turan 1987): Incrementally show that no
/// assignment of pigeons 1..k to holes 1..n can be injective, by summing
/// pigeon constraints and cancelling hole constraints.
///
/// Input inequalities (implicit, not in returned steps):
///   - Pigeon i (0-indexed): sum_j x_{i*n+j} >= 1, for i in 0..n+1
///   - Hole j (0-indexed): -sum_i x_{i*n+j} >= -1, for j in 0..n
///
/// The returned steps reference these axioms by index.
#[must_use]
pub fn cp_proof_of_php(n: usize) -> Vec<SepCpStep> {
    if n == 0 {
        // PHP(1,0): pigeon 1 has no hole. Input is already 0 >= 1.
        return Vec::new();
    }
    let pigeons = n + 1;
    // Axiom layout: indices 0..pigeons are pigeon constraints,
    // indices pigeons..pigeons+n are hole constraints.
    let mut steps = Vec::new();
    // Sum all pigeon constraints: result has all coefficients 1, rhs = pigeons.
    let mut acc = 0; // index of running sum
    for i in 1..pigeons {
        steps.push(SepCpStep::Addition(acc, i));
        acc = pigeons + n + steps.len() - 1;
    }
    // acc now points to: sum of all pigeon constraints.
    // Add all hole constraints to cancel variables.
    for j in 0..n {
        let hole_idx = pigeons + j;
        steps.push(SepCpStep::Addition(acc, hole_idx));
        acc = pigeons + n + steps.len() - 1;
    }
    // Result: 0 >= (n+1) - n = 0 >= 1. Contradiction.
    steps
}

/// Build the input axioms for `cp_proof_of_php` verification.
#[must_use]
pub fn php_cp_axioms(n: usize) -> Vec<CpInequality> {
    if n == 0 {
        return vec![CpInequality::new(Vec::new(), 1)];
    }
    let pigeons = n + 1;
    let num_vars = pigeons * n;
    let mut axioms = Vec::new();
    // Pigeon constraints.
    for i in 0..pigeons {
        let mut coeffs = vec![0i64; num_vars];
        for j in 0..n {
            coeffs[i * n + j] = 1;
        }
        axioms.push(CpInequality::new(coeffs, 1));
    }
    // Hole constraints: -sum_i x_{i*n+j} >= -1.
    for j in 0..n {
        let mut coeffs = vec![0i64; num_vars];
        for i in 0..pigeons {
            coeffs[i * n + j] = -1;
        }
        axioms.push(CpInequality::new(coeffs, -1));
    }
    axioms
}

fn coeff_at(ineq: &CpInequality, i: usize) -> i64 {
    ineq.coeffs.get(i).copied().unwrap_or(0)
}

fn div_ceil(a: i64, b: i64) -> i64 {
    assert!(b > 0);
    if a >= 0 {
        (a + b - 1) / b
    } else {
        a / b
    }
}
