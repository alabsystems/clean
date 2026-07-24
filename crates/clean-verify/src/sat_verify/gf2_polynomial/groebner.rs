// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Buchberger's algorithm for Groebner basis computation over GF(2).
//!
//! Computes a Groebner basis for a polynomial ideal over the field GF(2)
//! with boolean axioms (x^2 = x for all variables). The boolean axioms
//! ensure that the ideal always has a finite Groebner basis (the quotient
//! ring GF(2)[x1,...,xn]/(x1^2-x1,...,xn^2-xn) is finite).
//!
//! ## Algorithm
//!
//! Buchberger's algorithm computes the Groebner basis by:
//! 1. Starting with the input polynomials plus boolean axioms.
//! 2. For each pair (f, g), compute the S-polynomial S(f, g).
//! 3. Reduce S(f, g) modulo the current basis.
//! 4. If the remainder is nonzero, add it to the basis.
//! 5. Repeat until no new polynomials are generated.
//!
//! ## Termination (GF03)
//!
//! Over GF(2) with boolean axioms, every polynomial is equivalent to a
//! multilinear polynomial (degree at most 1 in each variable). The ring
//! GF(2)[x1,...,xn]/(x1^2-x1,...,xn^2-xn) has at most 2^n monomials,
//! so the basis is finite and Buchberger's algorithm terminates.
//!
//! ## References
//!
//! - Buchberger (1965). Thesis on Groebner bases.
//! - Clegg, Edmonds, Impagliazzo (1996). "Using the Groebner basis
//!   algorithm to find proofs of unsatisfiability." STOC 1996.
//! - Cox, Little, O'Shea (2015). "Ideals, Varieties, and Algorithms."

use super::polynomial::{leading_monomial, multivariate_division, s_polynomial, Gf2Poly};

/// A Groebner basis for a polynomial ideal over GF(2) with boolean axioms.
#[derive(Debug, Clone)]
pub struct GroebnerBasis {
    /// The basis polynomials, each in canonical multilinear form.
    basis: Vec<Gf2Poly>,
    /// Number of variables in the system.
    num_vars: u32,
}

impl GroebnerBasis {
    /// Read-only access to the basis polynomials.
    #[must_use]
    pub fn polynomials(&self) -> &[Gf2Poly] {
        &self.basis
    }

    /// Number of polynomials in the basis.
    #[must_use]
    pub fn len(&self) -> usize {
        self.basis.len()
    }

    /// Whether the basis is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.basis.is_empty()
    }

    /// Number of variables.
    #[must_use]
    pub fn num_vars(&self) -> u32 {
        self.num_vars
    }
}

/// Reduce a polynomial modulo a Groebner basis to a unique normal form.
///
/// Uses multivariate division: the remainder when dividing by a Groebner
/// basis is unique (independent of divisor ordering).
#[must_use]
pub fn reduce(poly: &Gf2Poly, basis: &GroebnerBasis) -> Gf2Poly {
    if basis.is_empty() {
        return poly.clone();
    }
    let (_, remainder) = multivariate_division(poly, &basis.basis);
    remainder
}

/// Apply boolean reduction (x^2 = x) to all variables in a polynomial.
///
/// Since `Gf2Poly` uses `BTreeSet<u32>` for monomials, boolean reduction
/// is already enforced by construction (sets cannot contain duplicate
/// elements, so x^2 = x automatically). This function is a no-op that
/// simply calls `reduce()` for explicitness.
fn boolean_reduce(poly: &mut Gf2Poly) {
    poly.reduce();
}

/// Compute a Groebner basis using Buchberger's algorithm with boolean
/// axioms over GF(2).
///
/// The boolean axioms (x_i^2 = x_i for i = 0..num_vars-1) are added
/// implicitly via multilinear reduction. Since `Gf2Poly` already enforces
/// multilinearity (BTreeSet monomials), the boolean axioms x^2-x = 0 are
/// built into the representation.
///
/// # Arguments
///
/// * `polynomials` - Input polynomial system.
/// * `num_vars` - Number of boolean variables.
///
/// # Safety Bound
///
/// To prevent runaway computation, the algorithm stops after the basis
/// exceeds 1000 polynomials. For typical SAT-derived systems with small
/// variable counts, this limit is never reached.
#[must_use]
pub fn buchberger(polynomials: &[Gf2Poly], num_vars: u32) -> GroebnerBasis {
    const MAX_BASIS_SIZE: usize = 1000;

    // Start with nonzero input polynomials (in canonical form).
    let mut basis: Vec<Gf2Poly> = polynomials
        .iter()
        .filter(|p| !p.is_zero())
        .cloned()
        .collect();

    // Reduce each basis polynomial.
    for p in &mut basis {
        boolean_reduce(p);
    }

    // Track which pairs have been processed.
    let mut processed: std::collections::HashSet<(usize, usize)> = std::collections::HashSet::new();

    loop {
        let n = basis.len();
        if n > MAX_BASIS_SIZE {
            break;
        }

        let mut new_polys: Vec<Gf2Poly> = Vec::new();

        for i in 0..n {
            for j in (i + 1)..n {
                if processed.contains(&(i, j)) {
                    continue;
                }
                processed.insert((i, j));

                if let Some(s_poly) = s_polynomial(&basis[i], &basis[j]) {
                    if s_poly.is_zero() {
                        continue;
                    }

                    let (_, mut remainder) = multivariate_division(&s_poly, &basis);
                    boolean_reduce(&mut remainder);

                    if !remainder.is_zero() {
                        new_polys.push(remainder);
                    }
                }
            }
        }

        if new_polys.is_empty() {
            break;
        }

        for p in new_polys {
            basis.push(p);
        }
    }

    // Minimize: remove polynomials whose leading monomial is divisible by
    // the leading monomial of another basis polynomial.
    let lms: Vec<Option<std::collections::BTreeSet<u32>>> =
        basis.iter().map(leading_monomial).collect();

    let mut keep = vec![true; basis.len()];
    for i in 0..basis.len() {
        if !keep[i] {
            continue;
        }
        for j in 0..basis.len() {
            if i == j || !keep[j] {
                continue;
            }
            if let (Some(lm_i), Some(lm_j)) = (&lms[i], &lms[j]) {
                if lm_j.is_subset(lm_i) && lm_i != lm_j {
                    keep[i] = false;
                    break;
                }
            }
        }
    }

    let minimized: Vec<Gf2Poly> = basis
        .into_iter()
        .enumerate()
        .filter(|(idx, _)| keep[*idx])
        .map(|(_, p)| p)
        .collect();

    GroebnerBasis {
        basis: minimized,
        num_vars,
    }
}

/// Check if the Groebner basis contains the constant 1, indicating that
/// the polynomial system is unsatisfiable (the ideal is the whole ring).
///
/// A system of polynomial equations `{f_1 = 0, ..., f_k = 0}` over GF(2)
/// is unsatisfiable iff the Groebner basis of the ideal `<f_1,...,f_k>`
/// (with boolean axioms) contains 1.
#[must_use]
pub fn is_unsatisfiable(basis: &GroebnerBasis) -> bool {
    basis.basis.iter().any(Gf2Poly::is_one)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_buchberger_empty_system() {
        let basis = buchberger(&[], 2);
        assert!(basis.is_empty());
        assert!(!is_unsatisfiable(&basis));
    }

    #[test]
    fn test_buchberger_single_zero() {
        let basis = buchberger(&[Gf2Poly::zero()], 2);
        assert!(basis.is_empty());
    }

    #[test]
    fn test_buchberger_trivially_unsat() {
        // System: {1 = 0} is unsatisfiable.
        let basis = buchberger(&[Gf2Poly::one()], 2);
        assert!(is_unsatisfiable(&basis));
    }

    #[test]
    fn test_buchberger_satisfiable_single_var() {
        // x0 = 0 is satisfiable (set x0 = 0).
        let basis = buchberger(&[Gf2Poly::variable(0)], 1);
        assert!(!is_unsatisfiable(&basis));
    }

    #[test]
    fn test_buchberger_contradictory_system() {
        // System: {x0 = 0, x0 + 1 = 0} -> x0 = 0 AND x0 = 1 -> UNSAT.
        let p1 = Gf2Poly::variable(0);
        let p2 = Gf2Poly::variable(0).add(&Gf2Poly::one());
        let basis = buchberger(&[p1, p2], 1);
        assert!(is_unsatisfiable(&basis));
    }

    #[test]
    fn test_buchberger_two_var_unsat() {
        // System: {x0 + x1 = 0, x0 + x1 + 1 = 0}
        // First says x0 = x1, second says x0 != x1 -> UNSAT.
        let p1 = Gf2Poly::variable(0).add(&Gf2Poly::variable(1));
        let p2 = Gf2Poly::variable(0)
            .add(&Gf2Poly::variable(1))
            .add(&Gf2Poly::one());
        let basis = buchberger(&[p1, p2], 2);
        assert!(is_unsatisfiable(&basis));
    }

    #[test]
    fn test_buchberger_two_var_sat() {
        // System: {x0 + x1 = 0, x0*x1 = 0}
        // x0 = x1 and x0*x1 = 0 -> x0 = x1 = 0. Satisfiable.
        let p1 = Gf2Poly::variable(0).add(&Gf2Poly::variable(1));
        let p2 = Gf2Poly::monomial(&[0, 1]);
        let basis = buchberger(&[p1, p2], 2);
        assert!(!is_unsatisfiable(&basis));
    }

    #[test]
    fn test_reduce_to_normal_form() {
        // basis: {x0 = 0} (a trivial Groebner basis)
        // reduce x0*x1 modulo {x0} should give 0.
        let gb = buchberger(&[Gf2Poly::variable(0)], 2);
        let p = Gf2Poly::monomial(&[0, 1]);
        let r = reduce(&p, &gb);
        assert!(r.is_zero());
    }

    #[test]
    fn test_reduce_nonzero_remainder() {
        // basis: {x0 = 0}
        // reduce x1 modulo {x0} should give x1 (not divisible).
        let gb = buchberger(&[Gf2Poly::variable(0)], 2);
        let p = Gf2Poly::variable(1);
        let r = reduce(&p, &gb);
        assert_eq!(r, Gf2Poly::variable(1));
    }

    #[test]
    fn test_buchberger_cnf_clause_unsat() {
        // Encode: (x1) AND (NOT x1) — trivially UNSAT.
        // Clause (x1): poly = 1 + x0 (since x1 satisfied iff poly = 0)
        // Clause (NOT x1): poly = x0
        let p1 = Gf2Poly::from_clause(&[1]);
        let p2 = Gf2Poly::from_clause(&[-1]);
        let basis = buchberger(&[p1, p2], 1);
        assert!(is_unsatisfiable(&basis));
    }

    #[test]
    fn test_buchberger_tseitin_triangle() {
        // Tseitin on a triangle (3 vertices, 3 edges) with odd parity sum.
        // Edges: (0,1), (1,2), (0,2). Variables: e0, e1, e2.
        // Parity constraints (XOR):
        //   v0: e0 + e2 = 1  (odd parity)
        //   v1: e0 + e1 = 0  (even parity)
        //   v2: e1 + e2 = 0  (even parity)
        // Sum of parities = 1 (odd) -> UNSAT (each edge counted twice,
        // total must be even).
        let p_v0 = Gf2Poly::variable(0)
            .add(&Gf2Poly::variable(2))
            .add(&Gf2Poly::one());
        let p_v1 = Gf2Poly::variable(0).add(&Gf2Poly::variable(1));
        let p_v2 = Gf2Poly::variable(1).add(&Gf2Poly::variable(2));

        let basis = buchberger(&[p_v0, p_v1, p_v2], 3);
        assert!(is_unsatisfiable(&basis));
    }

    #[test]
    fn test_buchberger_tseitin_even_parity_sat() {
        // Same triangle but even parity sum -> SAT.
        // v0: e0 + e2 = 0, v1: e0 + e1 = 0, v2: e1 + e2 = 0
        let p_v0 = Gf2Poly::variable(0).add(&Gf2Poly::variable(2));
        let p_v1 = Gf2Poly::variable(0).add(&Gf2Poly::variable(1));
        let p_v2 = Gf2Poly::variable(1).add(&Gf2Poly::variable(2));

        let basis = buchberger(&[p_v0, p_v1, p_v2], 3);
        assert!(!is_unsatisfiable(&basis));
    }
}
