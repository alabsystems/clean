// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! GF(2) polynomial operations for Groebner basis computation.
//!
//! Re-exports [`Gf2Poly`] from the frontier module and adds operations
//! needed for Buchberger's algorithm: leading monomial extraction under
//! graded reverse lexicographic (grevlex) order, S-polynomial computation,
//! and multivariate polynomial division.
//!
//! ## Monomial Order
//!
//! We use graded reverse lexicographic order (grevlex):
//! 1. Compare total degree first (higher degree is larger).
//! 2. For equal degree, compare variable indices in reverse: the monomial
//!    with the smaller last-differing variable is larger.
//!
//! This is the standard order for Groebner basis computation because it
//! tends to produce smaller bases than lexicographic order.
//!
//! ## References
//!
//! - Cox, Little, O'Shea (2015). "Ideals, Varieties, and Algorithms." Ch. 2.

use std::collections::BTreeSet;

pub use super::super::frontier::gf2_algebra::Gf2Poly;

/// Compare two monomials under graded reverse lexicographic (grevlex) order.
///
/// Returns `Ordering::Greater` if `a` is larger than `b`.
#[must_use]
pub fn grevlex_cmp(a: &BTreeSet<u32>, b: &BTreeSet<u32>) -> std::cmp::Ordering {
    // First: compare total degree.
    let deg_cmp = a.len().cmp(&b.len());
    if deg_cmp != std::cmp::Ordering::Equal {
        return deg_cmp;
    }

    // Equal degree: compare in reverse variable order.
    // In grevlex, among equal-degree monomials, the one with the smaller
    // exponent in the LAST variable where they differ is LARGER.
    let a_vars: Vec<u32> = a.iter().copied().collect();
    let b_vars: Vec<u32> = b.iter().copied().collect();

    // Walk from the highest variable index downward.
    // We need to compare which variables are present. Use symmetric difference.
    let mut a_iter = a_vars.iter().rev();
    let mut b_iter = b_vars.iter().rev();

    // Since degrees are equal, compare variable sets from the top.
    // The monomial that has the smaller variable at the first point of
    // difference (from the top) is LARGER in grevlex.
    loop {
        match (a_iter.next(), b_iter.next()) {
            (None, None) => return std::cmp::Ordering::Equal,
            (Some(_), None) => return std::cmp::Ordering::Greater,
            (None, Some(_)) => return std::cmp::Ordering::Less,
            (Some(&va), Some(&vb)) => {
                if va != vb {
                    // In grevlex: the monomial with the SMALLER variable
                    // at the highest differing position is LARGER.
                    return vb.cmp(&va);
                }
            }
        }
    }
}

/// Return the leading monomial of a polynomial under grevlex order.
///
/// Returns `None` for the zero polynomial.
#[must_use]
pub fn leading_monomial(poly: &Gf2Poly) -> Option<BTreeSet<u32>> {
    if poly.is_zero() {
        return None;
    }
    poly.terms()
        .iter()
        .max_by(|a, b| grevlex_cmp(a, b))
        .cloned()
}

/// Compute the least common multiple of two monomials.
///
/// Since monomials over GF(2) are multilinear (each variable appears at
/// most once), the LCM is just the union of variable sets.
#[must_use]
pub fn monomial_lcm(a: &BTreeSet<u32>, b: &BTreeSet<u32>) -> BTreeSet<u32> {
    a.union(b).copied().collect()
}

/// Divide monomial `a` by monomial `b`, returning `Some(quotient)` if `b`
/// divides `a` (i.e., `b` is a subset of `a`), or `None` otherwise.
#[must_use]
pub fn monomial_divides(a: &BTreeSet<u32>, b: &BTreeSet<u32>) -> Option<BTreeSet<u32>> {
    if b.is_subset(a) {
        Some(a.difference(b).copied().collect())
    } else {
        None
    }
}

/// Compute the S-polynomial of `f` and `g`.
///
/// The S-polynomial is defined as:
///   S(f, g) = lcm(LM(f), LM(g)) / LM(f) * f + lcm(LM(f), LM(g)) / LM(g) * g
///
/// where operations are over GF(2) (so subtraction = addition).
///
/// Returns `None` if either polynomial is zero.
#[must_use]
pub fn s_polynomial(f: &Gf2Poly, g: &Gf2Poly) -> Option<Gf2Poly> {
    let lm_f = leading_monomial(f)?;
    let lm_g = leading_monomial(g)?;

    let lcm = monomial_lcm(&lm_f, &lm_g);

    // lcm / LM(f) -- guaranteed to divide since lcm is superset of lm_f
    let quot_f: Vec<u32> = lcm.difference(&lm_f).copied().collect();
    let quot_g: Vec<u32> = lcm.difference(&lm_g).copied().collect();

    let multiplier_f = Gf2Poly::monomial(&quot_f);
    let multiplier_g = Gf2Poly::monomial(&quot_g);

    // S(f,g) = (lcm/LM(f)) * f + (lcm/LM(g)) * g  (over GF(2))
    let result = multiplier_f.mul(f).add(&multiplier_g.mul(g));
    Some(result)
}

/// Multivariate division of `f` by a set of `divisors`.
///
/// Returns `(quotients, remainder)` where:
///   `f = sum_i quotients[i] * divisors[i] + remainder`
///
/// and no term of `remainder` is divisible by any leading monomial of the
/// divisors.
///
/// This is Algorithm 2 from Cox, Little, O'Shea (2015), Ch. 2, Sec. 3.
#[must_use]
pub fn multivariate_division(f: &Gf2Poly, divisors: &[Gf2Poly]) -> (Vec<Gf2Poly>, Gf2Poly) {
    let s = divisors.len();
    let mut quotients: Vec<Gf2Poly> = vec![Gf2Poly::zero(); s];
    let mut remainder = Gf2Poly::zero();
    let mut p = f.clone();

    // Pre-compute leading monomials of divisors.
    let lms: Vec<Option<BTreeSet<u32>>> = divisors.iter().map(leading_monomial).collect();

    while !p.is_zero() {
        let lm_p = match leading_monomial(&p) {
            Some(lm) => lm,
            None => break,
        };

        let mut divided = false;
        for i in 0..s {
            if let Some(ref lm_di) = lms[i] {
                if let Some(quot_mono) = monomial_divides(&lm_p, lm_di) {
                    // LM(divisors[i]) divides LM(p).
                    let quot_poly =
                        Gf2Poly::monomial(&quot_mono.iter().copied().collect::<Vec<_>>());
                    quotients[i] = quotients[i].add(&quot_poly);
                    // p = p + quot_poly * divisors[i] (addition = subtraction in GF(2))
                    p = p.add(&quot_poly.mul(&divisors[i]));
                    divided = true;
                    break;
                }
            }
        }

        if !divided {
            // No divisor divides LM(p); move LM(p) to remainder.
            let lm_poly = Gf2Poly::monomial(&lm_p.iter().copied().collect::<Vec<_>>());
            remainder = remainder.add(&lm_poly);
            p = p.add(&lm_poly);
        }
    }

    (quotients, remainder)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_grevlex_same_degree() {
        // x0*x1 vs x0*x2: both degree 2.
        // Highest differing var from top: x2 vs x1.
        // x0*x1 has smaller last var (1 < 2) so x0*x1 is LARGER in grevlex.
        let a: BTreeSet<u32> = [0, 1].into_iter().collect();
        let b: BTreeSet<u32> = [0, 2].into_iter().collect();
        assert_eq!(grevlex_cmp(&a, &b), std::cmp::Ordering::Greater);
    }

    #[test]
    fn test_grevlex_different_degree() {
        let a: BTreeSet<u32> = [0, 1, 2].into_iter().collect(); // degree 3
        let b: BTreeSet<u32> = [0, 1].into_iter().collect(); // degree 2
        assert_eq!(grevlex_cmp(&a, &b), std::cmp::Ordering::Greater);
    }

    #[test]
    fn test_grevlex_constant_vs_variable() {
        let constant: BTreeSet<u32> = BTreeSet::new(); // degree 0
        let var: BTreeSet<u32> = [0].into_iter().collect(); // degree 1
        assert_eq!(grevlex_cmp(&constant, &var), std::cmp::Ordering::Less);
    }

    #[test]
    fn test_leading_monomial_zero() {
        assert_eq!(leading_monomial(&Gf2Poly::zero()), None);
    }

    #[test]
    fn test_leading_monomial_single_var() {
        let p = Gf2Poly::variable(3);
        let lm = leading_monomial(&p).unwrap();
        assert_eq!(lm, [3].into_iter().collect::<BTreeSet<u32>>());
    }

    #[test]
    fn test_leading_monomial_picks_highest_degree() {
        // p = x0*x1 + x2 + 1
        let p = Gf2Poly::monomial(&[0, 1])
            .add(&Gf2Poly::variable(2))
            .add(&Gf2Poly::one());
        let lm = leading_monomial(&p).unwrap();
        // x0*x1 has degree 2, x2 has degree 1, 1 has degree 0.
        assert_eq!(lm, [0, 1].into_iter().collect::<BTreeSet<u32>>());
    }

    #[test]
    fn test_monomial_lcm() {
        let a: BTreeSet<u32> = [0, 1].into_iter().collect();
        let b: BTreeSet<u32> = [1, 2].into_iter().collect();
        let lcm = monomial_lcm(&a, &b);
        assert_eq!(lcm, [0, 1, 2].into_iter().collect::<BTreeSet<u32>>());
    }

    #[test]
    fn test_monomial_divides_yes() {
        let a: BTreeSet<u32> = [0, 1, 2].into_iter().collect();
        let b: BTreeSet<u32> = [0, 2].into_iter().collect();
        let q = monomial_divides(&a, &b).unwrap();
        assert_eq!(q, [1].into_iter().collect::<BTreeSet<u32>>());
    }

    #[test]
    fn test_monomial_divides_no() {
        let a: BTreeSet<u32> = [0, 1].into_iter().collect();
        let b: BTreeSet<u32> = [0, 2].into_iter().collect();
        assert!(monomial_divides(&a, &b).is_none());
    }

    #[test]
    fn test_s_polynomial_trivial() {
        // S(x0, x0) should be zero since LCMs match.
        let f = Gf2Poly::variable(0);
        let result = s_polynomial(&f, &f).unwrap();
        assert!(result.is_zero());
    }

    #[test]
    fn test_s_polynomial_disjoint() {
        // f = x0, g = x1
        // LCM = x0*x1, S(f,g) = x1*x0 + x0*x1 = 0 in GF(2)
        let f = Gf2Poly::variable(0);
        let g = Gf2Poly::variable(1);
        let result = s_polynomial(&f, &g).unwrap();
        assert!(result.is_zero());
    }

    #[test]
    fn test_s_polynomial_nontrivial() {
        // f = x0*x1 + x2, g = x0*x2 + x1
        // LM(f) = x0*x1, LM(g) = x0*x2
        // LCM = x0*x1*x2
        // S(f,g) = x2*(x0*x1 + x2) + x1*(x0*x2 + x1)
        //        = x0*x1*x2 + x2 + x0*x1*x2 + x1   (using x^2=x: x2^2=x2, x1^2=x1)
        //        = x1 + x2  (the x0*x1*x2 terms cancel)
        let f = Gf2Poly::monomial(&[0, 1]).add(&Gf2Poly::variable(2));
        let g = Gf2Poly::monomial(&[0, 2]).add(&Gf2Poly::variable(1));
        let result = s_polynomial(&f, &g).unwrap();
        let expected = Gf2Poly::variable(1).add(&Gf2Poly::variable(2));
        assert_eq!(result, expected);
    }

    #[test]
    fn test_multivariate_division_exact() {
        // f = x0*x1 + x0, divisors = [x0]
        // f / x0 = x1 + 1, remainder = 0
        let f = Gf2Poly::monomial(&[0, 1]).add(&Gf2Poly::variable(0));
        let divisors = vec![Gf2Poly::variable(0)];
        let (quotients, remainder) = multivariate_division(&f, &divisors);

        assert!(remainder.is_zero());
        let expected_q = Gf2Poly::variable(1).add(&Gf2Poly::one());
        assert_eq!(quotients[0], expected_q);
    }

    #[test]
    fn test_multivariate_division_with_remainder() {
        // f = x0*x1 + x2, divisors = [x0]
        // x1 * x0 + x2 -> quotient x1, remainder x2
        let f = Gf2Poly::monomial(&[0, 1]).add(&Gf2Poly::variable(2));
        let divisors = vec![Gf2Poly::variable(0)];
        let (quotients, remainder) = multivariate_division(&f, &divisors);

        assert_eq!(quotients[0], Gf2Poly::variable(1));
        assert_eq!(remainder, Gf2Poly::variable(2));
    }

    #[test]
    fn test_multivariate_division_zero_dividend() {
        let f = Gf2Poly::zero();
        let divisors = vec![Gf2Poly::variable(0)];
        let (quotients, remainder) = multivariate_division(&f, &divisors);
        assert!(quotients[0].is_zero());
        assert!(remainder.is_zero());
    }

    #[test]
    fn test_division_reconstructs_original() {
        // Verify: f = sum(q_i * d_i) + r
        let f = Gf2Poly::monomial(&[0, 1])
            .add(&Gf2Poly::monomial(&[0, 2]))
            .add(&Gf2Poly::variable(1))
            .add(&Gf2Poly::one());
        let divisors = vec![
            Gf2Poly::monomial(&[0, 1]).add(&Gf2Poly::one()),
            Gf2Poly::variable(2),
        ];
        let (quotients, remainder) = multivariate_division(&f, &divisors);

        let mut reconstructed = remainder;
        for (q, d) in quotients.iter().zip(divisors.iter()) {
            reconstructed = reconstructed.add(&q.mul(d));
        }
        assert_eq!(reconstructed, f);
    }
}
