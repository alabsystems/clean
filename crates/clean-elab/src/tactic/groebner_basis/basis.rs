// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use std::cmp::Ordering;

use super::monomial::{cmp_monomials, lcm_monomials, monomial_quotient};
use super::types::{BasisElement, GroebnerConfig, IntPolynomial, Rational, RationalPolynomial};

/// Reduced Groebner basis plus reduction operations over integer polynomials.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct GBasis {
    polynomials: Vec<IntPolynomial>,
}

impl GBasis {
    pub(crate) fn compute(generators: &[IntPolynomial], config: &GroebnerConfig) -> Self {
        Self {
            polynomials: buchberger_basis(generators, config),
        }
    }

    pub(crate) fn polynomials(&self) -> &[IntPolynomial] {
        &self.polynomials
    }

    pub(crate) fn reduce(&self, poly: &IntPolynomial) -> IntPolynomial {
        reduce_by_basis(poly, &self.polynomials)
    }
}

/// Compute a bounded Buchberger basis for the given integer generators.
pub(crate) fn buchberger_basis(
    generators: &[IntPolynomial],
    config: &GroebnerConfig,
) -> Vec<IntPolynomial> {
    let mut reduced_basis: Vec<_> = buchberger_basis_with_combinations(generators, config)
        .into_iter()
        .map(|elt| elt.poly)
        .collect();
    reduced_basis = interreduce_basis(reduced_basis);
    reduced_basis.sort_by(cmp_rational_polynomials);
    reduced_basis
        .into_iter()
        .map(|poly| poly.to_primitive_integer())
        .collect()
}

/// Reduce an integer polynomial by the supplied basis and return a primitive
/// integer normal form.
pub(crate) fn reduce_by_basis(poly: &IntPolynomial, basis: &[IntPolynomial]) -> IntPolynomial {
    if poly.is_zero() {
        return IntPolynomial::zero();
    }

    let rational_poly = RationalPolynomial::from_integer(poly);
    let rational_basis: Vec<_> = basis
        .iter()
        .filter(|basis_poly| !basis_poly.is_zero())
        .map(RationalPolynomial::from_integer)
        .map(|basis_poly| basis_poly.monic())
        .collect();

    reduce_rational_by_basis(&rational_poly, &rational_basis).to_primitive_integer()
}

pub(super) fn buchberger_basis_with_combinations(
    generators: &[IntPolynomial],
    config: &GroebnerConfig,
) -> Vec<BasisElement> {
    let mut basis = Vec::new();
    let width = generators.len();

    for (idx, generator) in generators.iter().enumerate() {
        if generator.is_zero() || generator.degree() > config.max_degree {
            continue;
        }

        let rational = RationalPolynomial::from_integer(generator);
        let Some((_, leading_coeff)) = rational.leading_term() else {
            continue;
        };
        let scaling = Rational::one().div(leading_coeff);

        let mut combination = zero_combination(width);
        combination[idx] = RationalPolynomial::constant(scaling);
        basis.push(BasisElement {
            poly: rational.monic(),
            combination,
        });
    }

    if basis.len() > config.max_basis_size {
        basis.truncate(config.max_basis_size);
    }

    let mut pairs = Vec::new();
    for i in 0..basis.len() {
        for j in (i + 1)..basis.len() {
            pairs.push((i, j));
        }
    }

    let mut reductions = 0usize;
    while let Some((i, j)) = pairs.pop() {
        if reductions >= config.max_reductions || basis.len() >= config.max_basis_size {
            break;
        }
        reductions += 1;

        let (s_poly, s_combo) = s_polynomial_with_combination(&basis[i], &basis[j]);
        let basis_polys: Vec<_> = basis.iter().map(|elt| elt.poly.clone()).collect();
        let (reduced, quotient_basis) =
            reduce_rational_by_basis_with_quotients(&s_poly, &basis_polys);
        if reduced.is_zero() || reduced.degree() > config.max_degree {
            continue;
        }

        let quotient_combo = compose_basis_quotients(&quotient_basis, &basis, width);
        let reduced_combo = sub_combinations(&s_combo, &quotient_combo);
        let Some((_, leading_coeff)) = reduced.leading_term() else {
            continue;
        };
        let scaling = Rational::one().div(leading_coeff);
        let reduced = reduced.monic();
        let reduced_combo = scale_combination(&reduced_combo, &vec![], scaling);

        if basis.iter().any(|elt| elt.poly == reduced) {
            continue;
        }

        let new_idx = basis.len();
        basis.push(BasisElement {
            poly: reduced,
            combination: reduced_combo,
        });
        for existing in 0..new_idx {
            pairs.push((existing, new_idx));
        }
    }

    basis.sort_by(|lhs, rhs| cmp_rational_polynomials(&lhs.poly, &rhs.poly));
    basis
}

pub(super) fn reduce_rational_by_basis_with_quotients(
    poly: &RationalPolynomial,
    basis: &[RationalPolynomial],
) -> (RationalPolynomial, Vec<RationalPolynomial>) {
    let mut work = poly.clone();
    let mut remainder = RationalPolynomial::zero();
    let mut quotients = vec![RationalPolynomial::zero(); basis.len()];

    while let Some((work_mono, work_coeff)) = work
        .leading_term()
        .map(|(mono, coeff)| (mono.clone(), coeff))
    {
        let mut reduced = false;

        for (basis_idx, basis_poly) in basis.iter().enumerate() {
            let Some((basis_mono, basis_coeff)) = basis_poly.leading_term() else {
                continue;
            };
            let Some(quotient_mono) = monomial_quotient(&work_mono, basis_mono) else {
                continue;
            };

            let factor = work_coeff.div(basis_coeff);
            quotients[basis_idx].add_term(quotient_mono.clone(), factor);
            work = work.sub(&basis_poly.mul_term(&quotient_mono, factor));
            reduced = true;
            break;
        }

        if reduced {
            continue;
        }

        let mut leading_only = RationalPolynomial::zero();
        leading_only.add_term(work_mono.clone(), work_coeff);
        remainder = remainder.add(&leading_only);
        work = work.sub(&leading_only);
    }

    (remainder, quotients)
}

pub(super) fn compose_basis_quotients(
    quotient_basis: &[RationalPolynomial],
    basis: &[BasisElement],
    width: usize,
) -> Vec<RationalPolynomial> {
    let mut result = zero_combination(width);

    for (quotient, basis_element) in quotient_basis.iter().zip(basis) {
        if quotient.is_zero() {
            continue;
        }

        for (result_poly, basis_combo_poly) in result.iter_mut().zip(&basis_element.combination) {
            *result_poly = result_poly.add(&quotient.mul(basis_combo_poly));
        }
    }

    result
}

fn zero_combination(width: usize) -> Vec<RationalPolynomial> {
    vec![RationalPolynomial::zero(); width]
}

fn scale_combination(
    combination: &[RationalPolynomial],
    mono: &super::types::Monomial,
    coeff: Rational,
) -> Vec<RationalPolynomial> {
    combination
        .iter()
        .map(|poly| poly.mul_term(mono, coeff))
        .collect()
}

fn sub_combinations(
    lhs: &[RationalPolynomial],
    rhs: &[RationalPolynomial],
) -> Vec<RationalPolynomial> {
    lhs.iter()
        .zip(rhs)
        .map(|(lhs_poly, rhs_poly)| lhs_poly.sub(rhs_poly))
        .collect()
}

fn interreduce_basis(mut basis: Vec<RationalPolynomial>) -> Vec<RationalPolynomial> {
    let mut reduced = Vec::new();
    while !basis.is_empty() {
        let current = basis.remove(0);
        let reduced_poly = reduce_rational_by_basis(&current, &basis);
        if reduced_poly.is_zero() {
            continue;
        }
        let reduced_poly = reduced_poly.monic();
        if !reduced.contains(&reduced_poly) {
            reduced.push(reduced_poly);
        }
    }
    reduced
}

fn s_polynomial_with_combination(
    lhs: &BasisElement,
    rhs: &BasisElement,
) -> (RationalPolynomial, Vec<RationalPolynomial>) {
    let Some((lhs_mono, lhs_coeff)) = lhs.poly.leading_term() else {
        return (
            RationalPolynomial::zero(),
            zero_combination(lhs.combination.len()),
        );
    };
    let Some((rhs_mono, rhs_coeff)) = rhs.poly.leading_term() else {
        return (
            RationalPolynomial::zero(),
            zero_combination(lhs.combination.len()),
        );
    };

    let lcm = lcm_monomials(lhs_mono, rhs_mono);
    let lhs_scale = monomial_quotient(&lcm, lhs_mono).unwrap_or_default();
    let rhs_scale = monomial_quotient(&lcm, rhs_mono).unwrap_or_default();

    let lhs_factor = Rational::one().div(lhs_coeff);
    let rhs_factor = Rational::one().div(rhs_coeff);

    let s_poly = lhs
        .poly
        .mul_term(&lhs_scale, lhs_factor)
        .sub(&rhs.poly.mul_term(&rhs_scale, rhs_factor));
    let lhs_combo = scale_combination(&lhs.combination, &lhs_scale, lhs_factor);
    let rhs_combo = scale_combination(&rhs.combination, &rhs_scale, rhs_factor);
    (s_poly, sub_combinations(&lhs_combo, &rhs_combo))
}

fn reduce_rational_by_basis(
    poly: &RationalPolynomial,
    basis: &[RationalPolynomial],
) -> RationalPolynomial {
    reduce_rational_by_basis_with_quotients(poly, basis).0
}

fn cmp_rational_polynomials(lhs: &RationalPolynomial, rhs: &RationalPolynomial) -> Ordering {
    match (lhs.leading_term(), rhs.leading_term()) {
        (Some((lhs_mono, _)), Some((rhs_mono, _))) => cmp_monomials(lhs_mono, rhs_mono),
        (Some(_), None) => Ordering::Greater,
        (None, Some(_)) => Ordering::Less,
        (None, None) => Ordering::Equal,
    }
    .then(lhs.terms.len().cmp(&rhs.terms.len()))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn x() -> IntPolynomial {
        IntPolynomial::var(0)
    }

    fn y() -> IntPolynomial {
        IntPolynomial::var(1)
    }

    #[test]
    fn test_int_polynomial_add_and_mul_normalize_terms() {
        let poly = IntPolynomial::from_terms([(vec![(0, 1)], 2), (vec![(0, 1)], -1)]);
        assert_eq!(poly, IntPolynomial::var(0));

        let product = x()
            .add(&IntPolynomial::constant(1))
            .mul(&x().sub(&IntPolynomial::constant(1)));
        let expected = x().mul(&x()).sub(&IntPolynomial::constant(1));
        assert_eq!(product, expected);
    }

    #[test]
    fn test_gbasis_reduce_matches_helper() {
        let generators = vec![
            x().mul(&y()).sub(&IntPolynomial::constant(1)),
            y().sub(&IntPolynomial::constant(1)),
        ];
        let basis = GBasis::compute(&generators, &GroebnerConfig::default());
        let goal = x().sub(&IntPolynomial::constant(1));

        assert!(basis.reduce(&goal).is_zero());
        assert_eq!(
            basis.reduce(&goal),
            reduce_by_basis(&goal, basis.polynomials())
        );
    }

    #[test]
    fn test_buchberger_derives_x_minus_one_from_xy_minus_one_and_y_minus_one() {
        let generators = vec![
            x().mul(&y()).sub(&IntPolynomial::constant(1)),
            y().sub(&IntPolynomial::constant(1)),
        ];
        let basis = buchberger_basis(&generators, &GroebnerConfig::default());
        let remainder = reduce_by_basis(&x().sub(&IntPolynomial::constant(1)), &basis);

        assert!(
            remainder.is_zero(),
            "x - 1 should reduce to 0 modulo <xy - 1, y - 1>, basis={basis:?}, remainder={remainder:?}"
        );
    }

    #[test]
    fn test_buchberger_derives_x_from_xy_and_xy_plus_x() {
        let xy = x().mul(&y());
        let generators = vec![xy.clone(), xy.add(&x())];
        let basis = buchberger_basis(&generators, &GroebnerConfig::default());
        let remainder = reduce_by_basis(&x(), &basis);

        assert!(
            remainder.is_zero(),
            "x should reduce to 0 modulo <xy, xy + x>, basis={basis:?}, remainder={remainder:?}"
        );
    }

    #[test]
    fn test_buchberger_reduces_two_y_sq_minus_one_for_circle_diagonal() {
        let x_sq = x().mul(&x());
        let y_sq = y().mul(&y());
        let generators = vec![
            x_sq.add(&y_sq).sub(&IntPolynomial::constant(1)),
            x().sub(&y()),
        ];
        let goal = IntPolynomial::constant(2)
            .mul(&y_sq)
            .sub(&IntPolynomial::constant(1));
        let basis = buchberger_basis(&generators, &GroebnerConfig::default());
        let remainder = reduce_by_basis(&goal, &basis);

        assert!(
            remainder.is_zero(),
            "2*y^2 - 1 should reduce to 0 modulo <x^2 + y^2 - 1, x - y>, basis={basis:?}, remainder={remainder:?}"
        );
    }
}
