// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use std::collections::BTreeMap;

use clean_kernel::{Expr, FVarId, Level};

use super::super::polynomial::gcd_u128;
use super::super::LinearConstraint;
use super::monomial::{cmp_monomials, multiply_monomials};

/// Configuration for Groebner basis computation.
#[derive(Debug, Clone)]
pub struct GroebnerConfig {
    /// Maximum total degree of basis elements kept in the basis.
    pub max_degree: usize,
    /// Maximum number of basis elements to keep.
    pub max_basis_size: usize,
    /// Maximum number of S-polynomial reductions to perform.
    pub max_reductions: usize,
}

impl Default for GroebnerConfig {
    fn default() -> Self {
        Self {
            max_degree: 4,
            max_basis_size: 50,
            max_reductions: 200,
        }
    }
}

/// Result of Groebner preprocessing.
pub struct GroebnerResult {
    /// Additional affine constraints derived from the equality ideal.
    pub linear_constraints: Vec<LinearConstraint>,
    /// Reserved for future non-negativity witnesses.
    pub nonnegativity_witnesses: Vec<LinearConstraint>,
}

pub(crate) type Monomial = Vec<(usize, u32)>;

/// Integer polynomial with sparse monomial storage.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IntPolynomial {
    pub(crate) terms: BTreeMap<Monomial, i128>,
}

impl IntPolynomial {
    pub fn zero() -> Self {
        Self {
            terms: BTreeMap::new(),
        }
    }

    pub fn constant(c: i128) -> Self {
        if c == 0 {
            return Self::zero();
        }
        let mut terms = BTreeMap::new();
        terms.insert(vec![], c);
        Self { terms }
    }

    pub fn var(idx: usize) -> Self {
        let mut terms = BTreeMap::new();
        terms.insert(vec![(idx, 1)], 1);
        Self { terms }
    }

    pub fn from_terms<I>(terms: I) -> Self
    where
        I: IntoIterator<Item = (Monomial, i128)>,
    {
        let mut poly = Self::zero();
        for (mono, coeff) in terms {
            poly.add_term(mono, coeff);
        }
        poly
    }

    pub fn is_zero(&self) -> bool {
        self.terms.is_empty()
    }

    pub fn degree(&self) -> usize {
        self.terms
            .keys()
            .map(|mono| {
                mono.iter()
                    .map(|(_, exp)| usize::try_from(*exp).unwrap_or(usize::MAX))
                    .sum()
            })
            .max()
            .unwrap_or(0)
    }

    pub fn add(&self, other: &Self) -> Self {
        let mut result = self.clone();
        for (mono, coeff) in &other.terms {
            result.add_term(mono.clone(), *coeff);
        }
        result
    }

    pub fn sub(&self, other: &Self) -> Self {
        let mut result = self.clone();
        for (mono, coeff) in &other.terms {
            result.add_term(mono.clone(), -*coeff);
        }
        result
    }

    pub fn negate(&self) -> Self {
        Self::from_terms(
            self.terms
                .iter()
                .map(|(mono, coeff)| (mono.clone(), -*coeff)),
        )
    }

    pub fn mul(&self, other: &Self) -> Self {
        let mut result = Self::zero();
        for (lhs_mono, lhs_coeff) in &self.terms {
            for (rhs_mono, rhs_coeff) in &other.terms {
                result.add_term(
                    multiply_monomials(lhs_mono, rhs_mono),
                    lhs_coeff.saturating_mul(*rhs_coeff),
                );
            }
        }
        result
    }

    pub(super) fn add_term(&mut self, mono: Monomial, coeff: i128) {
        if coeff == 0 {
            return;
        }
        let entry = self.terms.entry(mono.clone()).or_insert(0);
        *entry = entry.saturating_add(coeff);
        if *entry == 0 {
            self.terms.remove(&mono);
        }
    }

    pub(super) fn leading_term(&self) -> Option<(&Monomial, i128)> {
        self.terms
            .iter()
            .max_by(|(lhs_mono, _), (rhs_mono, _)| cmp_monomials(lhs_mono, rhs_mono))
            .map(|(mono, coeff)| (mono, *coeff))
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) struct Rational {
    pub(super) num: i128,
    pub(super) den: i128,
}

impl Rational {
    pub(super) fn new(num: i128, den: i128) -> Self {
        debug_assert!(den != 0);
        if num == 0 {
            return Self { num: 0, den: 1 };
        }

        let mut num = num;
        let mut den = den;
        if den < 0 {
            num = -num;
            den = -den;
        }
        let gcd = gcd_i128(num, den);
        Self {
            num: num / gcd,
            den: den / gcd,
        }
    }

    pub(super) fn one() -> Self {
        Self { num: 1, den: 1 }
    }

    pub(super) fn is_zero(self) -> bool {
        self.num == 0
    }

    pub(super) fn add(self, other: Self) -> Self {
        Self::new(
            self.num
                .saturating_mul(other.den)
                .saturating_add(other.num.saturating_mul(self.den)),
            self.den.saturating_mul(other.den),
        )
    }

    pub(super) fn mul(self, other: Self) -> Self {
        Self::new(
            self.num.saturating_mul(other.num),
            self.den.saturating_mul(other.den),
        )
    }

    pub(super) fn div(self, other: Self) -> Self {
        debug_assert!(!other.is_zero());
        Self::new(
            self.num.saturating_mul(other.den),
            self.den.saturating_mul(other.num),
        )
    }

    pub(super) fn neg(self) -> Self {
        Self {
            num: -self.num,
            den: self.den,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct RationalPolynomial {
    pub(super) terms: BTreeMap<Monomial, Rational>,
}

impl RationalPolynomial {
    pub(super) fn zero() -> Self {
        Self {
            terms: BTreeMap::new(),
        }
    }

    pub(super) fn constant(coeff: Rational) -> Self {
        if coeff.is_zero() {
            return Self::zero();
        }

        let mut terms = BTreeMap::new();
        terms.insert(vec![], coeff);
        Self { terms }
    }

    pub(super) fn from_integer(poly: &IntPolynomial) -> Self {
        let mut result = Self::zero();
        for (mono, coeff) in &poly.terms {
            result.add_term(mono.clone(), Rational::new(*coeff, 1));
        }
        result
    }

    pub(super) fn is_zero(&self) -> bool {
        self.terms.is_empty()
    }

    pub(super) fn degree(&self) -> usize {
        self.terms
            .keys()
            .map(|mono| {
                mono.iter()
                    .map(|(_, exp)| usize::try_from(*exp).unwrap_or(usize::MAX))
                    .sum()
            })
            .max()
            .unwrap_or(0)
    }

    pub(super) fn leading_term(&self) -> Option<(&Monomial, Rational)> {
        self.terms
            .iter()
            .max_by(|(lhs_mono, _), (rhs_mono, _)| cmp_monomials(lhs_mono, rhs_mono))
            .map(|(mono, coeff)| (mono, *coeff))
    }

    pub(super) fn add(&self, other: &Self) -> Self {
        let mut result = self.clone();
        for (mono, coeff) in &other.terms {
            result.add_term(mono.clone(), *coeff);
        }
        result
    }

    pub(super) fn sub(&self, other: &Self) -> Self {
        let mut result = self.clone();
        for (mono, coeff) in &other.terms {
            result.add_term(mono.clone(), coeff.neg());
        }
        result
    }

    pub(super) fn mul(&self, other: &Self) -> Self {
        let mut result = Self::zero();
        for (lhs_mono, lhs_coeff) in &self.terms {
            for (rhs_mono, rhs_coeff) in &other.terms {
                result.add_term(
                    multiply_monomials(lhs_mono, rhs_mono),
                    lhs_coeff.mul(*rhs_coeff),
                );
            }
        }
        result
    }

    pub(super) fn as_constant(&self) -> Option<Rational> {
        match self.terms.len() {
            0 => Some(Rational::new(0, 1)),
            1 => self.terms.get(&vec![]).copied(),
            _ => None,
        }
    }

    pub(super) fn add_term(&mut self, mono: Monomial, coeff: Rational) {
        if coeff.is_zero() {
            return;
        }
        let entry = self
            .terms
            .entry(mono.clone())
            .or_insert(Rational::new(0, 1));
        *entry = entry.add(coeff);
        if entry.is_zero() {
            self.terms.remove(&mono);
        }
    }

    pub(super) fn mul_term(&self, mono: &Monomial, coeff: Rational) -> Self {
        let mut result = Self::zero();
        for (term_mono, term_coeff) in &self.terms {
            result.add_term(multiply_monomials(term_mono, mono), term_coeff.mul(coeff));
        }
        result
    }

    pub(super) fn monic(&self) -> Self {
        let Some((_, leading_coeff)) = self.leading_term() else {
            return self.clone();
        };
        if leading_coeff == Rational::one() {
            return self.clone();
        }

        let inv = Rational::one().div(leading_coeff);
        let mut result = Self::zero();
        for (mono, coeff) in &self.terms {
            result.add_term(mono.clone(), coeff.mul(inv));
        }
        result
    }

    pub(super) fn to_primitive_integer(&self) -> IntPolynomial {
        if self.is_zero() {
            return IntPolynomial::zero();
        }

        let mut lcm_den = 1i128;
        for coeff in self.terms.values() {
            lcm_den = lcm_i128(lcm_den, coeff.den);
        }

        let mut integer_terms = BTreeMap::new();
        for (mono, coeff) in &self.terms {
            let scale = lcm_den / coeff.den;
            integer_terms.insert(mono.clone(), coeff.num.saturating_mul(scale));
        }

        let content = integer_terms
            .values()
            .fold(0i128, |acc, coeff| gcd_i128(acc, *coeff));
        let content = if content == 0 { 1 } else { content };

        let mut poly = IntPolynomial::zero();
        for (mono, coeff) in integer_terms {
            poly.add_term(mono, coeff / content);
        }

        if let Some((_, leading_coeff)) = poly.leading_term() {
            if leading_coeff < 0 {
                return poly.negate();
            }
        }
        poly
    }
}

#[derive(Clone, Copy)]
pub(super) enum RelationKind {
    Eq,
    Le,
    Lt,
}

#[derive(Clone)]
pub(super) struct PolynomialRelation {
    pub(super) kind: RelationKind,
    pub(super) polynomial: IntPolynomial,
}

impl PolynomialRelation {
    pub(super) fn negated_goal_relation(&self) -> Option<Self> {
        match self.kind {
            RelationKind::Eq => None,
            RelationKind::Le => Some(Self {
                kind: RelationKind::Lt,
                polynomial: self.polynomial.negate(),
            }),
            RelationKind::Lt => Some(Self {
                kind: RelationKind::Le,
                polynomial: self.polynomial.negate(),
            }),
        }
    }
}

#[derive(Debug, Clone)]
pub(super) struct BasisElement {
    pub(super) poly: RationalPolynomial,
    pub(super) combination: Vec<RationalPolynomial>,
}

#[derive(Debug, Clone)]
pub(super) struct EqualityHypothesis {
    pub(super) fvar: FVarId,
    pub(super) lhs: Expr,
    pub(super) rhs: Expr,
}

#[derive(Debug, Clone)]
pub(super) struct EqAcc {
    pub(super) alpha: Expr,
    pub(super) u: Level,
    pub(super) lhs: Expr,
    pub(super) rhs: Expr,
    pub(super) proof: Expr,
}

fn gcd_i128(lhs: i128, rhs: i128) -> i128 {
    let lhs = lhs.unsigned_abs();
    let rhs = rhs.unsigned_abs();
    i128::try_from(gcd_u128(lhs, rhs)).unwrap_or(i128::MAX)
}

fn lcm_i128(lhs: i128, rhs: i128) -> i128 {
    if lhs == 0 || rhs == 0 {
        return 0;
    }
    let gcd = gcd_i128(lhs, rhs);
    lhs / gcd * rhs
}
