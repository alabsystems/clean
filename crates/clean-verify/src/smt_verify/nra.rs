// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Non-linear arithmetic (NRA/NIA) certificate checker.
//!
//! This module checks algebraic certificates for SMT non-linear arithmetic
//! lemmas. For inequality reasoning, it validates Positivstellensatz
//! refutations: SOS multipliers `s_i` over premises `p_i >= 0` must satisfy
//! `sum_i s_i * p_i = -1`. For equality reasoning, it validates ideal
//! membership witnesses showing a target polynomial lies in the ideal generated
//! by the input equalities. All arithmetic is exact over `Rational64`.

// 2026-07-31: the `pub(crate)` items in this module are exercised only by its
// own `#[cfg(test)]` tests, so only the non-test `lib` build sees them as dead.
// Scoped to `not(test)` on purpose: the `lib test` build still enforces
// `dead_code` in full, so an item with no caller anywhere still fails the gate.
#![cfg_attr(not(test), allow(dead_code))]

use std::collections::BTreeMap;

use num_rational::Rational64;

use super::dag::{SmtProofDag, SmtStepId, SmtTermId};
use super::trust::{StepTrustLevel, StepVerdict};

/// Name of this checker for trust ledger attribution.
pub(crate) const CHECKER_NAME: &str = "nra";

/// A monomial represented as a sorted list of `(variable, exponent)` pairs.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Monomial(pub(crate) Vec<(String, u32)>);

impl Monomial {
    /// Construct a normalized monomial.
    #[must_use]
    pub fn new(factors: Vec<(String, u32)>) -> Self {
        let mut merged: BTreeMap<String, u32> = BTreeMap::new();
        for (var, exp) in factors {
            if exp == 0 {
                continue;
            }
            let next = merged.get(&var).copied().unwrap_or(0).saturating_add(exp);
            merged.insert(var, next);
        }
        Self(merged.into_iter().collect())
    }

    /// The constant monomial `1`.
    #[must_use]
    pub fn one() -> Self {
        Self(Vec::new())
    }

    /// A single variable monomial with exponent 1.
    #[must_use]
    pub fn variable(name: impl Into<String>) -> Self {
        Self::new(vec![(name.into(), 1)])
    }

    /// Total degree.
    #[must_use]
    pub fn degree(&self) -> u32 {
        self.0
            .iter()
            .fold(0_u32, |acc, (_, exp)| acc.saturating_add(*exp))
    }

    /// Monomial multiplication.
    #[must_use]
    pub fn mul(&self, other: &Self) -> Self {
        let mut factors = self.0.clone();
        factors.extend(other.0.clone());
        Self::new(factors)
    }
}

/// A sparse polynomial represented as a sum of coefficient-monomial terms.
#[derive(Clone, Debug, PartialEq)]
pub struct Polynomial(pub(crate) Vec<(Rational64, Monomial)>);

impl Polynomial {
    /// Construct a normalized polynomial.
    #[must_use]
    pub fn new(terms: Vec<(Rational64, Monomial)>) -> Self {
        let zero = Rational64::from_integer(0);
        let mut combined: BTreeMap<Monomial, Rational64> = BTreeMap::new();

        for (coeff, monomial) in terms {
            if coeff == zero {
                continue;
            }
            let monomial = Monomial::new(monomial.0);
            combined
                .entry(monomial)
                .and_modify(|current| *current += coeff)
                .or_insert(coeff);
        }

        let normalized = combined
            .into_iter()
            .filter_map(|(monomial, coeff)| {
                if coeff == zero {
                    None
                } else {
                    Some((coeff, monomial))
                }
            })
            .collect();

        Self(normalized)
    }

    /// The zero polynomial.
    #[must_use]
    pub fn zero() -> Self {
        Self(Vec::new())
    }

    /// A constant polynomial.
    #[must_use]
    pub fn constant(value: Rational64) -> Self {
        if value == Rational64::from_integer(0) {
            Self::zero()
        } else {
            Self::new(vec![(value, Monomial::one())])
        }
    }

    /// A single-term polynomial.
    #[must_use]
    pub fn term(coeff: Rational64, monomial: Monomial) -> Self {
        Self::new(vec![(coeff, monomial)])
    }

    /// Polynomial addition.
    #[must_use]
    pub fn add(&self, other: &Self) -> Self {
        let mut terms = self.0.clone();
        terms.extend(other.0.clone());
        Self::new(terms)
    }

    /// Polynomial subtraction.
    #[must_use]
    pub fn sub(&self, other: &Self) -> Self {
        let mut terms = self.0.clone();
        terms.extend(
            other
                .0
                .iter()
                .map(|(coeff, monomial)| (-*coeff, monomial.clone())),
        );
        Self::new(terms)
    }

    /// Polynomial multiplication.
    #[must_use]
    pub fn mul(&self, other: &Self) -> Self {
        let mut terms = Vec::new();
        for (left_coeff, left_monomial) in &self.0 {
            for (right_coeff, right_monomial) in &other.0 {
                terms.push((
                    *left_coeff * *right_coeff,
                    left_monomial.mul(right_monomial),
                ));
            }
        }
        Self::new(terms)
    }

    /// Evaluate the polynomial at a variable assignment.
    #[must_use]
    pub fn evaluate(&self, assignment: &BTreeMap<String, Rational64>) -> Option<Rational64> {
        let mut total = Rational64::from_integer(0);
        for (coeff, monomial) in &self.0 {
            let mut monomial_value = Rational64::from_integer(1);
            for (var, exp) in &monomial.0 {
                let value = assignment.get(var)?;
                monomial_value *= rational_pow(value, *exp);
            }
            total += *coeff * monomial_value;
        }
        Some(total)
    }

    /// Total degree of the polynomial.
    #[must_use]
    pub fn degree(&self) -> u32 {
        self.0
            .iter()
            .map(|(_, monomial)| monomial.degree())
            .max()
            .unwrap_or(0)
    }

    /// True when the polynomial has no non-zero terms.
    #[must_use]
    pub fn is_zero(&self) -> bool {
        self.0.is_empty()
    }
}

/// SOS certificate `m(x)^T G m(x)`.
#[derive(Clone, Debug, PartialEq)]
pub struct SosCertificate {
    /// Symmetric Gram matrix.
    pub gram_matrix: Vec<Vec<Rational64>>,
    /// Monomial basis vector `m(x)`.
    pub basis: Vec<Monomial>,
}

/// Positivstellensatz infeasibility certificate.
#[derive(Clone, Debug, PartialEq)]
pub struct PsatzCertificate {
    /// Premise polynomials `p_i >= 0`.
    pub pi: Vec<Polynomial>,
    /// SOS multipliers `s_i`.
    pub si: Vec<SosCertificate>,
}

/// Witness that `f` lies in the ideal generated by `g_1, ..., g_m`.
#[derive(Clone, Debug, PartialEq)]
pub struct IdealMembershipWitness {
    /// Target polynomial.
    pub(crate) f: Polynomial,
    /// Ideal generators.
    pub(crate) generators: Vec<Polynomial>,
    /// Quotient polynomials.
    pub(crate) quotients: Vec<Polynomial>,
}

/// Certificate payload for an NRA/NIA theory lemma.
#[derive(Clone, Debug, PartialEq)]
pub enum NraWitness {
    Psatz(PsatzCertificate),
    IdealMembership(IdealMembershipWitness),
    Structural,
}

/// Verify an SOS certificate.
#[must_use]
pub fn verify_sos(cert: &SosCertificate) -> bool {
    sos_polynomial(cert).is_some()
}

/// Verify a Positivstellensatz certificate.
#[must_use]
pub fn check_psatz(cert: &PsatzCertificate) -> bool {
    if cert.pi.len() != cert.si.len() {
        return false;
    }

    let mut combination = Polynomial::zero();
    for (premise, multiplier) in cert.pi.iter().zip(&cert.si) {
        let sos_poly = match sos_polynomial(multiplier) {
            Some(poly) => poly,
            None => return false,
        };
        combination = combination.add(&sos_poly.mul(premise));
    }

    combination
        .add(&Polynomial::constant(Rational64::from_integer(1)))
        .is_zero()
}

/// Verify ideal membership by exact polynomial arithmetic.
#[must_use]
pub(crate) fn verify_ideal_membership(witness: &IdealMembershipWitness) -> bool {
    if witness.generators.len() != witness.quotients.len() {
        return false;
    }

    let mut sum = Polynomial::zero();
    for (generator, quotient) in witness.generators.iter().zip(&witness.quotients) {
        sum = sum.add(&quotient.mul(generator));
    }

    sum == Polynomial::new(witness.f.0.clone())
}

/// Check an NRA/NIA theory lemma from the SMT proof DAG.
#[must_use]
pub(crate) fn check_nra_lemma(
    dag: &SmtProofDag,
    step_id: SmtStepId,
    clause: &[SmtTermId],
    witness: &NraWitness,
) -> StepVerdict {
    if dag.step(step_id).is_none() {
        return fail(step_id, "nra: missing proof step");
    }

    if clause.is_empty() {
        return fail(step_id, "nra: empty clause");
    }

    if let Some(expected_clause) = dag.step_clause(step_id) {
        if expected_clause != clause {
            return fail(step_id, "nra: clause does not match proof DAG");
        }
    }

    match witness {
        NraWitness::Psatz(cert) => {
            if check_psatz(cert) {
                ok(step_id)
            } else {
                fail(step_id, "nra: invalid Positivstellensatz certificate")
            }
        }
        NraWitness::IdealMembership(witness) => {
            if verify_ideal_membership(witness) {
                ok(step_id)
            } else {
                fail(step_id, "nra: invalid ideal-membership witness")
            }
        }
        NraWitness::Structural => StepVerdict {
            step_id,
            trust_level: StepTrustLevel::StructurallyAccepted,
            checker: CHECKER_NAME,
            detail: Some("nra: structurally accepted".to_string()),
        },
    }
}

pub(super) fn sos_polynomial(cert: &SosCertificate) -> Option<Polynomial> {
    let dimension = cert.basis.len();
    if cert.gram_matrix.len() != dimension {
        return None;
    }
    if cert.gram_matrix.iter().any(|row| row.len() != dimension) {
        return None;
    }
    if !is_symmetric(&cert.gram_matrix) {
        return None;
    }
    if !is_psd_gram_matrix(&cert.gram_matrix) {
        return None;
    }

    let zero = Rational64::from_integer(0);
    let mut terms = Vec::new();
    for i in 0..dimension {
        for j in 0..dimension {
            let coeff = cert.gram_matrix[i][j];
            if coeff == zero {
                continue;
            }
            terms.push((coeff, cert.basis[i].mul(&cert.basis[j])));
        }
    }
    Some(Polynomial::new(terms))
}

fn is_symmetric(matrix: &[Vec<Rational64>]) -> bool {
    // Indices `i` and `j` access transposed positions `matrix[i][j]` and
    // `matrix[j][i]`; iterator-based rewrites cannot express this.
    #[allow(clippy::needless_range_loop)]
    for i in 0..matrix.len() {
        for j in 0..matrix.len() {
            if matrix[i][j] != matrix[j][i] {
                return false;
            }
        }
    }
    true
}

/// Exact LDL-style PSD check for symmetric rational matrices.
fn is_psd_gram_matrix(matrix: &[Vec<Rational64>]) -> bool {
    let n = matrix.len();
    if matrix.iter().any(|row| row.len() != n) {
        return false;
    }
    if !is_symmetric(matrix) {
        return false;
    }

    let zero = Rational64::from_integer(0);
    let one = Rational64::from_integer(1);
    let mut l = vec![vec![zero; n]; n];
    let mut d = vec![zero; n];

    for k in 0..n {
        let mut diag = matrix[k][k];
        for j in 0..k {
            diag -= l[k][j] * l[k][j] * d[j];
        }
        if diag < zero {
            return false;
        }

        d[k] = diag;
        l[k][k] = one;

        for i in (k + 1)..n {
            let mut value = matrix[i][k];
            for j in 0..k {
                value -= l[i][j] * l[k][j] * d[j];
            }
            if d[k] == zero {
                if value != zero {
                    return false;
                }
                l[i][k] = zero;
            } else {
                l[i][k] = value / d[k];
            }
        }
    }

    true
}

fn rational_pow(base: &Rational64, mut exp: u32) -> Rational64 {
    let mut result = Rational64::from_integer(1);
    let mut factor = *base;
    while exp > 0 {
        if exp % 2 == 1 {
            result *= factor;
        }
        exp /= 2;
        if exp > 0 {
            factor = factor * factor;
        }
    }
    result
}

fn ok(step_id: SmtStepId) -> StepVerdict {
    StepVerdict {
        step_id,
        trust_level: StepTrustLevel::KernelVerified,
        checker: CHECKER_NAME,
        detail: None,
    }
}

fn fail(step_id: SmtStepId, reason: &str) -> StepVerdict {
    StepVerdict {
        step_id,
        trust_level: StepTrustLevel::Trusted,
        checker: CHECKER_NAME,
        detail: Some(reason.to_string()),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::smt_verify::dag::{SmtProofDag, SmtProofStep, SmtTerm};
    use crate::smt_verify::trust::StepTrustLevel;

    fn rat(n: i64) -> Rational64 {
        Rational64::from_integer(n)
    }

    fn monomial(vars: Vec<(&str, u32)>) -> Monomial {
        Monomial::new(vars.into_iter().map(|(v, e)| (v.to_string(), e)).collect())
    }

    fn poly(terms: Vec<(i64, Vec<(&str, u32)>)>) -> Polynomial {
        Polynomial::new(
            terms
                .into_iter()
                .map(|(coeff, vars)| (rat(coeff), monomial(vars)))
                .collect(),
        )
    }

    fn assignment(entries: Vec<(&str, i64)>) -> BTreeMap<String, Rational64> {
        entries
            .into_iter()
            .map(|(name, value)| (name.to_string(), rat(value)))
            .collect()
    }

    fn sos_constant_one() -> SosCertificate {
        SosCertificate {
            gram_matrix: vec![vec![rat(1)]],
            basis: vec![Monomial::one()],
        }
    }

    #[test]
    fn test_monomial_ordering() {
        let m = Monomial::new(vec![
            ("z".to_string(), 1),
            ("x".to_string(), 2),
            ("y".to_string(), 3),
        ]);
        assert_eq!(
            m,
            Monomial(vec![
                ("x".to_string(), 2),
                ("y".to_string(), 3),
                ("z".to_string(), 1),
            ])
        );
    }

    #[test]
    fn test_monomial_degree() {
        let m = monomial(vec![("x", 2), ("y", 3), ("z", 1)]);
        assert_eq!(m.degree(), 6);
    }

    #[test]
    fn test_polynomial_add() {
        let left = poly(vec![(2, vec![("x", 1)]), (1, vec![])]);
        let right = poly(vec![(3, vec![("x", 1)]), (-1, vec![])]);
        let expected = poly(vec![(5, vec![("x", 1)])]);
        assert_eq!(left.add(&right), expected);
    }

    #[test]
    fn test_polynomial_sub() {
        let left = poly(vec![(5, vec![("x", 1)]), (2, vec![])]);
        let right = poly(vec![(3, vec![("x", 1)]), (7, vec![])]);
        let expected = poly(vec![(2, vec![("x", 1)]), (-5, vec![])]);
        assert_eq!(left.sub(&right), expected);
    }

    #[test]
    fn test_polynomial_mul() {
        let left = poly(vec![(1, vec![("x", 1)]), (1, vec![])]);
        let right = poly(vec![(1, vec![("x", 1)]), (-1, vec![])]);
        let expected = poly(vec![(1, vec![("x", 2)]), (-1, vec![])]);
        assert_eq!(left.mul(&right), expected);
    }

    #[test]
    fn test_polynomial_mul_distributive() {
        let a = poly(vec![(1, vec![("x", 1)])]);
        let b = poly(vec![(2, vec![("y", 1)])]);
        let c = poly(vec![(3, vec![("z", 1)])]);
        let left = a.add(&b).mul(&c);
        let right = a.mul(&c).add(&b.mul(&c));
        assert_eq!(left, right);
    }

    #[test]
    fn test_polynomial_evaluate() {
        let p = poly(vec![(2, vec![("x", 2)]), (3, vec![("y", 1)]), (-1, vec![])]);
        let values = assignment(vec![("x", 2), ("y", 5)]);
        assert_eq!(p.evaluate(&values), Some(rat(22)));
    }

    #[test]
    fn test_polynomial_is_zero() {
        let p = poly(vec![(1, vec![("x", 1)]), (-1, vec![("x", 1)])]);
        assert!(p.is_zero());
    }

    #[test]
    fn test_polynomial_constant() {
        let p = Polynomial::constant(rat(7));
        assert_eq!(p, poly(vec![(7, vec![])]));
        assert_eq!(p.degree(), 0);
    }

    #[test]
    fn test_sos_verify_simple_square() {
        let cert = SosCertificate {
            gram_matrix: vec![vec![rat(1)]],
            basis: vec![Monomial::variable("x")],
        };
        assert!(verify_sos(&cert));
        assert_eq!(
            sos_polynomial(&cert).unwrap(),
            poly(vec![(1, vec![("x", 2)])])
        );
    }

    #[test]
    fn test_sos_verify_sum_of_squares() {
        let cert = SosCertificate {
            gram_matrix: vec![vec![rat(1), rat(0)], vec![rat(0), rat(1)]],
            basis: vec![Monomial::variable("x"), Monomial::variable("y")],
        };
        assert!(verify_sos(&cert));
        assert_eq!(
            sos_polynomial(&cert).unwrap(),
            poly(vec![(1, vec![("x", 2)]), (1, vec![("y", 2)])])
        );
    }

    #[test]
    fn test_sos_verify_invalid_not_psd() {
        let cert = SosCertificate {
            gram_matrix: vec![vec![rat(-1)]],
            basis: vec![Monomial::variable("x")],
        };
        assert!(!verify_sos(&cert));
    }

    #[test]
    fn test_psatz_simple_infeasibility() {
        let cert = PsatzCertificate {
            pi: vec![
                poly(vec![(-1, vec![("x", 2)]), (-1, vec![])]),
                poly(vec![(1, vec![("x", 2)])]),
            ],
            si: vec![sos_constant_one(), sos_constant_one()],
        };
        assert!(check_psatz(&cert));
    }

    #[test]
    fn test_psatz_two_constraints() {
        let cert = PsatzCertificate {
            pi: vec![
                poly(vec![(1, vec![]), (-1, vec![("x", 2)])]),
                poly(vec![(1, vec![]), (-1, vec![("y", 2)])]),
                poly(vec![(1, vec![("x", 2)]), (1, vec![("y", 2)]), (-3, vec![])]),
            ],
            si: vec![sos_constant_one(), sos_constant_one(), sos_constant_one()],
        };
        assert!(check_psatz(&cert));
    }

    #[test]
    fn test_ideal_membership_simple() {
        let witness = IdealMembershipWitness {
            f: poly(vec![(2, vec![("x", 1)]), (-2, vec![])]),
            generators: vec![poly(vec![(1, vec![("x", 1)]), (-1, vec![])])],
            quotients: vec![Polynomial::constant(rat(2))],
        };
        assert!(verify_ideal_membership(&witness));
    }

    #[test]
    fn test_ideal_membership_two_generators() {
        let witness = IdealMembershipWitness {
            f: poly(vec![(1, vec![("x", 1)]), (1, vec![("y", 1)]), (1, vec![])]),
            generators: vec![
                poly(vec![(1, vec![("x", 1)]), (-1, vec![])]),
                poly(vec![(1, vec![("y", 1)]), (2, vec![])]),
            ],
            quotients: vec![Polynomial::constant(rat(1)), Polynomial::constant(rat(1))],
        };
        assert!(verify_ideal_membership(&witness));
    }

    #[test]
    fn test_ideal_membership_invalid() {
        let witness = IdealMembershipWitness {
            f: poly(vec![(2, vec![("x", 1)]), (-2, vec![])]),
            generators: vec![poly(vec![(1, vec![("x", 1)]), (-1, vec![])])],
            quotients: vec![Polynomial::constant(rat(3))],
        };
        assert!(!verify_ideal_membership(&witness));
    }

    #[test]
    fn test_check_nra_lemma_structural() {
        let mut dag = SmtProofDag::new();
        let lit = dag.add_term(SmtTerm::Bool(true));
        let step_id = dag.add_step(SmtProofStep::Assume(lit));
        let verdict = check_nra_lemma(&dag, step_id, &[lit], &NraWitness::Structural);
        assert_eq!(verdict.trust_level, StepTrustLevel::StructurallyAccepted);
        assert_eq!(verdict.checker, CHECKER_NAME);
    }
}
