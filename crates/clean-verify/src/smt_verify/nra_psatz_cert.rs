// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Public Positivstellensatz certificate checker for NRA/NIA lemmas.
//!
//! This module exposes a serde-friendly, externally emittable certificate
//! format for Positivstellensatz (Psatz) refutations over non-linear real
//! arithmetic, together with a standalone checker that verifies the SoS
//! polynomial identity independently of the SMT proof DAG.
//!
//! ## Soundness Statement
//!
//! Given premise polynomials `p_1, ..., p_n` (each asserted `>= 0`) and
//! SOS multipliers `s_1, ..., s_n` (each of the form `m(x)^T G m(x)` with
//! `G` symmetric PSD), the certificate
//!
//! ```text
//! sum_i s_i * p_i + 1 = 0   (as a polynomial identity)
//! ```
//!
//! witnesses infeasibility of the constraint system `p_1 >= 0 /\ ... /\
//! p_n >= 0`: under any real assignment each `s_i(x) >= 0` and
//! `p_i(x) >= 0`, so the combination is non-negative, contradicting the
//! constant `-1`.
//!
//! When [`verify_positivstellensatz_cert`] returns `Ok(())`, both the
//! structural shape of every Gram matrix and the polynomial identity are
//! validated by exact rational arithmetic — so the claimed refutation is
//! a genuine entailment, independent of the solver that produced it.
//!
//! ## Intended Use
//!
//! ay's NRA solver emits a [`PsatzCert`] alongside an unsat answer. This
//! module is the receiving side: callers deserialize the certificate
//! (e.g. via `serde_json`) and feed it to [`verify_positivstellensatz_cert`].
//! Forged or malformed certificates produce structured [`PsError`] variants
//! so callers can report which invariant the certificate broke.
//!
//! The public [`PolyRepr`]/[`SosCert`]/[`PsatzCert`] types are deliberately
//! decoupled from the internal [`Polynomial`]/[`SosCertificate`] used by
//! the SMT proof DAG: callers author certificates in a stable,
//! self-describing form and the internal representation is free to evolve.

use std::collections::BTreeMap;

use num_rational::Rational64;
use serde::{Deserialize, Serialize};

use super::nra::{
    check_psatz, sos_polynomial, verify_sos, Monomial, Polynomial, PsatzCertificate, SosCertificate,
};

/// Rational coefficient represented as `numerator / denominator`.
///
/// Kept out of [`Rational64`] so the public format stays self-describing
/// under JSON/bincode round-trips (serde's `Rational64` impl is provided
/// by `num-rational`'s optional `serde` feature; exposing our own type
/// keeps the serialized shape stable across crate versions).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct RationalRepr {
    /// Numerator.
    pub num: i64,
    /// Denominator. Must be non-zero.
    pub den: i64,
}

impl RationalRepr {
    /// Build a [`RationalRepr`] from an integer.
    #[must_use]
    pub fn integer(value: i64) -> Self {
        Self { num: value, den: 1 }
    }

    /// Build a [`RationalRepr`] from a ratio. Returns `None` for zero
    /// denominator.
    #[must_use]
    pub fn ratio(num: i64, den: i64) -> Option<Self> {
        if den == 0 {
            None
        } else {
            Some(Self { num, den })
        }
    }

    fn to_rational(self) -> Result<Rational64, PsError> {
        if self.den == 0 {
            return Err(PsError::ZeroDenominator);
        }
        Ok(Rational64::new(self.num, self.den))
    }
}

/// A public monomial: sorted `(variable, exponent)` pairs with `exp > 0`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct MonomialRepr {
    /// Factors. Variables may appear in any order; duplicates are merged
    /// and zero exponents are dropped during [`to_internal`] conversion.
    pub factors: Vec<(String, u32)>,
}

impl MonomialRepr {
    /// Construct a monomial from its factors.
    #[must_use]
    pub fn new(factors: Vec<(String, u32)>) -> Self {
        Self { factors }
    }

    /// The constant monomial `1`.
    #[must_use]
    pub fn one() -> Self {
        Self {
            factors: Vec::new(),
        }
    }

    fn to_internal(&self) -> Monomial {
        Monomial::new(self.factors.clone())
    }
}

/// A public polynomial: sum of `(coeff, monomial)` terms.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PolyRepr {
    /// Non-zero terms. Duplicates are combined during conversion; a
    /// term whose coefficient totals to zero is dropped.
    pub terms: Vec<(RationalRepr, MonomialRepr)>,
}

impl PolyRepr {
    /// Construct a polynomial from its terms.
    #[must_use]
    pub fn new(terms: Vec<(RationalRepr, MonomialRepr)>) -> Self {
        Self { terms }
    }

    /// The zero polynomial.
    #[must_use]
    pub fn zero() -> Self {
        Self { terms: Vec::new() }
    }

    /// A constant polynomial.
    #[must_use]
    pub fn constant(value: RationalRepr) -> Self {
        Self {
            terms: vec![(value, MonomialRepr::one())],
        }
    }

    fn to_internal(&self) -> Result<Polynomial, PsError> {
        let mut internal_terms = Vec::with_capacity(self.terms.len());
        for (coeff, monomial) in &self.terms {
            internal_terms.push((coeff.to_rational()?, monomial.to_internal()));
        }
        Ok(Polynomial::new(internal_terms))
    }
}

/// A public SOS multiplier: `m(x)^T G m(x)` with `G` symmetric PSD over
/// rationals and `m(x)` a monomial basis.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SosCert {
    /// Row-major symmetric Gram matrix.
    pub gram: Vec<Vec<RationalRepr>>,
    /// Monomial basis aligned with the Gram matrix rows/columns.
    pub basis: Vec<MonomialRepr>,
}

impl SosCert {
    fn to_internal(&self) -> Result<SosCertificate, PsError> {
        let dim = self.basis.len();
        if self.gram.len() != dim {
            return Err(PsError::GramDimensionMismatch {
                basis: dim,
                gram_rows: self.gram.len(),
            });
        }
        if let Some(offending) = self.gram.iter().find(|row| row.len() != dim) {
            return Err(PsError::GramNonSquare {
                expected: dim,
                row_len: offending.len(),
            });
        }

        let mut gram_internal = Vec::with_capacity(dim);
        for row in &self.gram {
            let mut internal_row = Vec::with_capacity(dim);
            for cell in row {
                internal_row.push(cell.to_rational()?);
            }
            gram_internal.push(internal_row);
        }

        let basis_internal = self.basis.iter().map(MonomialRepr::to_internal).collect();

        Ok(SosCertificate {
            gram_matrix: gram_internal,
            basis: basis_internal,
        })
    }
}

/// A public Positivstellensatz refutation certificate.
///
/// Asserts that `sum_i si[i] * premises[i] + 1 == 0` as a polynomial
/// identity, which witnesses infeasibility of
/// `forall i. premises[i] >= 0`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PsatzCert {
    /// Premise polynomials, each asserted `>= 0` in the claimed constraint
    /// system.
    pub premises: Vec<PolyRepr>,
    /// SOS multipliers, one per premise. `si.len()` must equal
    /// `premises.len()`.
    pub si: Vec<SosCert>,
}

impl PsatzCert {
    /// Convert to the internal representation used by the SMT proof DAG.
    fn to_internal(&self) -> Result<PsatzCertificate, PsError> {
        if self.premises.len() != self.si.len() {
            return Err(PsError::ShapeMismatch {
                premises: self.premises.len(),
                multipliers: self.si.len(),
            });
        }
        let mut pi = Vec::with_capacity(self.premises.len());
        for premise in &self.premises {
            pi.push(premise.to_internal()?);
        }
        let mut si = Vec::with_capacity(self.si.len());
        for sos in &self.si {
            si.push(sos.to_internal()?);
        }
        Ok(PsatzCertificate { pi, si })
    }
}

/// Failure modes for [`verify_positivstellensatz_cert`].
///
/// Each variant distinguishes a specific invariant the certificate broke,
/// making downstream reporting precise.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum PsError {
    /// The certificate has a different number of premises and SOS
    /// multipliers, so the refutation combination is ill-formed.
    #[error(
        "Psatz certificate shape mismatch: {premises} premises but {multipliers} SOS multipliers"
    )]
    ShapeMismatch {
        /// Number of premises.
        premises: usize,
        /// Number of SOS multipliers.
        multipliers: usize,
    },
    /// An SOS certificate's Gram matrix row count does not match its
    /// basis length.
    #[error("SOS Gram matrix has {gram_rows} rows but basis has length {basis}")]
    GramDimensionMismatch {
        /// Declared basis length.
        basis: usize,
        /// Number of rows in the supplied Gram matrix.
        gram_rows: usize,
    },
    /// An SOS Gram matrix row does not have the expected length (matrix
    /// is non-square).
    #[error("SOS Gram matrix row has {row_len} columns, expected {expected}")]
    GramNonSquare {
        /// Expected row length (equal to basis length).
        expected: usize,
        /// Observed row length.
        row_len: usize,
    },
    /// A rational coefficient was supplied with denominator zero.
    #[error("rational coefficient has zero denominator")]
    ZeroDenominator,
    /// The SOS Gram matrix failed the structural PSD check (not
    /// symmetric or not positive semi-definite over the rationals).
    #[error("SOS Gram matrix at index {index} is not symmetric PSD")]
    SosNotPsd {
        /// 0-based position in [`PsatzCert::si`] that failed.
        index: usize,
    },
    /// The refutation polynomial identity `sum s_i * p_i + 1 == 0` does
    /// not hold. This catches forged or truncated certificates.
    #[error("Psatz identity does not hold: sum s_i * p_i + 1 is not the zero polynomial")]
    IdentityFails,
    /// The certificate would entail infeasibility of the empty premise
    /// set (a "refutation" with no premises), which is trivially false.
    #[error("Psatz certificate has no premises; infeasibility is vacuously false")]
    EmptyPremises,
}

/// Verify a public Positivstellensatz certificate.
///
/// Returns `Ok(())` iff:
/// 1. Premises and multipliers have matching lengths.
/// 2. Every SOS Gram matrix is well-shaped, symmetric, and PSD over the
///    rationals.
/// 3. The polynomial identity `sum_i s_i * p_i + 1 == 0` holds exactly
///    (via sparse rational arithmetic).
///
/// Any failure returns a structured [`PsError`] pinpointing the broken
/// invariant. Because the checker is a pure polynomial-identity test, it
/// is independent of the NRA solver that produced the certificate and
/// provides an independent soundness gate.
///
/// # Empty-premise policy
///
/// A certificate with no premises is always rejected ([`PsError::EmptyPremises`])
/// — a Positivstellensatz refutation must reference at least one premise
/// to be non-vacuous.
pub fn verify_positivstellensatz_cert(cert: &PsatzCert) -> Result<(), PsError> {
    if cert.premises.is_empty() {
        return Err(PsError::EmptyPremises);
    }

    let internal = cert.to_internal()?;

    // Validate each SOS multiplier individually so errors point to the
    // offending index.
    for (index, sos) in internal.si.iter().enumerate() {
        if !verify_sos(sos) {
            return Err(PsError::SosNotPsd { index });
        }
    }

    if check_psatz(&internal) {
        Ok(())
    } else {
        Err(PsError::IdentityFails)
    }
}

/// Return the expanded SOS polynomial for a single [`SosCert`], if the
/// Gram matrix is well-formed and PSD. Useful for debugging forged
/// certificates: callers can diff the expected `s_i * p_i` contribution
/// against the expansion.
#[must_use]
pub fn expand_sos_cert(cert: &SosCert) -> Option<Polynomial> {
    let internal = cert.to_internal().ok()?;
    sos_polynomial(&internal)
}

/// Sum_i s_i * p_i for a [`PsatzCert`] (without the `+ 1`). Useful for
/// diagnostics.
pub fn combination_polynomial(cert: &PsatzCert) -> Result<Polynomial, PsError> {
    let internal = cert.to_internal()?;
    let mut combination = Polynomial::zero();
    for (index, (premise, multiplier)) in internal.pi.iter().zip(&internal.si).enumerate() {
        let sos_poly = sos_polynomial(multiplier).ok_or(PsError::SosNotPsd { index })?;
        combination = combination.add(&sos_poly.mul(premise));
    }
    Ok(combination)
}

/// Evaluate the refutation polynomial `sum s_i * p_i + 1` at a rational
/// assignment. For a valid certificate this must be identically zero, so
/// any sample should return `Some(0)` — a non-zero sample immediately
/// falsifies the claimed identity without requiring the full
/// Gram-expansion check.
pub fn evaluate_refutation(
    cert: &PsatzCert,
    assignment: &BTreeMap<String, RationalRepr>,
) -> Result<Option<Rational64>, PsError> {
    let combination = combination_polynomial(cert)?;
    let one = Polynomial::constant(Rational64::from_integer(1));
    let residual = combination.add(&one);
    let mut internal_assignment = BTreeMap::new();
    for (var, value) in assignment {
        internal_assignment.insert(var.clone(), value.to_rational()?);
    }
    Ok(residual.evaluate(&internal_assignment))
}
