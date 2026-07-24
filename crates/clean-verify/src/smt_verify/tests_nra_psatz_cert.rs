// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Behavioural accept+reject tests for the Positivstellensatz NRA
//! certificate checker in [`crate::smt_verify::nra_psatz_cert`].
//!
//! Tests cover each failure mode in [`PsError`] (one reject case per
//! variant) plus canonical accept cases (valid x^2+1 refutation, linear
//! infeasibility, non-trivial SOS multiplier, multi-variable SoS
//! expansion, JSON round-trip, rational sampling).

use std::collections::BTreeMap;

use num_rational::Rational64;

use super::nra::Polynomial;
use super::nra_psatz_cert::{
    combination_polynomial, evaluate_refutation, expand_sos_cert, verify_positivstellensatz_cert,
    MonomialRepr, PolyRepr, PsError, PsatzCert, RationalRepr, SosCert,
};

fn r(n: i64) -> RationalRepr {
    RationalRepr::integer(n)
}

fn mono(factors: &[(&str, u32)]) -> MonomialRepr {
    MonomialRepr::new(
        factors
            .iter()
            .map(|(v, e)| ((*v).to_string(), *e))
            .collect(),
    )
}

fn poly(terms: &[(i64, &[(&str, u32)])]) -> PolyRepr {
    PolyRepr::new(
        terms
            .iter()
            .map(|(c, factors)| (r(*c), mono(factors)))
            .collect(),
    )
}

fn sos_one() -> SosCert {
    SosCert {
        gram: vec![vec![r(1)]],
        basis: vec![MonomialRepr::one()],
    }
}

/// Valid certificate: `p1 = -x^2 - 1 >= 0`, `p2 = x^2 >= 0` with
/// `s1 = s2 = 1`. Then `1 * (-x^2 - 1) + 1 * x^2 + 1 = 0`.
#[test]
fn test_verify_accepts_valid_refutation() {
    let cert = PsatzCert {
        premises: vec![
            poly(&[(-1, &[("x", 2)]), (-1, &[])]),
            poly(&[(1, &[("x", 2)])]),
        ],
        si: vec![sos_one(), sos_one()],
    };
    verify_positivstellensatz_cert(&cert).expect("valid Psatz certificate must be accepted");
}

/// Valid certificate with a non-trivial SOS multiplier: `p1 = -1 - x^2`,
/// `s1 = 1`, `p2 = 1`, `s2 = x^2`. Then
/// `(-1 - x^2) + x^2 + 1 = 0`.
#[test]
fn test_verify_accepts_nontrivial_sos() {
    let cert = PsatzCert {
        premises: vec![poly(&[(-1, &[]), (-1, &[("x", 2)])]), poly(&[(1, &[])])],
        si: vec![
            sos_one(),
            // s2 = x^2 via Gram [[1]] over basis [x]
            SosCert {
                gram: vec![vec![r(1)]],
                basis: vec![mono(&[("x", 1)])],
            },
        ],
    };
    verify_positivstellensatz_cert(&cert).expect("non-trivial SOS must be accepted");
}

#[test]
fn test_verify_rejects_empty_premises() {
    let cert = PsatzCert {
        premises: vec![],
        si: vec![],
    };
    assert!(matches!(
        verify_positivstellensatz_cert(&cert),
        Err(PsError::EmptyPremises)
    ));
}

#[test]
fn test_verify_rejects_shape_mismatch() {
    let cert = PsatzCert {
        premises: vec![poly(&[(1, &[])])],
        si: vec![sos_one(), sos_one()],
    };
    assert!(matches!(
        verify_positivstellensatz_cert(&cert),
        Err(PsError::ShapeMismatch {
            premises: 1,
            multipliers: 2,
        })
    ));
}

/// Forged certificate: the combination of premises sums to 0 (not -1),
/// so `sum + 1 = 1 != 0`: identity check must reject.
#[test]
fn test_verify_rejects_forged_identity() {
    let cert = PsatzCert {
        premises: vec![
            poly(&[(-1, &[("x", 2)]), (-1, &[])]),
            poly(&[(1, &[("x", 2)]), (1, &[])]),
        ],
        si: vec![sos_one(), sos_one()],
    };
    assert!(matches!(
        verify_positivstellensatz_cert(&cert),
        Err(PsError::IdentityFails)
    ));
}

/// Forged certificate with a non-PSD Gram matrix. The diagonal entry
/// `-1` makes the SOS multiplier `-1`, which is negative — not a valid
/// SOS witness. The checker must reject at the SoS step regardless of
/// whether the identity later holds.
#[test]
fn test_verify_rejects_non_psd_gram() {
    let cert = PsatzCert {
        premises: vec![poly(&[(-1, &[])])],
        si: vec![SosCert {
            gram: vec![vec![r(-1)]],
            basis: vec![MonomialRepr::one()],
        }],
    };
    assert!(matches!(
        verify_positivstellensatz_cert(&cert),
        Err(PsError::SosNotPsd { index: 0 })
    ));
}

#[test]
fn test_verify_rejects_gram_dimension_mismatch() {
    let cert = PsatzCert {
        premises: vec![poly(&[(-1, &[])])],
        si: vec![SosCert {
            // 2x2 matrix but basis of length 1
            gram: vec![vec![r(1), r(0)], vec![r(0), r(1)]],
            basis: vec![MonomialRepr::one()],
        }],
    };
    assert!(matches!(
        verify_positivstellensatz_cert(&cert),
        Err(PsError::GramDimensionMismatch {
            basis: 1,
            gram_rows: 2,
        })
    ));
}

#[test]
fn test_verify_rejects_non_square_gram() {
    let cert = PsatzCert {
        premises: vec![poly(&[(-1, &[])])],
        si: vec![SosCert {
            // First row has 2 entries, second has 1 — non-square
            gram: vec![vec![r(1), r(0)], vec![r(0)]],
            basis: vec![MonomialRepr::one(), MonomialRepr::one()],
        }],
    };
    assert!(matches!(
        verify_positivstellensatz_cert(&cert),
        Err(PsError::GramNonSquare { .. })
    ));
}

#[test]
fn test_verify_rejects_zero_denominator() {
    let cert = PsatzCert {
        premises: vec![PolyRepr::new(vec![(
            RationalRepr { num: 1, den: 0 },
            MonomialRepr::one(),
        )])],
        si: vec![sos_one()],
    };
    assert!(matches!(
        verify_positivstellensatz_cert(&cert),
        Err(PsError::ZeroDenominator)
    ));
}

/// Linear infeasibility of `x >= 0 /\ -x - 1 >= 0`: sum = -1.
#[test]
fn test_verify_accepts_linear_infeasibility() {
    let cert = PsatzCert {
        premises: vec![
            poly(&[(1, &[("x", 1)])]),
            poly(&[(-1, &[("x", 1)]), (-1, &[])]),
        ],
        si: vec![sos_one(), sos_one()],
    };
    verify_positivstellensatz_cert(&cert).expect("linear infeasibility must verify");
}

#[test]
fn test_evaluate_refutation_zero_at_any_point() {
    let cert = PsatzCert {
        premises: vec![
            poly(&[(-1, &[("x", 2)]), (-1, &[])]),
            poly(&[(1, &[("x", 2)])]),
        ],
        si: vec![sos_one(), sos_one()],
    };
    let mut assignment = BTreeMap::new();
    assignment.insert("x".to_string(), RationalRepr::ratio(7, 3).unwrap());
    let residual = evaluate_refutation(&cert, &assignment)
        .expect("eval must succeed")
        .expect("polynomial is total over declared vars");
    assert_eq!(residual, Rational64::from_integer(0));
}

/// The forged `x^2 + 1` premise produces a non-zero residual at `x = 1`
/// — a fast forgery witness independent of the symbolic identity check.
#[test]
fn test_evaluate_refutation_catches_forgery_at_sample() {
    let cert = PsatzCert {
        premises: vec![
            poly(&[(-1, &[("x", 2)]), (-1, &[])]),
            poly(&[(1, &[("x", 2)]), (1, &[])]),
        ],
        si: vec![sos_one(), sos_one()],
    };
    let mut assignment = BTreeMap::new();
    assignment.insert("x".to_string(), RationalRepr::integer(1));
    let residual = evaluate_refutation(&cert, &assignment)
        .expect("eval must succeed")
        .expect("polynomial is total");
    assert_ne!(residual, Rational64::from_integer(0));
}

#[test]
fn test_psatz_cert_serde_json_roundtrip() {
    let cert = PsatzCert {
        premises: vec![
            poly(&[(-1, &[("x", 2)]), (-1, &[])]),
            poly(&[(1, &[("x", 2)])]),
        ],
        si: vec![sos_one(), sos_one()],
    };
    let encoded = serde_json::to_string(&cert).expect("serialize");
    let decoded: PsatzCert = serde_json::from_str(&encoded).expect("deserialize");
    verify_positivstellensatz_cert(&decoded).expect("round-tripped cert verifies");
    assert_eq!(cert, decoded);
}

/// Two-variable SoS: Gram = [[1,0],[0,1]], basis = [x, y]. Expansion
/// is `x^2 + y^2`; evaluated at (3, 4) that's 25.
#[test]
fn test_expand_sos_cert_two_variable() {
    let cert = SosCert {
        gram: vec![vec![r(1), r(0)], vec![r(0), r(1)]],
        basis: vec![mono(&[("x", 1)]), mono(&[("y", 1)])],
    };
    let expanded = expand_sos_cert(&cert).expect("well-formed SOS");
    let mut assignment = BTreeMap::new();
    assignment.insert("x".to_string(), Rational64::from_integer(3));
    assignment.insert("y".to_string(), Rational64::from_integer(4));
    let value = expanded.evaluate(&assignment).expect("total");
    assert_eq!(value, Rational64::from_integer(25));
}

/// Combination polynomial diagnostic on the canonical `x^2 + 1 = 0`
/// refutation. `combination = -x^2 - 1 + x^2 = -1`.
#[test]
fn test_combination_polynomial_is_minus_one() {
    let cert = PsatzCert {
        premises: vec![
            poly(&[(-1, &[("x", 2)]), (-1, &[])]),
            poly(&[(1, &[("x", 2)])]),
        ],
        si: vec![sos_one(), sos_one()],
    };
    let combination = combination_polynomial(&cert).expect("diagnostic succeeds");
    assert_eq!(
        combination,
        Polynomial::constant(Rational64::from_integer(-1))
    );
}
