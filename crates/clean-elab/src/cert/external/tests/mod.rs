// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::rational::parse_rational_str_for_test;
use super::verify::{normalize_constraint, NormalizedConstraint};
use super::*;
use std::collections::BTreeMap;
use std::ops::Neg;

mod alethe;
mod proptest_constraint;
mod proptest_normalize;
mod proptest_rational;

#[test]
fn test_rational_parse_string_and_struct() {
    let json = r#""-3/4""#;
    let r: ExternalRational = serde_json::from_str(json).unwrap();
    assert_eq!(r, ExternalRational::new(-3, 4).unwrap());

    let json = r#"{"type":"rational","num":-3,"den":4}"#;
    let r: ExternalRational = serde_json::from_str(json).unwrap();
    assert_eq!(r, ExternalRational::new(-3, 4).unwrap());
}

#[test]
fn test_verify_farkas_simple_contradiction() {
    let cert = ExternalFarkasCert {
        version: "1.0".to_string(),
        constraints: vec![
            ExternalLinearConstraint {
                kind: ConstraintKind::Le,
                coefficients: BTreeMap::from([("x".to_string(), ExternalRational::from_int(1))]),
                constant: ExternalRational::from_int(5),
            },
            ExternalLinearConstraint {
                kind: ConstraintKind::Le,
                coefficients: BTreeMap::from([("x".to_string(), ExternalRational::from_int(-1))]),
                constant: ExternalRational::from_int(-6),
            },
        ],
        multipliers: vec![ExternalRational::ONE, ExternalRational::ONE],
        conclusion: "contradiction".to_string(),
    };

    let result = verify_farkas_certificate(&cert).unwrap();
    assert_eq!(result, ExternalRational::from_int(-1));
}

#[test]
fn test_verify_entailment_simple() {
    let cert = ExternalEntailmentCert {
        version: "1.0".to_string(),
        premises: vec![ExternalLinearConstraint {
            kind: ConstraintKind::Le,
            coefficients: BTreeMap::from([("x".to_string(), ExternalRational::from_int(1))]),
            constant: ExternalRational::from_int(5),
        }],
        multipliers: vec![ExternalRational::ONE],
        conclusion: ExternalLinearConstraint {
            kind: ConstraintKind::Le,
            coefficients: BTreeMap::from([("x".to_string(), ExternalRational::from_int(1))]),
            constant: ExternalRational::from_int(6),
        },
    };

    let result = verify_entailment_certificate(&cert).unwrap();
    assert_eq!(result.0, ExternalRational::from_int(5));
    assert_eq!(result.1, ExternalRational::from_int(6));
}

// ---------------------------------------------------------------------------
// Equality constraint in Farkas certificate
// ---------------------------------------------------------------------------

#[test]
fn test_verify_farkas_eq_constraint_contradiction() {
    // x = 5 (i.e., x <= 5 AND x >= 5) combined with x <= 4 (i.e., -x <= -4 as Ge)
    // gives: x <= 5, -x <= -5, -x <= -4 ... wait, that's not a contradiction.
    //
    // Correct setup: x = 5 AND x >= 6 is contradictory.
    // x = 5 decomposes to: x <= 5 AND -x <= -5
    // x >= 6 normalizes to: -x <= -6
    // Combined: (1*x + (-1)*x) <= (5 + -5) = 0 <= 0 (not strict, no contradiction yet)
    // We need: x = 5 AND -x <= -6
    // With multipliers [1, 1] on Eq and [1] on Ge:
    //   From Eq(x=5): x <= 5, -x <= -5 (both with multiplier 1)
    //   From Ge(x >= 6): -x <= -6 (with multiplier 1)
    //   Combined: x + (-x) + (-x) <= 5 + (-5) + (-6) = -x <= -6
    //   Doesn't cancel!
    //
    // Simpler: x = 5 AND x <= 4
    // Eq(x=5) decomposes to: x <= 5, -x <= -5
    // Le(x <= 4): x <= 4 (don't need this)
    // Better: Eq(x=5) gives both x <= 5 and -x <= -5
    // Le(-x <= -6) gives -x <= -6
    // Combined with mult [1, 1]: x + (-x) <= 5 + (-5) = 0 <= 0 (no contradiction)
    //
    // Actual contradiction: x = 5 (decomposes to x<=5 AND -x<=-5)
    // and -x = -6 (decomposes to -x<=-6 AND x<=6)
    // We need two constraints that when combined cancel variables AND give negative constant.
    //
    // Simplest: ONE equality constraint x = 5, plus one Le constraint -x <= -6
    // Eq(x=5) -> [x<=5, -x<=-5], Le(-x<=-6) -> [-x<=-6]
    // With multipliers [1, 1]: x<=5 + (-x<=-5) + (-x<=-6)... no, multiplier is per constraint.
    //
    // In Farkas, each constraint gets ONE multiplier. For Eq, the decomposition means
    // that multiplier applies to BOTH parts. So:
    // constraint[0] = Eq(x=5), multiplier[0] = 1 -> adds (x<=5) + (-x<=-5) = (0 <= 0)
    // constraint[1] = Le(-x <= -6), multiplier[1] = 1 -> adds (-x <= -6)
    // Combined: -x <= -6, still has variable.
    //
    // For a proper contradiction with Eq:
    // Eq(x=5): decomposes to (x <= 5) + (-x <= -5), net contribution with mult=1: 0 <= 0
    // For contradiction we need more constraints.
    //
    // Use: Eq(x=5) with mult=1: contributes 0 <= 0 (Le+Ge cancel)
    //      Le(x <= 4) with mult=1: contributes x <= 4
    //      Ge(x >= 6) with mult=1: contributes -x <= -6
    //      Combined: (0 + x + (-x)) <= (0 + 4 + (-6)) = 0 <= -2 -- contradiction!
    let cert = ExternalFarkasCert {
        version: "1.0".to_string(),
        constraints: vec![
            ExternalLinearConstraint {
                kind: ConstraintKind::Eq,
                coefficients: BTreeMap::from([("x".to_string(), ExternalRational::from_int(1))]),
                constant: ExternalRational::from_int(5),
            },
            ExternalLinearConstraint {
                kind: ConstraintKind::Le,
                coefficients: BTreeMap::from([("x".to_string(), ExternalRational::from_int(1))]),
                constant: ExternalRational::from_int(4),
            },
            ExternalLinearConstraint {
                kind: ConstraintKind::Ge,
                coefficients: BTreeMap::from([("x".to_string(), ExternalRational::from_int(1))]),
                constant: ExternalRational::from_int(6),
            },
        ],
        multipliers: vec![
            ExternalRational::ONE,
            ExternalRational::ONE,
            ExternalRational::ONE,
        ],
        conclusion: "contradiction".to_string(),
    };

    let result = verify_farkas_certificate(&cert).unwrap();
    assert_eq!(result, ExternalRational::from_int(-2));
}

#[test]
fn test_verify_farkas_eq_only_no_contradiction() {
    // A single Eq constraint x = 5 with multiplier 1 gives 0 <= 0 (Le + Ge cancel).
    // This is not a contradiction.
    let cert = ExternalFarkasCert {
        version: "1.0".to_string(),
        constraints: vec![ExternalLinearConstraint {
            kind: ConstraintKind::Eq,
            coefficients: BTreeMap::from([("x".to_string(), ExternalRational::from_int(1))]),
            constant: ExternalRational::from_int(5),
        }],
        multipliers: vec![ExternalRational::ONE],
        conclusion: "contradiction".to_string(),
    };

    let err = verify_farkas_certificate(&cert).unwrap_err();
    assert_eq!(err.code, ExternalCertErrorCode::NoContradiction);
}

#[test]
fn test_verify_entailment_eq_premise() {
    // Eq premise: x = 5 decomposes to (x <= 5) + (-x <= -5)
    // With multiplier 1 on the Eq, the contribution is: 0 <= 0
    // Adding Le premise x <= 3 with multiplier 1: x <= 3
    // Conclusion: x <= 3 -- should verify.
    let cert = ExternalEntailmentCert {
        version: "1.0".to_string(),
        premises: vec![
            ExternalLinearConstraint {
                kind: ConstraintKind::Eq,
                coefficients: BTreeMap::from([("x".to_string(), ExternalRational::from_int(1))]),
                constant: ExternalRational::from_int(5),
            },
            ExternalLinearConstraint {
                kind: ConstraintKind::Le,
                coefficients: BTreeMap::from([("x".to_string(), ExternalRational::from_int(1))]),
                constant: ExternalRational::from_int(3),
            },
        ],
        multipliers: vec![ExternalRational::ONE, ExternalRational::ONE],
        conclusion: ExternalLinearConstraint {
            kind: ConstraintKind::Le,
            coefficients: BTreeMap::from([("x".to_string(), ExternalRational::from_int(1))]),
            constant: ExternalRational::from_int(3),
        },
    };

    let (derived, claimed) = verify_entailment_certificate(&cert).unwrap();
    assert_eq!(derived, ExternalRational::from_int(3));
    assert_eq!(claimed, ExternalRational::from_int(3));
}

#[test]
fn test_verify_entailment_eq_conclusion_rejected() {
    // Equality constraints as conclusions are rejected because entailment
    // proves one-directional bounds, not exact equality.
    let cert = ExternalEntailmentCert {
        version: "1.0".to_string(),
        premises: vec![ExternalLinearConstraint {
            kind: ConstraintKind::Le,
            coefficients: BTreeMap::from([("x".to_string(), ExternalRational::from_int(1))]),
            constant: ExternalRational::from_int(5),
        }],
        multipliers: vec![ExternalRational::ONE],
        conclusion: ExternalLinearConstraint {
            kind: ConstraintKind::Eq,
            coefficients: BTreeMap::from([("x".to_string(), ExternalRational::from_int(1))]),
            constant: ExternalRational::from_int(5),
        },
    };

    let err = verify_entailment_certificate(&cert).unwrap_err();
    assert_eq!(err.code, ExternalCertErrorCode::UnsupportedConstraintKind);
}

#[test]
fn test_negative_multiplier_rejected() {
    let cert = ExternalFarkasCert {
        version: "1.0".to_string(),
        constraints: vec![ExternalLinearConstraint {
            kind: ConstraintKind::Le,
            coefficients: BTreeMap::new(),
            constant: ExternalRational::from_int(0),
        }],
        multipliers: vec![ExternalRational::from_int(-1)],
        conclusion: "contradiction".to_string(),
    };

    let err = verify_farkas_certificate(&cert).unwrap_err();
    assert_eq!(err.code, ExternalCertErrorCode::MultiplierNegative);
}

#[test]
fn test_linear_constraint_type_roundtrip() {
    let json = r#"{
        "type": "linear_constraint",
        "kind": "le",
        "coefficients": { "x": "1/2", "y": "-3" },
        "constant": "5/4"
    }"#;
    let constraint: ExternalLinearConstraint = serde_json::from_str(json).unwrap();
    assert_eq!(constraint.kind, ConstraintKind::Le);
    assert_eq!(
        constraint.coefficients.get("x").copied(),
        Some(ExternalRational::new(1, 2).unwrap())
    );
    assert_eq!(
        constraint.coefficients.get("y").copied(),
        Some(ExternalRational::from_int(-3))
    );
    assert_eq!(constraint.constant, ExternalRational::new(5, 4).unwrap());

    let serialized = serde_json::to_string(&constraint).unwrap();
    assert!(
        serialized.contains("\"type\":\"linear_constraint\""),
        "serialized constraint should include type field: {serialized}"
    );
}
