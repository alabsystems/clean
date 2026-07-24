// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;
use proptest::prelude::*;

// Strategy for small rationals
fn small_rational() -> impl Strategy<Value = ExternalRational> {
    (-10000i64..=10000i64, 1i64..=10000i64).prop_map(|(n, d)| ExternalRational::new(n, d).unwrap())
}

// Strategy for variable names
fn var_name() -> impl Strategy<Value = String> {
    prop_oneof![
        Just("x".to_string()),
        Just("y".to_string()),
        Just("z".to_string()),
    ]
}

// Strategy for coefficient maps
fn coeffs_map() -> impl Strategy<Value = BTreeMap<String, ExternalRational>> {
    proptest::collection::btree_map(var_name(), small_rational(), 0..=3)
}

// Strategy for non-equality constraint kinds (single-output normalization)
fn supported_kind() -> impl Strategy<Value = ConstraintKind> {
    prop_oneof![
        Just(ConstraintKind::Le),
        Just(ConstraintKind::Lt),
        Just(ConstraintKind::Ge),
        Just(ConstraintKind::Gt),
    ]
}

// Equality constraint decomposes into Le + Ge (2 normalized constraints)
#[test]
fn eq_decomposes_to_le_and_ge() {
    let mut coeffs = BTreeMap::new();
    coeffs.insert("x".to_string(), ExternalRational::from_int(3));
    let constraint = ExternalLinearConstraint {
        kind: ConstraintKind::Eq,
        coefficients: coeffs,
        constant: ExternalRational::from_int(7),
    };
    let result = normalize_constraint(&constraint).expect("Eq should normalize");
    assert_eq!(result.len(), 2, "Eq should decompose into 2 constraints");

    // First part: Le direction (A*x <= b)
    let le_part = &result[0];
    assert!(!le_part.strict, "Le part should not be strict");
    assert_eq!(
        le_part.coeffs.get("x").copied(),
        Some(ExternalRational::from_int(3)),
        "Le part should preserve coefficient sign"
    );
    assert_eq!(le_part.constant, ExternalRational::from_int(7));

    // Second part: Ge direction (-A*x <= -b)
    let ge_part = &result[1];
    assert!(!ge_part.strict, "Ge part should not be strict");
    assert_eq!(
        ge_part.coeffs.get("x").copied(),
        Some(ExternalRational::from_int(-3)),
        "Ge part should negate coefficient"
    );
    assert_eq!(ge_part.constant, ExternalRational::from_int(-7));
}

#[test]
fn eq_empty_coeffs_decomposes() {
    let constraint = ExternalLinearConstraint {
        kind: ConstraintKind::Eq,
        coefficients: BTreeMap::new(),
        constant: ExternalRational::ZERO,
    };
    let result = normalize_constraint(&constraint).expect("Eq with empty coeffs should normalize");
    assert_eq!(
        result.len(),
        2,
        "Eq should always decompose into 2 constraints"
    );
    assert!(result[0].coeffs.is_empty());
    assert!(result[1].coeffs.is_empty());
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(500))]

    // ----------------------------------------------------------------
    // normalize_constraint() Properties
    // ----------------------------------------------------------------

    #[test]
    fn le_preserves_sign(coeffs in coeffs_map(), constant in small_rational()) {
        let constraint = ExternalLinearConstraint {
            kind: ConstraintKind::Le,
            coefficients: coeffs.clone(),
            constant,
        };
        let parts = normalize_constraint(&constraint).unwrap();
        prop_assert_eq!(parts.len(), 1, "Le should produce exactly 1 normalized constraint");
        let normalized = &parts[0];

        // Le should preserve signs
        for (var, coeff) in &coeffs {
            if !coeff.is_zero() {
                prop_assert_eq!(
                    normalized.coeffs.get(var).copied(),
                    Some(*coeff),
                    "Le should preserve coefficient sign for {}",
                    var
                );
            }
        }
        prop_assert_eq!(normalized.constant, constant, "Le should preserve constant");
        prop_assert!(!normalized.strict, "Le should not be strict");
    }

    #[test]
    fn lt_is_strict(coeffs in coeffs_map(), constant in small_rational()) {
        let constraint = ExternalLinearConstraint {
            kind: ConstraintKind::Lt,
            coefficients: coeffs,
            constant,
        };
        let parts = normalize_constraint(&constraint).unwrap();
        prop_assert_eq!(parts.len(), 1, "Lt should produce exactly 1 normalized constraint");
        let normalized = &parts[0];
        prop_assert!(normalized.strict, "Lt should be strict");
    }

    #[test]
    fn ge_negates_coeffs(coeffs in coeffs_map(), constant in small_rational()) {
        let constraint = ExternalLinearConstraint {
            kind: ConstraintKind::Ge,
            coefficients: coeffs.clone(),
            constant,
        };
        let parts = normalize_constraint(&constraint).unwrap();
        prop_assert_eq!(parts.len(), 1, "Ge should produce exactly 1 normalized constraint");
        let normalized = &parts[0];

        // Ge should negate all coefficients
        for (var, coeff) in &coeffs {
            if !coeff.is_zero() {
                prop_assert_eq!(
                    normalized.coeffs.get(var).copied(),
                    Some(coeff.neg()),
                    "Ge should negate coefficient for {}",
                    var
                );
            }
        }
        prop_assert_eq!(normalized.constant, constant.neg(), "Ge should negate constant");
        prop_assert!(!normalized.strict, "Ge should not be strict");
    }

    #[test]
    fn gt_negates_and_strict(coeffs in coeffs_map(), constant in small_rational()) {
        let constraint = ExternalLinearConstraint {
            kind: ConstraintKind::Gt,
            coefficients: coeffs.clone(),
            constant,
        };
        let parts = normalize_constraint(&constraint).unwrap();
        prop_assert_eq!(parts.len(), 1, "Gt should produce exactly 1 normalized constraint");
        let normalized = &parts[0];

        // Gt should negate all coefficients
        for (var, coeff) in &coeffs {
            if !coeff.is_zero() {
                prop_assert_eq!(
                    normalized.coeffs.get(var).copied(),
                    Some(coeff.neg()),
                    "Gt should negate coefficient for {}",
                    var
                );
            }
        }
        prop_assert_eq!(normalized.constant, constant.neg(), "Gt should negate constant");
        prop_assert!(normalized.strict, "Gt should be strict");
    }

    #[test]
    fn zero_coeffs_removed(kind in supported_kind(), constant in small_rational()) {
        // Constraint with explicit zero coefficient should have it removed
        let mut coeffs = BTreeMap::new();
        coeffs.insert("x".to_string(), ExternalRational::ZERO);
        coeffs.insert("y".to_string(), ExternalRational::from_int(5));

        let constraint = ExternalLinearConstraint {
            kind,
            coefficients: coeffs,
            constant,
        };
        let parts = normalize_constraint(&constraint).unwrap();
        // supported_kind() excludes Eq, so always exactly 1 part
        prop_assert_eq!(parts.len(), 1);
        let normalized = &parts[0];

        prop_assert!(
            !normalized.coeffs.contains_key("x"),
            "zero coefficient should be removed after normalization"
        );
    }

    // ----------------------------------------------------------------
    // Semantic Equivalence
    // ----------------------------------------------------------------

    #[test]
    fn ge_le_duality(coeffs in coeffs_map(), constant in small_rational()) {
        // Ge(c, k) should normalize to same form as Le(-c, -k)
        let ge_constraint = ExternalLinearConstraint {
            kind: ConstraintKind::Ge,
            coefficients: coeffs.clone(),
            constant,
        };

        let negated_coeffs: BTreeMap<String, ExternalRational> = coeffs
            .iter()
            .map(|(k, v)| (k.clone(), v.neg()))
            .collect();
        let le_constraint = ExternalLinearConstraint {
            kind: ConstraintKind::Le,
            coefficients: negated_coeffs,
            constant: constant.neg(),
        };

        let norm_ge = normalize_constraint(&ge_constraint).unwrap().into_iter().next().unwrap();
        let norm_le = normalize_constraint(&le_constraint).unwrap().into_iter().next().unwrap();

        prop_assert_eq!(norm_ge.coeffs, norm_le.coeffs, "Ge and negated Le should have same coeffs");
        prop_assert_eq!(norm_ge.constant, norm_le.constant, "Ge and negated Le should have same constant");
        prop_assert_eq!(norm_ge.strict, norm_le.strict, "Ge and negated Le should have same strictness");
    }

    #[test]
    fn gt_lt_duality(coeffs in coeffs_map(), constant in small_rational()) {
        // Gt(c, k) should normalize to same form as Lt(-c, -k)
        let gt_constraint = ExternalLinearConstraint {
            kind: ConstraintKind::Gt,
            coefficients: coeffs.clone(),
            constant,
        };

        let negated_coeffs: BTreeMap<String, ExternalRational> = coeffs
            .iter()
            .map(|(k, v)| (k.clone(), v.neg()))
            .collect();
        let lt_constraint = ExternalLinearConstraint {
            kind: ConstraintKind::Lt,
            coefficients: negated_coeffs,
            constant: constant.neg(),
        };

        let norm_gt = normalize_constraint(&gt_constraint).unwrap().into_iter().next().unwrap();
        let norm_lt = normalize_constraint(&lt_constraint).unwrap().into_iter().next().unwrap();

        prop_assert_eq!(norm_gt.coeffs, norm_lt.coeffs, "Gt and negated Lt should have same coeffs");
        prop_assert_eq!(norm_gt.constant, norm_lt.constant, "Gt and negated Lt should have same constant");
        prop_assert_eq!(norm_gt.strict, norm_lt.strict, "Gt and negated Lt should have same strictness");
    }

    #[test]
    fn eq_decomposition_matches_le_and_ge(coeffs in coeffs_map(), constant in small_rational()) {
        // Eq(c, k) should decompose to [Le(c, k), Le(-c, -k)] which matches
        // normalizing Le(c, k) and Ge(c, k) independently
        let eq_constraint = ExternalLinearConstraint {
            kind: ConstraintKind::Eq,
            coefficients: coeffs.clone(),
            constant,
        };
        let le_constraint = ExternalLinearConstraint {
            kind: ConstraintKind::Le,
            coefficients: coeffs.clone(),
            constant,
        };
        let ge_constraint = ExternalLinearConstraint {
            kind: ConstraintKind::Ge,
            coefficients: coeffs,
            constant,
        };

        let mut eq_parts = normalize_constraint(&eq_constraint).unwrap();
        prop_assert_eq!(eq_parts.len(), 2, "Eq should always produce 2 parts");
        let eq_ge = eq_parts.pop().unwrap();
        let eq_le = eq_parts.pop().unwrap();

        let le_part = normalize_constraint(&le_constraint).unwrap().into_iter().next().unwrap();
        let ge_part = normalize_constraint(&ge_constraint).unwrap().into_iter().next().unwrap();

        // Eq Le-part should match Le normalization
        prop_assert_eq!(eq_le.coeffs, le_part.coeffs, "Eq Le-part coeffs should match Le");
        prop_assert_eq!(eq_le.constant, le_part.constant, "Eq Le-part constant should match Le");
        prop_assert_eq!(eq_le.strict, le_part.strict, "Eq Le-part should not be strict");

        // Eq Ge-part should match Ge normalization
        prop_assert_eq!(eq_ge.coeffs, ge_part.coeffs, "Eq Ge-part coeffs should match Ge");
        prop_assert_eq!(eq_ge.constant, ge_part.constant, "Eq Ge-part constant should match Ge");
        prop_assert_eq!(eq_ge.strict, ge_part.strict, "Eq Ge-part should not be strict");
    }
}
