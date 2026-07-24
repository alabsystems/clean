// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;
use proptest::prelude::*;

// Strategy for small rationals to avoid arithmetic overflow
fn small_rational() -> impl Strategy<Value = ExternalRational> {
    (-10000i64..=10000i64, 1i64..=10000i64).prop_map(|(n, d)| ExternalRational::new(n, d).unwrap())
}

// Strategy for variable names
fn var_name() -> impl Strategy<Value = String> {
    prop_oneof![
        Just("x".to_string()),
        Just("y".to_string()),
        Just("z".to_string()),
        Just("w".to_string()),
    ]
}

// Strategy for small coefficient maps (0-4 variables)
fn small_coeffs() -> impl Strategy<Value = BTreeMap<String, ExternalRational>> {
    proptest::collection::btree_map(var_name(), small_rational(), 0..=4)
}

// Strategy for NormalizedConstraint (canonical form: no zero coefficients)
fn constraint() -> impl Strategy<Value = NormalizedConstraint> {
    (small_coeffs(), small_rational(), any::<bool>()).prop_map(|(coeffs, constant, strict)| {
        NormalizedConstraint {
            // Filter out zero coefficients to produce canonical form
            coeffs: coeffs.into_iter().filter(|(_, v)| !v.is_zero()).collect(),
            constant,
            strict,
        }
    })
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(500))]

    // ----------------------------------------------------------------
    // scale() Properties
    // ----------------------------------------------------------------

    #[test]
    fn scale_by_zero_gives_zero(c in constraint()) {
        let scaled = c.scale(ExternalRational::ZERO).unwrap();
        prop_assert!(scaled.coeffs.is_empty(), "scale by 0 should clear coeffs");
        prop_assert!(scaled.constant.is_zero(), "scale by 0 should zero constant");
        prop_assert!(!scaled.strict, "scale by 0 should clear strict");
    }

    #[test]
    fn scale_by_one_is_identity(c in constraint()) {
        let scaled = c.scale(ExternalRational::ONE).unwrap();
        prop_assert_eq!(scaled.coeffs, c.coeffs, "scale by 1 should preserve coeffs");
        prop_assert_eq!(scaled.constant, c.constant, "scale by 1 should preserve constant");
        prop_assert_eq!(scaled.strict, c.strict, "scale by 1 should preserve strict");
    }

    #[test]
    fn scale_preserves_strictness(c in constraint(), factor in small_rational()) {
        // When factor is non-zero, strictness should be preserved
        if !factor.is_zero() {
            let scaled = c.scale(factor).unwrap();
            prop_assert_eq!(scaled.strict, c.strict, "scale should preserve strictness");
        }
    }

    #[test]
    fn scale_associative(c in constraint(), a in small_rational(), b in small_rational()) {
        // scale(scale(c, a), b) == scale(c, a*b)
        // When both factors and product are non-zero
        if let (Ok(_ab), Ok(scaled_a), Ok(scaled_ab_direct)) = (
            a.mul(b),
            c.scale(a),
            a.mul(b).and_then(|ab| c.scale(ab))
        ) {
            if let Ok(scaled_ab_seq) = scaled_a.scale(b) {
                // Compare coefficients
                prop_assert_eq!(
                    scaled_ab_seq.coeffs, scaled_ab_direct.coeffs,
                    "scale should be associative (coeffs)"
                );
                // Compare constants
                prop_assert_eq!(
                    scaled_ab_seq.constant, scaled_ab_direct.constant,
                    "scale should be associative (constant)"
                );
            }
        }
    }

    #[test]
    fn scale_removes_zero_coeffs(factor in small_rational()) {
        // If a coefficient becomes zero after scaling, it should be removed
        let mut coeffs = BTreeMap::new();
        coeffs.insert("x".to_string(), ExternalRational::from_int(0));
        let c = NormalizedConstraint {
            coeffs,
            constant: ExternalRational::ONE,
            strict: false,
        };
        // After scaling, the zero coeff should still be absent
        let scaled = c.scale(factor).unwrap();
        prop_assert!(
            !scaled.coeffs.contains_key("x"),
            "zero coefficients should be removed after scale"
        );
    }

    // ----------------------------------------------------------------
    // add() Properties
    // ----------------------------------------------------------------

    #[test]
    fn add_identity(c in constraint()) {
        let zero = NormalizedConstraint::zero();
        let result = c.clone().add(zero).unwrap();
        prop_assert_eq!(result.coeffs, c.coeffs, "add zero should preserve coeffs");
        prop_assert_eq!(result.constant, c.constant, "add zero should preserve constant");
        prop_assert_eq!(result.strict, c.strict, "add zero should preserve strictness");
    }

    #[test]
    fn add_commutative(a in constraint(), b in constraint()) {
        // a + b should equal b + a (structurally)
        let ab = a.clone().add(b.clone());
        let ba = b.clone().add(a.clone());
        match (ab, ba) {
            (Ok(ab), Ok(ba)) => {
                prop_assert_eq!(ab.coeffs, ba.coeffs, "add should be commutative (coeffs)");
                prop_assert_eq!(ab.constant, ba.constant, "add should be commutative (constant)");
                prop_assert_eq!(ab.strict, ba.strict, "add should be commutative (strict)");
            }
            (Err(_), Err(_)) => {} // both overflow is consistent
            _ => prop_assert!(false, "inconsistent overflow behavior"),
        }
    }

    #[test]
    fn add_cancels_opposite_coeffs(coeff in small_rational()) {
        // x + (-x) should yield empty coeffs for x
        let mut coeffs_a = BTreeMap::new();
        coeffs_a.insert("x".to_string(), coeff);
        let a = NormalizedConstraint {
            coeffs: coeffs_a,
            constant: ExternalRational::ZERO,
            strict: false,
        };

        let mut coeffs_b = BTreeMap::new();
        coeffs_b.insert("x".to_string(), coeff.neg());
        let b = NormalizedConstraint {
            coeffs: coeffs_b,
            constant: ExternalRational::ZERO,
            strict: false,
        };

        let result = a.add(b).unwrap();
        prop_assert!(
            !result.coeffs.contains_key("x"),
            "opposite coefficients should cancel and be removed"
        );
    }

    #[test]
    fn add_strictness_propagates(a in constraint(), b in constraint()) {
        // strict || strict should be the result
        let result = a.clone().add(b.clone()).unwrap();
        prop_assert_eq!(
            result.strict,
            a.strict || b.strict,
            "strictness should propagate via OR"
        );
    }

    #[test]
    fn add_combines_constants(const_a in small_rational(), const_b in small_rational()) {
        let a = NormalizedConstraint {
            coeffs: BTreeMap::new(),
            constant: const_a,
            strict: false,
        };
        let b = NormalizedConstraint {
            coeffs: BTreeMap::new(),
            constant: const_b,
            strict: false,
        };
        let result = a.add(b).unwrap();
        let expected = const_a.add(const_b).unwrap();
        prop_assert_eq!(result.constant, expected, "constants should add correctly");
    }

    #[test]
    fn add_associative(a in constraint(), b in constraint(), c in constraint()) {
        // (a + b) + c should equal a + (b + c)
        let ab_c = a.clone().add(b.clone()).and_then(|ab| ab.add(c.clone()));
        let a_bc = b.clone().add(c.clone()).and_then(|bc| a.clone().add(bc));
        match (ab_c, a_bc) {
            (Ok(ab_c), Ok(a_bc)) => {
                prop_assert_eq!(ab_c.coeffs, a_bc.coeffs, "add should be associative (coeffs)");
                prop_assert_eq!(ab_c.constant, a_bc.constant, "add should be associative (constant)");
                prop_assert_eq!(ab_c.strict, a_bc.strict, "add should be associative (strict)");
            }
            (Err(_), Err(_)) => {} // both overflow is consistent
            _ => prop_assert!(false, "inconsistent overflow behavior in associativity"),
        }
    }

}
