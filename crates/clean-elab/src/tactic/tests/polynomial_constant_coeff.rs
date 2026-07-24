// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constant-coefficient extraction regressions for `Polynomial::as_constant_coeff()`.

use std::collections::HashMap;

use super::super::polynomial::Polynomial;

#[test]
fn test_polynomial_as_constant_coeff_zero() {
    let p = Polynomial::zero();
    assert_eq!(p.as_constant_coeff(), Some((0, 1)));
}

#[test]
fn test_polynomial_as_constant_coeff_integer() {
    let p = Polynomial::constant(3, 1);
    assert_eq!(p.as_constant_coeff(), Some((3, 1)));
}

#[test]
fn test_polynomial_as_constant_coeff_rational() {
    let p = Polynomial::constant(1, 2);
    assert_eq!(p.as_constant_coeff(), Some((1, 2)));
}

#[test]
fn test_polynomial_as_constant_coeff_with_variable() {
    let p = Polynomial::var(0).add(&Polynomial::constant(1, 1));
    assert!(
        p.as_constant_coeff().is_none(),
        "polynomial with variables should return None"
    );
}

#[test]
fn test_polynomial_as_constant_coeff_negative() {
    let p = Polynomial::constant(-5, 1);
    assert_eq!(p.as_constant_coeff(), Some((-5, 1)));
}

#[test]
fn test_polynomial_as_constant_coeff_manual_hashmap_constant() {
    let p = Polynomial {
        terms: HashMap::from([(vec![], (7, 3))]),
    };
    assert_eq!(p.as_constant_coeff(), Some((7, 3)));
}
