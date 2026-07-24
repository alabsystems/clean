// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_rational_basic() {
    let a = Rational::new(1, 2);
    let b = Rational::new(1, 3);

    // 1/2 + 1/3 = 5/6
    let sum = a.add(&b).unwrap();
    assert_eq!(sum, Rational::new(5, 6));

    // 1/2 - 1/3 = 1/6
    let diff = a.sub(&b).unwrap();
    assert_eq!(diff, Rational::new(1, 6));

    // 1/2 * 1/3 = 1/6
    let prod = a.mul(&b).unwrap();
    assert_eq!(prod, Rational::new(1, 6));

    // 1/2 / 1/3 = 3/2
    let quot = a.div(&b).unwrap();
    assert_eq!(quot, Rational::new(3, 2));
}

#[test]
fn test_rational_comparison() {
    let a = Rational::new(1, 2);
    let b = Rational::new(1, 3);
    let c = Rational::new(2, 4); // = 1/2

    assert!(a > b);
    assert!(b < a);
    assert_eq!(a, c);
}

#[test]
fn test_rational_normalization() {
    let a = Rational::new(2, 4);
    let b = Rational::new(-3, -6);
    let c = Rational::new(-2, 4);

    assert_eq!(a, Rational::new(1, 2));
    assert_eq!(b, Rational::new(1, 2));
    assert_eq!(c, Rational::new(-1, 2));
}

#[test]
fn test_delta_rational_ordering() {
    let a = DeltaRational::new(Rational::from_int(5), Rational::ZERO);
    let b = DeltaRational::new(Rational::from_int(5), Rational::NEG_ONE);
    let c = DeltaRational::new(Rational::from_int(4), Rational::ONE);

    // (5, 0) > (5, -1) — same real, higher delta
    assert!(a > b);
    // (5, -1) > (4, 1) — higher real wins
    assert!(b > c);
    // (5, 0) == (5, 0)
    assert_eq!(a, DeltaRational::from_rational(Rational::from_int(5)));
}

#[test]
fn test_delta_rational_arithmetic() {
    let a = DeltaRational::new(Rational::from_int(3), Rational::ONE);
    let b = DeltaRational::new(Rational::from_int(1), Rational::NEG_ONE);

    // (3, 1) + (1, -1) = (4, 0)
    let sum = a.add(&b).unwrap();
    assert_eq!(sum.real, Rational::from_int(4));
    assert_eq!(sum.delta, Rational::ZERO);

    // (3, 1) - (1, -1) = (2, 2)
    let diff = a.sub(&b).unwrap();
    assert_eq!(diff.real, Rational::from_int(2));
    assert_eq!(diff.delta, Rational::from_int(2));

    // (3, 1) * 2 = (6, 2)
    let scaled = a.mul_rational(&Rational::from_int(2)).unwrap();
    assert_eq!(scaled.real, Rational::from_int(6));
    assert_eq!(scaled.delta, Rational::from_int(2));

    // Display: positive delta shows +, negative delta shows -
    assert_eq!(format!("{}", a), "3+1ε");
    assert_eq!(format!("{}", b), "1-1ε");
    assert_eq!(
        format!("{}", DeltaRational::from_rational(Rational::from_int(7))),
        "7"
    );
}
