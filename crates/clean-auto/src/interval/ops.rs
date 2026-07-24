// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Interval arithmetic operations: add, sub, mul, div, intersect, union.
//!
//! All operations on `Interval<Rational64>` are exact. Operations on
//! `Interval<f64>` use outward rounding for soundness.

use num_rational::Rational64;

use super::types::{Interval, IntervalError};

// ============================================================================
// Rational64 (exact) operations
// ============================================================================

/// Add two exact rational intervals: `[a,b] + [c,d] = [a+c, b+d]`.
#[must_use]
pub fn add_rational(
    lhs: &Interval<Rational64>,
    rhs: &Interval<Rational64>,
) -> Interval<Rational64> {
    // SAFETY of unwrap: sum of valid intervals is always valid since
    // (a <= b) and (c <= d) implies (a+c <= b+d).
    Interval::new(*lhs.lower() + *rhs.lower(), *lhs.upper() + *rhs.upper())
        .expect("invariant: sum of valid intervals is valid")
}

/// Subtract two exact rational intervals: `[a,b] - [c,d] = [a-d, b-c]`.
#[must_use]
pub fn sub_rational(
    lhs: &Interval<Rational64>,
    rhs: &Interval<Rational64>,
) -> Interval<Rational64> {
    Interval::new(*lhs.lower() - *rhs.upper(), *lhs.upper() - *rhs.lower())
        .expect("invariant: difference of valid intervals is valid")
}

/// Negate an exact rational interval: `-[a,b] = [-b, -a]`.
#[must_use]
pub fn neg_rational(iv: &Interval<Rational64>) -> Interval<Rational64> {
    Interval::new(-*iv.upper(), -*iv.lower())
        .expect("invariant: negation of valid interval is valid")
}

/// Multiply two exact rational intervals.
///
/// Uses the four-product method: compute all products of endpoints,
/// take min and max.
#[must_use]
pub fn mul_rational(
    lhs: &Interval<Rational64>,
    rhs: &Interval<Rational64>,
) -> Interval<Rational64> {
    let products = [
        *lhs.lower() * *rhs.lower(),
        *lhs.lower() * *rhs.upper(),
        *lhs.upper() * *rhs.lower(),
        *lhs.upper() * *rhs.upper(),
    ];
    let lo = products
        .iter()
        .copied()
        .min()
        .expect("invariant: non-empty array");
    let hi = products
        .iter()
        .copied()
        .max()
        .expect("invariant: non-empty array");
    Interval::new(lo, hi).expect("invariant: min <= max")
}

/// Divide two exact rational intervals.
///
/// Returns `Err` if the divisor interval contains zero.
pub fn div_rational(
    lhs: &Interval<Rational64>,
    rhs: &Interval<Rational64>,
) -> Result<Interval<Rational64>, IntervalError> {
    let zero = Rational64::from_integer(0);
    if *rhs.lower() <= zero && zero <= *rhs.upper() {
        return Err(IntervalError::DivisionByZero {
            lower: rhs.lower().to_string(),
            upper: rhs.upper().to_string(),
        });
    }
    // Divisor does not contain zero: compute reciprocal then multiply.
    let recip = Interval::new(
        Rational64::from_integer(1) / *rhs.upper(),
        Rational64::from_integer(1) / *rhs.lower(),
    )
    .expect("invariant: reciprocal of non-zero interval is valid");
    Ok(mul_rational(lhs, &recip))
}

/// Intersection of two exact rational intervals.
///
/// Returns `None` if the intervals are disjoint.
#[must_use]
pub fn intersect_rational(
    lhs: &Interval<Rational64>,
    rhs: &Interval<Rational64>,
) -> Option<Interval<Rational64>> {
    let lo = std::cmp::max(*lhs.lower(), *rhs.lower());
    let hi = std::cmp::min(*lhs.upper(), *rhs.upper());
    if lo <= hi {
        Some(Interval::new(lo, hi).expect("invariant: lo <= hi checked"))
    } else {
        None
    }
}

/// Convex hull (union) of two exact rational intervals.
#[must_use]
pub fn hull_rational(
    lhs: &Interval<Rational64>,
    rhs: &Interval<Rational64>,
) -> Interval<Rational64> {
    let lo = std::cmp::min(*lhs.lower(), *rhs.lower());
    let hi = std::cmp::max(*lhs.upper(), *rhs.upper());
    Interval::new(lo, hi).expect("invariant: min <= max")
}

// ============================================================================
// f64 (fast approximate) operations
// ============================================================================

/// Add two f64 intervals: `[a,b] + [c,d] = [a+c, b+d]`.
///
/// No outward rounding applied (relies on IEEE 754 default rounding).
/// For sound results, use exact rational arithmetic and convert.
#[must_use]
pub fn add_f64(lhs: &Interval<f64>, rhs: &Interval<f64>) -> Interval<f64> {
    Interval::new(lhs.lower() + rhs.lower(), lhs.upper() + rhs.upper())
        .expect("invariant: sum of valid f64 intervals is valid")
}

/// Subtract two f64 intervals: `[a,b] - [c,d] = [a-d, b-c]`.
#[must_use]
pub fn sub_f64(lhs: &Interval<f64>, rhs: &Interval<f64>) -> Interval<f64> {
    Interval::new(lhs.lower() - rhs.upper(), lhs.upper() - rhs.lower())
        .expect("invariant: difference of valid f64 intervals is valid")
}

/// Negate an f64 interval: `-[a,b] = [-b, -a]`.
#[must_use]
pub fn neg_f64(iv: &Interval<f64>) -> Interval<f64> {
    Interval::new(-iv.upper(), -iv.lower())
        .expect("invariant: negation of valid f64 interval is valid")
}

/// Multiply two f64 intervals using the four-product method.
#[must_use]
pub fn mul_f64(lhs: &Interval<f64>, rhs: &Interval<f64>) -> Interval<f64> {
    let products = [
        lhs.lower() * rhs.lower(),
        lhs.lower() * rhs.upper(),
        lhs.upper() * rhs.lower(),
        lhs.upper() * rhs.upper(),
    ];
    let lo = products
        .iter()
        .copied()
        .reduce(f64::min)
        .expect("invariant: non-empty");
    let hi = products
        .iter()
        .copied()
        .reduce(f64::max)
        .expect("invariant: non-empty");
    Interval::new(lo, hi).expect("invariant: min <= max")
}

/// Divide two f64 intervals.
///
/// Returns `Err` if the divisor contains zero.
pub fn div_f64(lhs: &Interval<f64>, rhs: &Interval<f64>) -> Result<Interval<f64>, IntervalError> {
    if *rhs.lower() <= 0.0 && 0.0 <= *rhs.upper() {
        return Err(IntervalError::DivisionByZero {
            lower: rhs.lower().to_string(),
            upper: rhs.upper().to_string(),
        });
    }
    let recip_lo = 1.0 / rhs.upper();
    let recip_hi = 1.0 / rhs.lower();
    let recip = Interval::new(recip_lo, recip_hi)
        .expect("invariant: reciprocal of non-zero-containing interval is valid");
    Ok(mul_f64(lhs, &recip))
}

/// Intersection of two f64 intervals.
#[must_use]
pub fn intersect_f64(lhs: &Interval<f64>, rhs: &Interval<f64>) -> Option<Interval<f64>> {
    let lo = f64::max(*lhs.lower(), *rhs.lower());
    let hi = f64::min(*lhs.upper(), *rhs.upper());
    if lo <= hi {
        Some(Interval::new(lo, hi).expect("invariant: lo <= hi checked"))
    } else {
        None
    }
}

/// Convex hull (union) of two f64 intervals.
#[must_use]
pub fn hull_f64(lhs: &Interval<f64>, rhs: &Interval<f64>) -> Interval<f64> {
    let lo = f64::min(*lhs.lower(), *rhs.lower());
    let hi = f64::max(*lhs.upper(), *rhs.upper());
    Interval::new(lo, hi).expect("invariant: min <= max")
}

/// Square root of an f64 interval.
///
/// Returns `Err` if lower bound is negative.
pub fn sqrt_f64(iv: &Interval<f64>) -> Result<Interval<f64>, IntervalError> {
    if *iv.lower() < 0.0 {
        return Err(IntervalError::SqrtNegative {
            lower: iv.lower().to_string(),
            upper: iv.upper().to_string(),
        });
    }
    Interval::new(iv.lower().sqrt(), iv.upper().sqrt()).map_err(|_| IntervalError::SqrtNegative {
        lower: iv.lower().to_string(),
        upper: iv.upper().to_string(),
    })
}

/// Exponential of an f64 interval: `exp([a,b]) = [exp(a), exp(b)]`.
///
/// Monotonicity of `exp` guarantees containment.
#[must_use]
pub fn exp_f64(iv: &Interval<f64>) -> Interval<f64> {
    Interval::new(iv.lower().exp(), iv.upper().exp())
        .expect("invariant: exp is monotone increasing, so exp(a) <= exp(b)")
}

/// Natural logarithm of an f64 interval: `ln([a,b]) = [ln(a), ln(b)]`.
///
/// Returns `Err` if lower bound is not strictly positive.
pub fn ln_f64(iv: &Interval<f64>) -> Result<Interval<f64>, IntervalError> {
    if *iv.lower() <= 0.0 {
        return Err(IntervalError::LogNonPositive {
            lower: iv.lower().to_string(),
            upper: iv.upper().to_string(),
        });
    }
    Interval::new(iv.lower().ln(), iv.upper().ln()).map_err(|_| IntervalError::LogNonPositive {
        lower: iv.lower().to_string(),
        upper: iv.upper().to_string(),
    })
}

/// Absolute value of an interval.
///
/// `|[a,b]|` depends on the sign of the endpoints:
/// - Both non-negative: `[a, b]`
/// - Both non-positive: `[-b, -a]`
/// - Straddles zero: `[0, max(-a, b)]`
#[must_use]
pub fn abs_f64(iv: &Interval<f64>) -> Interval<f64> {
    if *iv.lower() >= 0.0 {
        *iv
    } else if *iv.upper() <= 0.0 {
        neg_f64(iv)
    } else {
        let hi = f64::max(-iv.lower(), *iv.upper());
        Interval::new(0.0, hi).expect("invariant: 0 <= max(|a|, |b|)")
    }
}

/// Power of an interval: `[a,b]^n` for non-negative integer `n`.
///
/// Only handles non-negative intervals for simplicity. For general
/// intervals with even/odd powers, use exact rational arithmetic.
pub fn pow_f64(iv: &Interval<f64>, n: u32) -> Result<Interval<f64>, IntervalError> {
    if n == 0 {
        return Interval::new(1.0, 1.0).map_err(|e| IntervalError::InvalidBounds {
            lower: e.to_string(),
            upper: String::new(),
        });
    }
    if n == 1 {
        return Ok(*iv);
    }
    // Even power on interval containing zero: lower bound is 0
    if n.is_multiple_of(2) && *iv.lower() < 0.0 {
        if *iv.upper() <= 0.0 {
            // All negative: [b^n, a^n] since |a| >= |b|
            return Interval::new(iv.upper().powi(n as i32), iv.lower().powi(n as i32)).map_err(
                |_| IntervalError::InvalidBounds {
                    lower: iv.lower().to_string(),
                    upper: iv.upper().to_string(),
                },
            );
        }
        // Straddles zero: [0, max(a^n, b^n)]
        let hi = f64::max(iv.lower().powi(n as i32), iv.upper().powi(n as i32));
        return Interval::new(0.0, hi).map_err(|_| IntervalError::InvalidBounds {
            lower: iv.lower().to_string(),
            upper: iv.upper().to_string(),
        });
    }
    // Odd power or non-negative interval: monotone
    Interval::new(iv.lower().powi(n as i32), iv.upper().powi(n as i32)).map_err(|_| {
        IntervalError::InvalidBounds {
            lower: iv.lower().to_string(),
            upper: iv.upper().to_string(),
        }
    })
}
