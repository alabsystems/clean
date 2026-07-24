// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Interval arithmetic operations over `Rational64`.
//!
//! All 13 operations required by the interval arithmetic specification:
//! add, sub, mul, div, neg, abs, pow, sqrt, contains, width, midpoint,
//! intersect, hull.
//!
//! Operations on `Rational64` are exact (no rounding errors).

use num_rational::Rational64;

use super::types::{Interval, IntervalError};

// ---- 1. Addition ----

/// `[a.lo + b.lo, a.hi + b.hi]`
#[must_use]
pub fn add(a: &Interval, b: &Interval) -> Interval {
    // Invariant: (a.lo <= a.hi) and (b.lo <= b.hi) implies
    // (a.lo + b.lo <= a.hi + b.hi).
    Interval::new(a.lo() + b.lo(), a.hi() + b.hi())
        .expect("invariant: sum of valid intervals is valid")
}

// ---- 2. Subtraction ----

/// `[a.lo - b.hi, a.hi - b.lo]`
#[must_use]
pub fn sub(a: &Interval, b: &Interval) -> Interval {
    Interval::new(a.lo() - b.hi(), a.hi() - b.lo())
        .expect("invariant: difference of valid intervals is valid")
}

// ---- 3. Multiplication ----

/// Four-corner product: `[min(corners), max(corners)]` where
/// corners = `{a.lo*b.lo, a.lo*b.hi, a.hi*b.lo, a.hi*b.hi}`.
#[must_use]
pub fn mul(a: &Interval, b: &Interval) -> Interval {
    let products = [
        a.lo() * b.lo(),
        a.lo() * b.hi(),
        a.hi() * b.lo(),
        a.hi() * b.hi(),
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

// ---- 4. Division ----

/// `a * [1/b.hi, 1/b.lo]` when `0` is not in `b`.
pub fn div(a: &Interval, b: &Interval) -> Result<Interval, IntervalError> {
    let zero = Rational64::from_integer(0);
    if b.lo() <= zero && zero <= b.hi() {
        return Err(IntervalError::DivisionByZero {
            lo: b.lo().to_string(),
            hi: b.hi().to_string(),
        });
    }
    let one = Rational64::from_integer(1);
    let recip = Interval::new(one / b.hi(), one / b.lo())
        .expect("invariant: reciprocal of non-zero interval is valid");
    Ok(mul(a, &recip))
}

// ---- 5. Negation ----

/// `[-a.hi, -a.lo]`
#[must_use]
pub fn neg(a: &Interval) -> Interval {
    Interval::new(-a.hi(), -a.lo()).expect("invariant: negation of valid interval is valid")
}

// ---- 6. Absolute value ----

/// - Both non-negative: `[a.lo, a.hi]`
/// - Both non-positive: `[-a.hi, -a.lo]`
/// - Straddles zero: `[0, max(-a.lo, a.hi)]`
#[must_use]
pub fn abs(a: &Interval) -> Interval {
    let zero = Rational64::from_integer(0);
    if a.lo() >= zero {
        *a
    } else if a.hi() <= zero {
        neg(a)
    } else {
        let hi = std::cmp::max(-a.lo(), a.hi());
        Interval::new(zero, hi).expect("invariant: 0 <= max(|lo|, |hi|)")
    }
}

// ---- 7. Power (non-negative integer exponent) ----

/// `a^n` for non-negative integer `n`.
///
/// - `n = 0`: `[1, 1]`
/// - `n = 1`: `a`
/// - Even `n`, all negative: `[a.hi^n, a.lo^n]`
/// - Even `n`, straddles zero: `[0, max(a.lo^n, a.hi^n)]`
/// - Otherwise (odd or non-negative): `[a.lo^n, a.hi^n]`
pub fn pow(a: &Interval, n: u32) -> Result<Interval, IntervalError> {
    let one = Rational64::from_integer(1);
    let zero = Rational64::from_integer(0);
    if n == 0 {
        return Ok(Interval::point(one));
    }
    if n == 1 {
        return Ok(*a);
    }

    let lo_pow = rational_pow(a.lo(), n);
    let hi_pow = rational_pow(a.hi(), n);

    if n.is_multiple_of(2) && a.lo() < zero {
        if a.hi() <= zero {
            // All negative, even power reverses order
            Interval::new(hi_pow, lo_pow)
        } else {
            // Straddles zero, even power
            let max_pow = std::cmp::max(lo_pow, hi_pow);
            Interval::new(zero, max_pow)
        }
    } else {
        // Odd power or non-negative interval: monotone
        Interval::new(lo_pow, hi_pow)
    }
    .map_err(|_| IntervalError::InvalidBounds {
        lo: a.lo().to_string(),
        hi: a.hi().to_string(),
    })
}

/// Raise a `Rational64` to a `u32` power.
fn rational_pow(base: Rational64, exp: u32) -> Rational64 {
    let mut result = Rational64::from_integer(1);
    for _ in 0..exp {
        result *= base;
    }
    result
}

// ---- 8. Square root (rational approximation) ----

/// Rational square root approximation for intervals.
///
/// Uses f64 sqrt as a seed, then converts to rational bounds that
/// are provably sound (lo rounds down, hi rounds up). This avoids
/// the overflow issues of pure Newton iteration on `Rational64`.
///
/// Returns `Err` if `a.lo() < 0`.
pub fn sqrt(a: &Interval) -> Result<Interval, IntervalError> {
    let zero = Rational64::from_integer(0);
    if a.lo() < zero {
        return Err(IntervalError::SqrtNegative {
            lo: a.lo().to_string(),
            hi: a.hi().to_string(),
        });
    }
    let sqrt_lo = rational_sqrt_down(a.lo());
    let sqrt_hi = rational_sqrt_up(a.hi());
    Interval::new(sqrt_lo, sqrt_hi).map_err(|_| IntervalError::SqrtNegative {
        lo: a.lo().to_string(),
        hi: a.hi().to_string(),
    })
}

/// Compute a rational underestimate of `sqrt(x)` (i.e., result^2 <= x).
///
/// Strategy: use f64 sqrt, convert to rational, then verify and adjust.
fn rational_sqrt_down(x: Rational64) -> Rational64 {
    let zero = Rational64::from_integer(0);
    if x == zero {
        return zero;
    }
    // Use f64 to get a good approximation
    let x_f64 = *x.numer() as f64 / *x.denom() as f64;
    let sqrt_f64 = x_f64.sqrt();

    // Convert to rational with bounded denominator (1000) to avoid overflow
    let denom = 1000i64;
    let numer = (sqrt_f64 * denom as f64).floor() as i64;
    let mut guess = Rational64::new(numer.max(0), denom);

    // Verify guess^2 <= x; if not, decrease
    while guess * guess > x && guess > zero {
        guess = Rational64::new(*guess.numer() - 1, *guess.denom());
    }
    guess
}

/// Compute a rational overestimate of `sqrt(x)` (i.e., result^2 >= x).
///
/// Strategy: use f64 sqrt, convert to rational, then verify and adjust.
fn rational_sqrt_up(x: Rational64) -> Rational64 {
    let zero = Rational64::from_integer(0);
    if x == zero {
        return zero;
    }
    let x_f64 = *x.numer() as f64 / *x.denom() as f64;
    let sqrt_f64 = x_f64.sqrt();

    // Convert to rational with bounded denominator (1000) to avoid overflow
    let denom = 1000i64;
    let numer = (sqrt_f64 * denom as f64).ceil() as i64;
    let mut guess = Rational64::new(numer.max(1), denom);

    // Verify guess^2 >= x; if not, increase
    while guess * guess < x {
        guess = Rational64::new(*guess.numer() + 1, *guess.denom());
    }
    guess
}

// ---- 9. Contains (already on Interval type) ----
// See `Interval::contains` in types.rs

// ---- 10. Width (already on Interval type) ----
// See `Interval::width` in types.rs

// ---- 11. Midpoint (already on Interval type) ----
// See `Interval::midpoint` in types.rs

// ---- 12. Intersection ----

/// `[max(a.lo, b.lo), min(a.hi, b.hi)]` if non-empty.
pub fn intersect(a: &Interval, b: &Interval) -> Result<Interval, IntervalError> {
    let lo = std::cmp::max(a.lo(), b.lo());
    let hi = std::cmp::min(a.hi(), b.hi());
    if lo <= hi {
        Ok(Interval::new(lo, hi).expect("invariant: lo <= hi checked"))
    } else {
        Err(IntervalError::DisjointIntervals {
            lo1: a.lo().to_string(),
            hi1: a.hi().to_string(),
            lo2: b.lo().to_string(),
            hi2: b.hi().to_string(),
        })
    }
}

// ---- 13. Hull (convex union) ----

/// `[min(a.lo, b.lo), max(a.hi, b.hi)]`
#[must_use]
pub fn hull(a: &Interval, b: &Interval) -> Interval {
    let lo = std::cmp::min(a.lo(), b.lo());
    let hi = std::cmp::max(a.hi(), b.hi());
    Interval::new(lo, hi).expect("invariant: min <= max")
}
