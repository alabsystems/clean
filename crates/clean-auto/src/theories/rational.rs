// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Rational and delta-rational number types for arithmetic theory solvers.
//!
//! `Rational` provides exact rational arithmetic (numerator/denominator).
//! All arithmetic uses i128 intermediates to prevent silent overflow (#2324).
//! Operations return `Option<Rational>` — `None` signals that the normalized
//! result does not fit in i64 and the caller should treat the computation
//! as incomplete (not unsound).
//!
//! `DeltaRational` extends rationals with an infinitesimal component for
//! encoding strict inequalities without degenerate simplex pivots.
//!
//! # References
//!
//! - Dutertre & de Moura, "A Fast Linear-Arithmetic Solver for DPLL(T)", CAV 2006
//!   (Section 3.2: infinitesimals for strict inequalities)

use std::cmp::Ordering;

/// A rational number represented as numerator/denominator.
///
/// Internally uses i64 for storage (fast, Copy). Arithmetic uses i128
/// intermediates and returns `Option` to prevent silent overflow (#2324).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Rational {
    num: i64,
    den: i64, // Always positive
}

impl Rational {
    pub const ZERO: Rational = Rational { num: 0, den: 1 };
    pub const ONE: Rational = Rational { num: 1, den: 1 };
    pub const NEG_ONE: Rational = Rational { num: -1, den: 1 };

    /// Create a new rational number from i64 values, automatically normalized.
    ///
    /// Panics on division by zero. Sign normalization is performed in `i128`
    /// so that flipping the sign of `i64::MIN` (which has no positive `i64`
    /// representation) cannot overflow. In the rare case where the normalized
    /// magnitude still does not fit in `i64` after GCD reduction (only possible
    /// when `num == i64::MIN` or `den == i64::MIN` with a sign flip and no
    /// reduction), the value saturates to the in-range boundary, matching the
    /// `saturating_abs` approximation policy already used by `abs`.
    pub fn new(num: i64, den: i64) -> Self {
        assert!(den != 0, "Division by zero in Rational::new");
        // Sign-normalize in i128 so `-i64::MIN` cannot overflow. For every input
        // that did not overflow before, the i128 path produces identical results.
        let (num, den): (i128, i128) = if den < 0 {
            (-(num as i128), -(den as i128))
        } else {
            (num as i128, den as i128)
        };
        let g = Self::gcd_128(num.unsigned_abs(), den.unsigned_abs());
        let num = num / (g as i128);
        let den = den / (g as i128);
        Rational {
            num: i64::try_from(num).unwrap_or(if num < 0 { i64::MIN } else { i64::MAX }),
            den: i64::try_from(den).unwrap_or(i64::MAX),
        }
    }

    /// Create from i128 intermediates, returning None if the normalized result
    /// does not fit in i64. Used by arithmetic operations to prevent overflow.
    fn new_checked(num: i128, den: i128) -> Option<Self> {
        if den == 0 {
            return None;
        }
        let (num, den) = if den < 0 { (-num, -den) } else { (num, den) };
        let g = Self::gcd_128(num.unsigned_abs(), den.unsigned_abs());
        let num = num / (g as i128);
        let den = den / (g as i128);
        // After GCD normalization, check if result fits in i64
        let num = i64::try_from(num).ok()?;
        let den = i64::try_from(den).ok()?;
        Some(Rational { num, den })
    }

    /// Create from an integer
    pub fn from_int(n: i64) -> Self {
        Rational { num: n, den: 1 }
    }

    /// GCD using Euclidean algorithm (u64 version for construction)
    fn gcd(mut a: u64, mut b: u64) -> u64 {
        while b != 0 {
            let t = b;
            b = a % b;
            a = t;
        }
        if a == 0 {
            1
        } else {
            a
        }
    }

    /// GCD using Euclidean algorithm (u128 version for checked operations)
    fn gcd_128(mut a: u128, mut b: u128) -> u128 {
        while b != 0 {
            let t = b;
            b = a % b;
            a = t;
        }
        if a == 0 {
            1
        } else {
            a
        }
    }

    pub fn is_zero(&self) -> bool {
        self.num == 0
    }

    pub fn is_positive(&self) -> bool {
        self.num > 0
    }

    pub fn is_negative(&self) -> bool {
        self.num < 0
    }

    #[must_use]
    pub fn abs(&self) -> Self {
        Rational {
            num: self.num.saturating_abs(),
            den: self.den,
        }
    }

    #[must_use]
    pub fn neg(&self) -> Self {
        Rational {
            num: self.num.wrapping_neg(),
            den: self.den,
        }
    }

    /// Checked negation. Returns None if num == i64::MIN (no i64 positive
    /// representation).
    #[must_use]
    pub fn checked_neg(&self) -> Option<Self> {
        Some(Rational {
            num: self.num.checked_neg()?,
            den: self.den,
        })
    }

    /// Add two rationals. Returns None on overflow after normalization.
    #[must_use]
    pub fn add(&self, other: &Self) -> Option<Rational> {
        let num =
            (self.num as i128) * (other.den as i128) + (other.num as i128) * (self.den as i128);
        let den = (self.den as i128) * (other.den as i128);
        Self::new_checked(num, den)
    }

    /// Subtract two rationals. Returns None on overflow after normalization.
    #[must_use]
    pub fn sub(&self, other: &Self) -> Option<Rational> {
        let num =
            (self.num as i128) * (other.den as i128) - (other.num as i128) * (self.den as i128);
        let den = (self.den as i128) * (other.den as i128);
        Self::new_checked(num, den)
    }

    /// Multiply two rationals. Returns None on overflow after normalization.
    #[must_use]
    pub fn mul(&self, other: &Self) -> Option<Rational> {
        let num = (self.num as i128) * (other.num as i128);
        let den = (self.den as i128) * (other.den as i128);
        Self::new_checked(num, den)
    }

    /// Divide two rationals. Returns None on division by zero or overflow.
    #[must_use]
    pub fn div(&self, other: &Self) -> Option<Rational> {
        if other.num == 0 {
            return None;
        }
        let num = (self.num as i128) * (other.den as i128);
        let den = (self.den as i128) * (other.num as i128);
        Self::new_checked(num, den)
    }

    /// Numerator (for external inspection)
    pub fn numerator(&self) -> i64 {
        self.num
    }

    /// Denominator (for external inspection)
    pub fn denominator(&self) -> i64 {
        self.den
    }
}

impl PartialOrd for Rational {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Rational {
    fn cmp(&self, other: &Self) -> Ordering {
        // a/b vs c/d  =>  a*d vs c*b (using i128 to prevent overflow #2324)
        let lhs = (self.num as i128) * (other.den as i128);
        let rhs = (other.num as i128) * (self.den as i128);
        lhs.cmp(&rhs)
    }
}

impl std::fmt::Display for Rational {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.den == 1 {
            write!(f, "{}", self.num)
        } else {
            write!(f, "{}/{}", self.num, self.den)
        }
    }
}

/// A value with infinitesimal component: represents `real + delta * epsilon`
/// where epsilon is a positive infinitesimal (#2334).
///
/// Used to encode strict inequalities without degenerate simplex pivots.
/// `x < b` becomes `x <= (b, -1)` meaning `x <= b - epsilon`.
/// With this encoding, ALL bounds are non-strict in the simplex, eliminating
/// the pivot cycling that occurs when variables sit exactly at strict boundaries.
///
/// Reference: Dutertre & de Moura, "A Fast Linear-Arithmetic Solver for DPLL(T)",
/// CAV 2006, Section 3.2.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct DeltaRational {
    pub real: Rational,
    pub delta: Rational,
}

impl DeltaRational {
    pub const ZERO: DeltaRational = DeltaRational {
        real: Rational::ZERO,
        delta: Rational::ZERO,
    };

    /// Create from a plain rational (zero delta component)
    pub fn from_rational(r: Rational) -> Self {
        DeltaRational {
            real: r,
            delta: Rational::ZERO,
        }
    }

    /// Create with explicit real and delta components
    pub fn new(real: Rational, delta: Rational) -> Self {
        DeltaRational { real, delta }
    }

    #[must_use]
    pub fn add(&self, other: &Self) -> Option<Self> {
        Some(DeltaRational {
            real: self.real.add(&other.real)?,
            delta: self.delta.add(&other.delta)?,
        })
    }

    #[must_use]
    pub fn sub(&self, other: &Self) -> Option<Self> {
        Some(DeltaRational {
            real: self.real.sub(&other.real)?,
            delta: self.delta.sub(&other.delta)?,
        })
    }

    /// Multiply by a plain rational coefficient: `(r, d) * c = (r*c, d*c)`
    #[must_use]
    pub fn mul_rational(&self, c: &Rational) -> Option<Self> {
        Some(DeltaRational {
            real: self.real.mul(c)?,
            delta: self.delta.mul(c)?,
        })
    }

    /// Divide by a plain rational coefficient: `(r, d) / c = (r/c, d/c)`
    #[must_use]
    pub fn div_rational(&self, c: &Rational) -> Option<Self> {
        Some(DeltaRational {
            real: self.real.div(c)?,
            delta: self.delta.div(c)?,
        })
    }
}

impl PartialOrd for DeltaRational {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for DeltaRational {
    fn cmp(&self, other: &Self) -> Ordering {
        match self.real.cmp(&other.real) {
            Ordering::Equal => self.delta.cmp(&other.delta),
            ord => ord,
        }
    }
}

impl std::fmt::Display for DeltaRational {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.delta.is_zero() {
            write!(f, "{}", self.real)
        } else if self.delta.is_negative() {
            write!(f, "{}{}ε", self.real, self.delta)
        } else {
            write!(f, "{}+{}ε", self.real, self.delta)
        }
    }
}
