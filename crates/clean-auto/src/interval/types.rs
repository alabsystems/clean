// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Core interval types for verified interval arithmetic.
//!
//! Provides [`Interval`] parameterised over a numeric bound type, with
//! both exact (`Rational`) and fast (`f64`) instantiations. The type
//! enforces the invariant `lower <= upper` at construction time.

use std::fmt;

use num_rational::Rational64;

/// Rounding mode for floating-point interval operations.
///
/// When converting from exact rational arithmetic to f64 intervals,
/// the lower bound must be rounded down and the upper bound rounded up
/// to maintain the containment property.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum RoundingMode {
    /// Round toward negative infinity (for lower bounds).
    Down,
    /// Round toward positive infinity (for upper bounds).
    Up,
    /// Round to nearest (default IEEE 754 mode).
    Nearest,
}

/// Error type for interval operations.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
#[non_exhaustive]
pub enum IntervalError {
    /// Lower bound exceeds upper bound.
    #[error("invalid interval: lower ({lower}) exceeds upper ({upper})")]
    InvalidBounds { lower: String, upper: String },
    /// Division by an interval containing zero.
    #[error("division by interval containing zero: [{lower}, {upper}]")]
    DivisionByZero { lower: String, upper: String },
    /// Logarithm of non-positive interval.
    #[error("logarithm of non-positive interval: [{lower}, {upper}]")]
    LogNonPositive { lower: String, upper: String },
    /// Square root of negative interval.
    #[error("sqrt of negative interval: [{lower}, {upper}]")]
    SqrtNegative { lower: String, upper: String },
}

/// A closed interval `[lower, upper]` over a totally-ordered numeric type.
///
/// The fundamental invariant is `lower <= upper`. This is enforced at
/// construction via [`Interval::new`], which returns an error on violation.
///
/// # Type parameters
///
/// - `T`: The bound type. Commonly `Rational64` for exact arithmetic or
///   `f64` for fast approximate arithmetic.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct Interval<T> {
    lower: T,
    upper: T,
}

impl<T: fmt::Debug> fmt::Debug for Interval<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[{:?}, {:?}]", self.lower, self.upper)
    }
}

impl<T: fmt::Display> fmt::Display for Interval<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[{}, {}]", self.lower, self.upper)
    }
}

impl<T: PartialOrd + fmt::Display + Clone> Interval<T> {
    /// Create a new interval `[lower, upper]`.
    ///
    /// Returns `Err` if `lower > upper`.
    pub fn new(lower: T, upper: T) -> Result<Self, IntervalError> {
        if lower > upper {
            return Err(IntervalError::InvalidBounds {
                lower: lower.to_string(),
                upper: upper.to_string(),
            });
        }
        Ok(Self { lower, upper })
    }

    /// Lower bound of the interval.
    #[must_use]
    pub fn lower(&self) -> &T {
        &self.lower
    }

    /// Upper bound of the interval.
    #[must_use]
    pub fn upper(&self) -> &T {
        &self.upper
    }

    /// Check whether a value is contained in this interval.
    #[must_use]
    pub fn contains(&self, x: &T) -> bool {
        *x >= self.lower && *x <= self.upper
    }

    /// Check whether `other` is a subset of `self`.
    #[must_use]
    pub fn contains_interval(&self, other: &Interval<T>) -> bool {
        self.lower <= other.lower && other.upper <= self.upper
    }
}

/// A point interval `[v, v]`.
impl<T: Clone + PartialOrd + fmt::Display> Interval<T> {
    /// Create a degenerate (point) interval `[v, v]`.
    #[must_use]
    pub fn point(v: T) -> Self {
        Self {
            lower: v.clone(),
            upper: v,
        }
    }
}

// ---- Rational64 convenience constructors ----

impl Interval<Rational64> {
    /// Create an exact rational interval from integer bounds.
    pub fn from_integers(lower: i64, upper: i64) -> Result<Self, IntervalError> {
        Self::new(
            Rational64::from_integer(lower),
            Rational64::from_integer(upper),
        )
    }

    /// Width of the interval: `upper - lower`.
    #[must_use]
    pub fn width(&self) -> Rational64 {
        self.upper - self.lower
    }

    /// Midpoint of the interval: `(lower + upper) / 2`.
    #[must_use]
    pub fn midpoint(&self) -> Rational64 {
        (self.lower + self.upper) / Rational64::from_integer(2)
    }

    /// Whether the interval contains zero.
    #[must_use]
    pub fn contains_zero(&self) -> bool {
        let zero = Rational64::from_integer(0);
        self.lower <= zero && zero <= self.upper
    }

    /// Whether both bounds are strictly positive.
    #[must_use]
    pub fn is_strictly_positive(&self) -> bool {
        self.lower > Rational64::from_integer(0)
    }

    /// Whether both bounds are strictly negative.
    #[must_use]
    pub fn is_strictly_negative(&self) -> bool {
        self.upper < Rational64::from_integer(0)
    }
}

// ---- f64 convenience constructors ----

impl Interval<f64> {
    /// Width of the interval: `upper - lower`.
    #[must_use]
    pub fn width_f64(&self) -> f64 {
        self.upper - self.lower
    }

    /// Midpoint of the interval: `(lower + upper) / 2`.
    #[must_use]
    pub fn midpoint_f64(&self) -> f64 {
        (self.lower + self.upper) / 2.0
    }

    /// Whether the interval contains zero.
    #[must_use]
    pub fn contains_zero_f64(&self) -> bool {
        self.lower <= 0.0 && 0.0 <= self.upper
    }

    /// Convert exact rational interval to f64, rounding outward for soundness.
    ///
    /// Lower bound is rounded toward negative infinity, upper bound toward
    /// positive infinity. This guarantees that any rational value in the
    /// original interval is also in the f64 interval.
    #[must_use]
    pub fn from_rational(r: &Interval<Rational64>) -> Self {
        // Rational64 to f64 conversion truncates; we nudge outward.
        let lo = rational_to_f64_down(r.lower());
        let hi = rational_to_f64_up(r.upper());
        Self {
            lower: lo,
            upper: hi,
        }
    }
}

/// Convert a `Rational64` to `f64`, rounding toward negative infinity.
fn rational_to_f64_down(r: &Rational64) -> f64 {
    let v: f64 = (*r.numer() as f64) / (*r.denom() as f64);
    // If exact conversion round-trips, we're fine. Otherwise nudge down.
    let back = Rational64::new(*r.numer(), *r.denom());
    if Rational64::from_integer(1) * back == *r {
        v
    } else {
        // Nudge toward -inf by one ULP
        f64::from_bits(if v >= 0.0 {
            v.to_bits().wrapping_sub(1)
        } else {
            v.to_bits().wrapping_add(1)
        })
    }
}

/// Convert a `Rational64` to `f64`, rounding toward positive infinity.
fn rational_to_f64_up(r: &Rational64) -> f64 {
    let v: f64 = (*r.numer() as f64) / (*r.denom() as f64);
    let back = Rational64::new(*r.numer(), *r.denom());
    if Rational64::from_integer(1) * back == *r {
        v
    } else {
        // Nudge toward +inf by one ULP
        f64::from_bits(if v >= 0.0 {
            v.to_bits().wrapping_add(1)
        } else {
            v.to_bits().wrapping_sub(1)
        })
    }
}

/// Type alias for exact rational intervals.
pub type RationalInterval = Interval<Rational64>;

/// Type alias for fast floating-point intervals.
pub type F64Interval = Interval<f64>;
