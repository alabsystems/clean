// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Core types for the interval arithmetic library.
//!
//! Provides [`Interval`] over `Rational64` with the invariant `lo <= hi`,
//! enforced at construction time.

use std::fmt;

use num_rational::Rational64;

/// Error type for interval arithmetic operations.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
#[non_exhaustive]
pub enum IntervalError {
    /// Lower bound exceeds upper bound.
    #[error("invalid interval: lo ({lo}) > hi ({hi})")]
    InvalidBounds { lo: String, hi: String },
    /// Division by an interval containing zero.
    #[error("division by interval containing zero: [{lo}, {hi}]")]
    DivisionByZero { lo: String, hi: String },
    /// Square root of interval with negative lower bound.
    #[error("sqrt of negative interval: [{lo}, {hi}]")]
    SqrtNegative { lo: String, hi: String },
    /// Empty intersection (disjoint intervals).
    #[error("disjoint intervals: [{lo1}, {hi1}] and [{lo2}, {hi2}]")]
    DisjointIntervals {
        lo1: String,
        hi1: String,
        lo2: String,
        hi2: String,
    },
}

/// A closed interval `[lo, hi]` over `Rational64`.
///
/// Invariant: `lo <= hi` (enforced at construction).
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct Interval {
    lo: Rational64,
    hi: Rational64,
}

impl fmt::Debug for Interval {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[{:?}, {:?}]", self.lo, self.hi)
    }
}

impl fmt::Display for Interval {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[{}, {}]", self.lo, self.hi)
    }
}

impl Interval {
    /// Create a new interval `[lo, hi]`.
    ///
    /// Returns `Err` if `lo > hi`.
    pub fn new(lo: Rational64, hi: Rational64) -> Result<Self, IntervalError> {
        if lo > hi {
            return Err(IntervalError::InvalidBounds {
                lo: lo.to_string(),
                hi: hi.to_string(),
            });
        }
        Ok(Self { lo, hi })
    }

    /// Create an interval from integer bounds.
    pub fn from_integers(lo: i64, hi: i64) -> Result<Self, IntervalError> {
        Self::new(Rational64::from_integer(lo), Rational64::from_integer(hi))
    }

    /// Create a degenerate (point) interval `[v, v]`.
    #[must_use]
    pub fn point(v: Rational64) -> Self {
        Self { lo: v, hi: v }
    }

    /// Lower bound.
    #[must_use]
    pub fn lo(&self) -> Rational64 {
        self.lo
    }

    /// Upper bound.
    #[must_use]
    pub fn hi(&self) -> Rational64 {
        self.hi
    }

    /// Check whether a value is contained in this interval: `lo <= x <= hi`.
    #[must_use]
    pub fn contains(&self, x: Rational64) -> bool {
        self.lo <= x && x <= self.hi
    }

    /// Check whether `other` is a subset of `self`.
    #[must_use]
    pub fn contains_interval(&self, other: &Interval) -> bool {
        self.lo <= other.lo && other.hi <= self.hi
    }

    /// Width of the interval: `hi - lo`.
    #[must_use]
    pub fn width(&self) -> Rational64 {
        self.hi - self.lo
    }

    /// Midpoint of the interval: `(lo + hi) / 2`.
    #[must_use]
    pub fn midpoint(&self) -> Rational64 {
        (self.lo + self.hi) / Rational64::from_integer(2)
    }

    /// Whether the interval contains zero.
    #[must_use]
    pub fn contains_zero(&self) -> bool {
        let zero = Rational64::from_integer(0);
        self.lo <= zero && zero <= self.hi
    }

    /// Whether both bounds are strictly positive.
    #[must_use]
    pub fn is_strictly_positive(&self) -> bool {
        self.lo > Rational64::from_integer(0)
    }

    /// Whether both bounds are strictly negative.
    #[must_use]
    pub fn is_strictly_negative(&self) -> bool {
        self.hi < Rational64::from_integer(0)
    }

    /// Whether both bounds are non-negative.
    #[must_use]
    pub fn is_nonnegative(&self) -> bool {
        self.lo >= Rational64::from_integer(0)
    }
}
