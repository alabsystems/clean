// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Verified interval arithmetic library.
//!
//! Provides sound interval operations with formal containment proofs.
//! Used downstream by NN verification (CROWN bounds) and nonlinear
//! arithmetic reasoning.
//!
//! # Architecture
//!
//! - [`types`] — Core `Interval<T>` type, exact (`Rational64`) and fast (`f64`)
//! - [`ops`] — Arithmetic operations (add, sub, mul, div, sqrt, exp, ln)
//! - [`theorems`] — 20 formal containment theorems with runtime verification
//!
//! # Example
//!
//! ```
//! use num_rational::Rational64;
//! use clean_auto::interval::types::Interval;
//! use clean_auto::interval::ops;
//!
//! let x = Interval::from_integers(1, 3).expect("valid interval");
//! let y = Interval::from_integers(2, 5).expect("valid interval");
//! let sum = ops::add_rational(&x, &y);
//! assert_eq!(*sum.lower(), Rational64::from_integer(3));
//! assert_eq!(*sum.upper(), Rational64::from_integer(8));
//! ```

pub mod ops;
pub mod theorems;
pub mod theorems_monotone;
pub mod types;

#[cfg(test)]
mod tests;

// Re-export core types at module level for convenience.
pub use types::{F64Interval, Interval, IntervalError, RationalInterval};
