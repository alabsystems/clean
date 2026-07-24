// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Verified interval arithmetic library for clean-verify.
//!
//! Provides sound interval operations over exact rational arithmetic
//! (`Rational64`) with 20 formal soundness theorems tracked via
//! [`ProofStatus`](crate::spec::ProofStatus).
//!
//! # Architecture
//!
//! - [`types`] -- Core `Interval` type over `Rational64`, error types
//! - [`ops`] -- 13 arithmetic operations (add, sub, mul, div, neg, abs,
//!   pow, sqrt, contains, width, midpoint, intersect, hull)
//! - [`theorems`] -- 20 soundness theorems with runtime witness verification
//!
//! # Theorem Coverage
//!
//! | ID    | Property                          | Status        |
//! |-------|-----------------------------------|---------------|
//! | T01   | Addition containment              | DerivedPending |
//! | T02   | Subtraction containment           | DerivedPending |
//! | T03   | Negation containment              | DerivedPending |
//! | T04   | Multiplication containment        | DerivedPending |
//! | T05   | Division containment              | DerivedPending |
//! | T06   | Absolute value containment        | DerivedPending |
//! | T07   | Power containment (non-negative)  | DerivedPending |
//! | T08   | Sqrt containment                  | DerivedPending |
//! | T09   | Intersection containment          | DerivedPending |
//! | T10   | Hull containment                  | DerivedPending |
//! | T11   | Subset transitivity               | DerivedPending |
//! | T12   | Containment transitivity          | DerivedPending |
//! | T13   | Point interval identity           | DerivedPending |
//! | T14   | Contains reflexive                | DerivedPending |
//! | T15   | Width of addition                 | DerivedPending |
//! | T16   | Width of subtraction              | DerivedPending |
//! | T17   | Width of negation                 | DerivedPending |
//! | T18   | Addition commutativity            | DerivedPending |
//! | T19   | Multiplication commutativity      | DerivedPending |
//! | T20   | Addition associativity            | DerivedPending |

pub mod ops;
pub(crate) mod spec_registration;
pub mod theorems;
pub mod theorems_algebraic;
pub mod theorems_promote;
pub mod types;

#[cfg(test)]
mod tests;
#[cfg(test)]
mod tests_promote;
#[cfg(test)]
mod tests_proptest;

pub use theorems::TheoremWitness;
pub use theorems_promote::{spec_name_for, DynamicStatusError};
// Gated re-export — `compute_proof_statuses_dynamically` calls into
// `Specification::new_interval_arith_test_spec`, which itself is only
// compiled under `test-utils`. See #3477.
#[cfg(any(test, feature = "test-utils"))]
pub use theorems_promote::compute_proof_statuses_dynamically;
pub use types::{Interval, IntervalError};
