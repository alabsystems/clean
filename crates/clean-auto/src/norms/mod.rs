// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Concrete L1/L2/Linf norm instances for vectors and matrices.
//!
//! Provides types, computation, and verified properties (triangle inequality,
//! submultiplicativity, norm equivalence bounds) for use in NN verification
//! proofs.
//!
//! # Modules
//!
//! - [`types`] — `NormKind`, `Vector<T>`, `Matrix<T>`
//! - [`compute`] — Norm evaluation (f64 and exact rational)
//! - [`theorems`] — Runtime property witnesses

pub mod compute;
pub mod theorems;
pub mod types;

#[cfg(test)]
mod tests;
