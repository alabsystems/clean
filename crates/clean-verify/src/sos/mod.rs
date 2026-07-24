// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! SageMath SDP bridge for sum-of-squares (SOS) polynomial certificates.
//!
//! Parses SOS certificate output from SageMath / DSOS / SDSOS solvers,
//! converts polynomial certificates into the existing NRA [`Polynomial`] and
//! [`SosCertificate`] types, and algebraically verifies that the SOS
//! decomposition equals the target polynomial.
//!
//! ## Certificate Format
//!
//! The parser accepts a text format:
//!
//! ```text
//! SOS_CERTIFICATE
//! VARIABLES: x y z
//! TARGET: x^4 + y^4 + z^4 - x^2*y^2 - y^2*z^2 - z^2*x^2
//! SQUARES: 3
//! Q1: (1/2)*x^2 - (1/2)*y^2
//! Q2: (1/2)*y^2 - (1/2)*z^2
//! Q3: (1/2)*x^2 - (1/2)*z^2
//! ```
//!
//! ## Architecture
//!
//! - [`parse`] — Certificate text format parser
//! - [`verify`] — Algebraic verification of SOS decompositions
//!
//! Reuses [`Polynomial`](crate::smt_verify::nra::Polynomial) and
//! [`Monomial`](crate::smt_verify::nra::Monomial) from the NRA checker.

pub(crate) mod parse;
pub(crate) mod verify;

#[cfg(test)]
mod tests;
