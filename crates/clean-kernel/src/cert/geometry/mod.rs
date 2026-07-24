// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Geometry Certificate Generator
//!
//! This module generates ProofCert certificates from geometry derivation traces.
//! External geometry solvers (Newclid, AlphaGeometry, etc.) produce derivation
//! traces that this module translates into clean proof certificates.

mod cert_gen;
mod converter;

pub use cert_gen::{GeomStep, GeometryCertError, GeometryCertGenerator};
pub use converter::{ConversionError, GoalStep, ProblemSteps, ProblemToStepsConverter};

#[cfg(test)]
mod tests;
