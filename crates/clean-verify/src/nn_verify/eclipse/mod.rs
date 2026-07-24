// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! ECLipsE iterative refinement proofs and executable witnesses (C003).
//!
//! Proves convergence of the ECLipsE iterative bound refinement algorithm
//! via Lipschitz contraction (Banach fixed-point theorem).

pub(crate) mod c003_spec;
pub(crate) mod convergence;
#[cfg(test)]
mod tests_convergence;
