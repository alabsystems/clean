// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Neural Network Verification Proof Engine
//!
//! Formalizes soundness proofs for neural network verification techniques
//! used in gamma-crown. This module provides proof strategies and status
//! tracking for IBP (Interval Bound Propagation), CROWN (backward mode
//! linear relaxation), and related methods.
//!
//! ## Architecture
//!
//! The proof engine is organized by verification technique:
//!
//! - [`ibp_crown`]: IBP forward bounds, Lipschitz analysis, and CROWN
//!   backward bounds. Phase 1 covers IBP linear/ReLU/composition and
//!   Lipschitz submultiplicativity. Phase 3 covers CROWN, LayerNorm,
//!   and McCormick relaxations.
//!
//! ## Relationship to `neural_surgery`
//!
//! The `neural_surgery` module formalizes *weight edit* properties (rank-1
//! update algebra, bound degradation under perturbation). This module
//! formalizes the *verification methods themselves* -- proving that IBP,
//! CROWN, etc. compute sound bounds on network outputs.
//!
//! ## Cross-References
//!
//! - gamma-crown: production NN verifier that implements these techniques
//! - `neural_surgery::bound_propagation`: Lipschitz-based bound propagation
//!   under weight edits (complementary to IBP/CROWN soundness here)
//! - TorchLean (arXiv:2602.22631): Lean 4 formalization of NN models

pub mod bab_branching;
pub mod base;
pub mod cert_expr_builder;
pub mod cert_json_parser;
pub mod certificate;
pub(crate) mod e2e_json_parser;
#[cfg(test)]
mod e2e_tests;
pub(crate) mod e2e_verifier;
pub mod eclipse;
pub mod ibp_crown;
pub mod nullstellensatz;
pub mod orbit_crown;
pub mod pac_proof;
pub mod pipeline;
#[cfg(test)]
mod pipeline_tests;
pub mod poly_zonotope;
pub mod relu;
pub mod softmax;
pub mod streaming;
pub mod zonotope;
