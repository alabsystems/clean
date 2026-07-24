// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Polynomial zonotope attention verification (C015).
//!
//! Polynomial zonotopes extend standard (linear) zonotopes with quadratic
//! generators that track `eps_i * eps_j` cross-terms through nonlinear
//! operations. For attention layers in Vision Transformers, this provides
//! O(eps) tightness instead of the O(eps^2) gap from linear relaxations.
//!
//! ## Architecture
//!
//! - [`types`]: `PolyZonotope` type with arithmetic (add, scale, linear
//!   transform, Hadamard product)
//! - [`attention`]: Attention bound computation using polynomial zonotope
//!   arithmetic, with comparison to linear zonotope baseline
//! - [`tightness`]: Empirical tightness analysis confirming O(eps) scaling
//! - [`c015_spec`]: C015 theorem specification with proof status tracking
//!
//! ## Key Results
//!
//! - **C015a:** Polynomial zonotope product is sound (contains true product)
//! - **C015b:** Attention bounds (q*k*v) are sound
//! - **C015c:** Polynomial zonotope gap is O(eps) (linear in perturbation)
//! - **C015d:** Linear zonotope gap is O(eps^2) (quadratic in perturbation)
//! - **C015e:** Polynomial zonotope always at least as tight as linear
//!
//! ## Relationship to Other Modules
//!
//! - `zonotope`: Standard (linear) zonotope implementation (T01-T08)
//! - `softmax`: Softmax convex relaxation (C020) — complementary approach
//!   for the softmax component of attention
//! - `ibp_crown`: IBP/CROWN bounds — linear relaxation baseline
//!
//! ## References
//!
//! - Kochdumper & Althoff, "Sparse Polynomial Zonotopes" (2020)
//! - Bonaert et al., "Fast and Precise Certification of Transformers" (PLDI 2021)
//! - Shi et al., "Robustness Verification for Transformers" (ICLR 2020)

pub mod attention;
pub mod c015_spec;
pub(crate) mod tightness;
pub mod types;

#[cfg(test)]
mod tests_integration;

pub use attention::{
    attention_bound_linear, attention_bound_poly, compare_attention_bounds,
    verify_attention_soundness, AttentionBound,
};
pub use c015_spec::{
    c015_theorem_entries, C015_ATTENTION_BOUND_SOUND, C015_LINEAR_O_EPS_SQUARED,
    C015_POLY_DOMINATES_LINEAR, C015_POLY_O_EPS_TIGHTNESS, C015_POLY_PRODUCT_SOUND,
};
pub use tightness::{analyze_tightness, verify_o_eps_tightness, TightnessAnalysis};
pub use types::{PolyZonotope, PolyZonotopeError};
