// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Softmax convex relaxation with provable O(range) tightness (C020).
//!
//! This module implements tight convex relaxations for the softmax function
//! used in transformer/attention verification. The key decomposition:
//!
//! ```text
//! softmax(x)_i = exp(x_i) / sum_j exp(x_j) = exp(x_i - LSE(x))
//! ```
//!
//! where `LSE(x) = log(sum_j exp(x_j))` is the log-sum-exp function.
//!
//! ## Architecture
//!
//! - [`lse`]: Log-sum-exp computation, properties (convexity, squeeze, gradient)
//! - [`convex_relaxation`]: Interval-arithmetic bounds on softmax over boxes,
//!   tangent-plane and secant linear bounds on LSE
//! - [`c020_spec`]: C020 theorem specification with proof status tracking
//!
//! ## Key Results
//!
//! - **C020a:** LSE is convex (Hessian = diag(softmax) - softmax*softmax^T is PSD)
//! - **C020b:** Interval-arithmetic softmax bounds are sound
//! - **C020c:** Bound gap is O(range) where range = max(u) - min(l)
//! - **C020d:** LSE squeeze: max(x) <= LSE(x) <= max(x) + ln(n)
//!
//! ## Relationship to Other Modules
//!
//! - `ibp_crown::attention`: Existing softmax bounds using interval arithmetic
//!   (this module extends that with tightness analysis and LSE decomposition)
//! - `ibp_crown::mccormick`: McCormick envelopes for bilinear terms in attention
//! - `ibp_crown::layernorm`: LayerNorm bounds (similar convex-function analysis)
//!
//! ## References
//!
//! - Boyd & Vandenberghe, "Convex Optimization" (2004), Section 3.1.5
//! - Shi et al., "Robustness Verification for Transformers" (ICLR 2020)
//! - Wei et al., "Certified Robustness of Transformers" (NeurIPS 2021)

pub mod c020_spec;
pub(crate) mod convex_relaxation;
pub(crate) mod lse;

#[cfg(test)]
mod tests_relaxation;

pub use c020_spec::{
    c020_theorem_entries, C020_LSE_CONVEXITY, C020_LSE_SQUEEZE, C020_O_RANGE_TIGHTNESS,
    C020_SOFTMAX_BOUND_SOUNDNESS,
};
pub(crate) use convex_relaxation::{
    softmax_convex_relaxation, tightness_ratio, verify_o_range_tightness,
    verify_relaxation_soundness, SoftmaxRelaxation,
};
pub(crate) use lse::{log_sum_exp, softmax, softmax_via_lse};
