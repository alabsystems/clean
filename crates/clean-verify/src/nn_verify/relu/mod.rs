// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! ReLU stability analysis for neural network verification (C012).
//!
//! This module provides concrete computational analysis of ReLU neuron
//! stability. A neuron is "stable" when its pre-activation bounds do not
//! cross zero -- meaning the ReLU can be replaced by a linear function
//! (identity for always-active, zero for always-inactive), enabling exact
//! verification without relaxation.
//!
//! ## Architecture
//!
//! - [`stability`]: Core stability analysis (classification, counting, gap
//!   computation)
//! - [`c012_spec`]: C012 theorem specification with proof status tracking
//!
//! ## Relationship to Other Modules
//!
//! - `zonotope::relu`: Lambda-relaxation overapproximation for crossing neurons
//! - `ibp_crown::ibp`: IBP ReLU case-split (T81) uses the same always-active /
//!   always-inactive / crossing classification
//! - `clean-kernel::nn_verify_relu_stability`: Kernel-level C012 theorems
//!   (pattern_stable_criterion, crown_exact_under_stable, lp_reduction)
//!
//! ## References
//!
//! - Wong & Kolter, "Provable Defenses" (NeurIPS 2018)
//! - Xu et al., "Auto-LiRPA" (NeurIPS 2020)

pub mod c012_spec;
pub mod stability;

#[cfg(test)]
mod tests_stability;

pub use c012_spec::{
    c012_theorem_entries, C012_CROWN_EXACT_UNDER_STABLE, C012_LP_REDUCTION,
    C012_PATTERN_STABLE_CRITERION,
};
pub use stability::{
    analyze_layer_stability, analyze_network_stability, relaxation_gap_ratio,
    NetworkStabilityReport, NeuronStability, StabilityAnalyzer,
};
