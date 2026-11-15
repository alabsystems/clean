// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! wasm32 stand-in for `proof_reconstruct/`.
//!
//! The native reconstruction pipeline consumes `ay_core::Proof` and cannot
//! compile on wasm32. `reconstruction_quality.rs` (reused verbatim on wasm)
//! only needs the shape of [`ReconstructionResult`], so that shape is
//! mirrored here field-for-field from `proof_reconstruct/types.rs`.

use super::reconstruction_quality::ResidualTrustSummary;
use clean_kernel::{Expr, FVarId};

// `types.rs` is ay-free (kernel exprs + hashbrown only); reused verbatim for
// the `VariableMapping` the cross-crate contract exports.
#[path = "proof_reconstruct/types.rs"]
mod types;
pub use types::VariableMapping;

/// Result of attempting proof reconstruction. Never constructed on wasm32 —
/// the solver entry points that would produce one are native-only.
#[derive(Debug)]
pub(crate) struct ReconstructionResult {
    /// The reconstructed kernel proof term, if successful.
    pub proof_term: Option<Expr>,
    /// FVarId of the negated-goal assumption proof, if one was introduced.
    pub negated_goal_fvar: Option<FVarId>,
    /// FVarIds of compound witness assumptions unbound in the proof term.
    pub compound_witness_fvars: Vec<(FVarId, Expr)>,
    /// Whether the selected reconstruction root derives the empty clause.
    pub derives_empty_clause: bool,
    /// Number of `trustedAy` sub-terms the reconstruction reported.
    pub trust_subterm_count: usize,
    /// Residual trust accounting carried by the candidate.
    pub residual: ResidualTrustSummary,
}
