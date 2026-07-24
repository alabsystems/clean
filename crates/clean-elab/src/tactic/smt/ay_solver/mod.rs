// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//! Unified SMT solver wrapper and factory.
//!
//! This module contains the `SmtSolver` enum that abstracts over different
//! Ay backend implementations based on the configured verify policy. Split
//! from `ay_types.rs` to separate solver driver logic from type/config
//! definitions. Part of #2518.

#[cfg(feature = "ay-smt")]
mod assertion;
#[cfg(feature = "ay-smt")]
mod factory;
#[cfg(feature = "ay-smt")]
mod prove;
#[cfg(feature = "ay-smt")]
mod registration;
#[cfg(all(test, feature = "ay-smt"))]
mod test_support;

#[cfg(feature = "ay-smt")]
use super::ay_solver_translation::{
    is_exists_hypothesis, is_literal_false_goal, register_exists_witness_bindings,
    sync_new_translator_declarations, translate_expr_with_sync,
};
#[cfg(feature = "ay-smt")]
pub(super) use super::ay_solver_types::{
    DirectAyKernelProof, ExistsWitnessBinding, SmtProveOutcome,
};
#[cfg(feature = "ay-smt")]
use super::ay_types::{
    supported_local_decl_kind, AyConfig, SmtVerifyPolicy, SupportedLocalDeclKind,
};
#[cfg(feature = "ay-smt")]
use super::reconstruction_gate::reconstruct_unsat_proof;
#[cfg(feature = "ay-smt")]
use crate::tactic::smt_translate::SmtLibTranslator;
#[cfg(feature = "ay-smt")]
use clean_auto::bridge::ay_contract::{
    AyBackend, AyError, AyLogic, AyProofBackend, AyProofResult, AyResult, ProofProfile,
    TrustBudget, VariableMapping,
};
#[cfg(feature = "ay-smt")]
use clean_kernel::{Expr, FVarId};

/// Unified SMT solver that wraps either AyBackend or AyProofBackend
///
/// This enum enables verify_policy branching by selecting the appropriate
/// backend based on the configured policy:
///
/// - `TrustSolver`: Uses `Fast(AyBackend)` — no proof verification
/// - Other policies: Uses `Verifiable` with `AyProofBackend` — proof extraction
///   and optional kernel reconstruction via the proof_reconstruct pipeline
#[cfg(feature = "ay-smt")]
pub(crate) enum SmtSolver {
    /// Fast path using AyBackend (no proofs)
    Fast(AyBackend),
    /// Proof-capable path using AyProofBackend with Expr→SMT-LIB translation.
    /// Enables proof extraction, Carcara verification, and kernel reconstruction.
    /// Part of #2427.
    Verifiable {
        backend: AyProofBackend,
        translator: SmtLibTranslator,
        var_map: VariableMapping,
        exists_bindings: Vec<ExistsWitnessBinding>,
        next_exists_placeholder_fvar: u64,
        #[cfg(test)]
        policy: SmtVerifyPolicy,
        reconstruction_budget: TrustBudget,
    },
    /// Disabled solver (fallback for configuration errors)
    #[cfg(test)]
    Disabled {
        policy: SmtVerifyPolicy,
        reason: String,
    },
}

#[cfg(feature = "ay-smt")]
pub(super) fn create_smt_backend(config: &AyConfig, logic: AyLogic) -> SmtSolver {
    factory::create_smt_backend(config, logic)
}
