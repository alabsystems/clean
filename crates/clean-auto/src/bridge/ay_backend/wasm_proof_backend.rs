// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! wasm32 mirror of the pure-data pieces of `proof_backend/`.
//!
//! The native `proof_backend` owns an `ay::executor::Executor` and cannot
//! compile without the ay crates, which have no wasm32 port. The result /
//! quality / error types carry no solver state and are kept
//! variant-for-variant identical to `proof_backend/mod.rs`; the
//! `AyProofBackend` stub keeps the SMT-LIB bookkeeping surface (assertions,
//! declarations, fresh variables) compiling while every solve or
//! reconstruction entry point reports the solver as unavailable instead of
//! running one.

use super::proof_reconstruct::VariableMapping;
use super::reconstruction_quality::{KernelReconstructionCandidate, TrustBudget};
use super::surface::{AyError, AyLogic, AyResult};
use super::{AyBackendConfig, AyUnknownReason};
use std::num::NonZeroU64;
use std::time::Duration;
use thiserror::Error;

/// Errors from proof verification
#[derive(Debug, Error)]
#[non_exhaustive]
pub enum VerifyError {
    /// Proof verification failed
    #[error("proof verification failed: {0}")]
    VerificationFailed(String),

    /// Proof format not supported
    #[error("proof format not supported: {0}")]
    UnsupportedFormat(String),

    /// Theory not accepted by profile
    #[error("theory not accepted: {0}")]
    TheoryRejected(String),

    /// Carcara feature not enabled
    #[error("carcara-verify feature required for tier 1 verification")]
    CarcaraNotEnabled,
}

impl From<VerifyError> for AyError {
    fn from(error: VerifyError) -> Self {
        match error {
            VerifyError::VerificationFailed(message) => Self::VerificationFailed(message),
            VerifyError::UnsupportedFormat(message) => {
                Self::VerificationFailed(format!("unsupported proof format: {message}"))
            }
            VerifyError::TheoryRejected(message) => Self::TheoryRejected(message),
            VerifyError::CarcaraNotEnabled => Self::VerificationFailed(
                "proof verification required but no checker available".to_string(),
            ),
        }
    }
}

/// clean-owned proof quality diagnostics on the curated `AyProofResult` surface.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
#[non_exhaustive]
pub struct AyProofQuality {
    pub assume_count: u32,
    pub resolution_count: u32,
    pub theory_lemma_count: u32,
    pub trust_count: u32,
    pub trust_fallback_count: u32,
    pub hole_count: u32,
    pub drup_count: u32,
    pub th_resolution_count: u32,
    pub other_rule_count: u32,
    pub total_steps: u32,
}

// Visibility note: only the entry points a crate OUTSIDE clean-auto calls on
// the wasm surface are bare `pub` (the type definitions must also stay `pub`
// for `ay_contract`'s wasm re-export list — E0364 refuses a pub(crate) item
// there). Everything else is pub(crate) even where the native twin is `pub`:
// stub internals carry no wider visibility than their callers require.
impl AyProofQuality {
    #[must_use]
    pub(crate) fn is_complete(&self) -> bool {
        self.trust_count == 0 && self.hole_count == 0
    }

    #[must_use]
    pub(crate) fn verified_count(&self) -> u32 {
        self.resolution_count + self.drup_count + self.th_resolution_count
    }

    #[must_use]
    pub(crate) fn axiom_count(&self) -> u32 {
        self.assume_count + self.theory_lemma_count
    }

    #[must_use]
    pub(crate) fn fallback_count(&self) -> u32 {
        self.trust_count + self.hole_count
    }
}

/// Result of a satisfiability check with optional proof
#[must_use = "solver results should be inspected before being dropped"]
#[derive(Debug, Clone)]
#[non_exhaustive]
pub enum AyProofResult {
    /// The constraints are satisfiable
    Sat,
    /// The constraints are unsatisfiable, with optional Alethe proof
    Unsat {
        /// The Alethe proof, when one was rendered.
        proof: Option<String>,
        /// Whether the proof was verified (tier 1+)
        verified: bool,
        /// Proof quality metrics from ay-proof native checker (if available)
        quality: Option<AyProofQuality>,
    },
    /// The solver could not determine satisfiability, for the reason ay gave.
    Unknown {
        /// Why the solve ended undecided, as ay reported it.
        reason: AyUnknownReason,
        /// ay's sentence beside the reason, when it recorded one.
        detail: Option<String>,
    },
}

/// Message every wasm solve entry point reports: the ay solver stack is
/// native-only.
fn solver_unavailable() -> AyError {
    AyError::SolverDisabled("SMT automation is native-only (no wasm32 ay solver)".to_string())
}

/// Proof-capable backend stub: keeps the SMT-LIB bookkeeping surface
/// compiling on wasm32 while every solve entry point refuses.
pub struct AyProofBackend {
    logic: AyLogic,
    config: AyBackendConfig,
    assertions: Vec<String>,
    declarations: Vec<String>,
    fresh_counter: u32,
}

impl AyProofBackend {
    /// Create a new proof-capable backend stub from full configuration.
    pub fn with_config(config: AyBackendConfig) -> Self {
        let logic = config.logic();
        Self {
            logic,
            config,
            assertions: Vec::new(),
            declarations: Vec::new(),
            fresh_counter: 0,
        }
    }

    /// Create a new proof-capable backend stub with default config.
    pub(crate) fn new_default(logic: AyLogic) -> Self {
        Self::with_config(AyBackendConfig::new(logic))
    }

    /// Create a new proof-capable backend stub with proof production enabled.
    pub(crate) fn new_with_proofs(logic: AyLogic) -> Self {
        Self::with_config(AyBackendConfig::with_proofs(logic))
    }

    /// Get the logic this backend is configured for
    pub(crate) fn logic(&self) -> AyLogic {
        self.logic
    }

    /// Get the configuration
    pub(crate) fn config(&self) -> &AyBackendConfig {
        &self.config
    }

    fn fresh_var(&mut self, name_hint: &str, sort: &str) -> String {
        let name = format!("{}_{}", name_hint, self.fresh_counter);
        self.fresh_counter += 1;
        self.declarations
            .push(format!("(declare-const {name} {sort})"));
        name
    }

    /// Declare a fresh integer variable and return its name
    pub(crate) fn fresh_int(&mut self, name_hint: &str) -> String {
        self.fresh_var(name_hint, "Int")
    }

    /// Declare a fresh boolean variable and return its name
    pub(crate) fn fresh_bool(&mut self, name_hint: &str) -> String {
        self.fresh_var(name_hint, "Bool")
    }

    /// Declare a fresh real variable and return its name
    pub(crate) fn fresh_real(&mut self, name_hint: &str) -> String {
        self.fresh_var(name_hint, "Real")
    }

    /// Record an SMT-LIB assertion
    pub fn assert_formula(&mut self, formula: &str) {
        self.assertions.push(format!("(assert {formula})"));
    }

    /// Record a raw SMT-LIB declaration
    pub fn add_raw_declaration(&mut self, decl: &str) {
        self.declarations.push(decl.to_string());
    }

    /// Clear recorded assertions and declarations
    pub(crate) fn reset(&mut self) {
        self.assertions.clear();
        self.declarations.clear();
        self.fresh_counter = 0;
    }

    /// Check satisfiability: always refuses — the solver is native-only.
    pub fn check_sat(&mut self) -> AyResult<AyProofResult> {
        Err(solver_unavailable())
    }

    /// Check satisfiability within an effort: always refuses — the solver is
    /// native-only.
    pub(crate) fn check_sat_with_effort(
        &mut self,
        _effort: NonZeroU64,
        _backstop: Duration,
    ) -> AyResult<AyProofResult> {
        Err(solver_unavailable())
    }

    /// Kernel proof reconstruction: no proof can exist on wasm32.
    pub(crate) fn attempt_kernel_reconstruction(
        &self,
        _var_map: &VariableMapping,
        _negated_goal: &clean_kernel::Expr,
    ) -> Option<KernelReconstructionCandidate> {
        None
    }

    /// Kernel proof reconstruction under a trust budget: no proof can exist
    /// on wasm32.
    pub fn attempt_kernel_reconstruction_with_budget(
        &self,
        _var_map: &VariableMapping,
        _negated_goal: &clean_kernel::Expr,
        _budget: TrustBudget,
    ) -> Option<KernelReconstructionCandidate> {
        None
    }
}

/// Alethe proof verification: no checker is linked on wasm32.
pub fn verify_alethe_proof(_problem: &str, _proof: &str) -> Result<bool, VerifyError> {
    Err(VerifyError::CarcaraNotEnabled)
}
