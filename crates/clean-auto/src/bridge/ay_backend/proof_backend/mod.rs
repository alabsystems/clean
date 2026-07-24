// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Ay proof backend: executor-based solving with Alethe proof extraction
//! and optional Carcara verification.

mod execution;
mod verification;

#[cfg(test)]
mod test_support;

use super::{AyBackendConfig, AyError, AyLogic};
use ay::executor::Executor;
use ay_core::quote_symbol;
use std::fmt;
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

    /// Carcara verification error
    #[cfg(feature = "carcara-verify")]
    #[error("carcara error: {0}")]
    CarcaraError(String),
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
            #[cfg(feature = "carcara-verify")]
            VerifyError::CarcaraError(message) => {
                Self::VerificationFailed(format!("Carcara verification error: {message}"))
            }
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

impl AyProofQuality {
    #[must_use]
    pub fn is_complete(&self) -> bool {
        self.trust_count == 0 && self.hole_count == 0
    }

    #[must_use]
    pub fn verified_count(&self) -> u32 {
        self.resolution_count + self.drup_count + self.th_resolution_count
    }

    #[must_use]
    pub fn axiom_count(&self) -> u32 {
        self.assume_count + self.theory_lemma_count
    }

    #[must_use]
    pub fn fallback_count(&self) -> u32 {
        self.trust_count + self.hole_count
    }
}

impl From<ay::ProofQuality> for AyProofQuality {
    fn from(value: ay::ProofQuality) -> Self {
        Self {
            assume_count: value.assume_count,
            resolution_count: value.resolution_count,
            theory_lemma_count: value.theory_lemma_count,
            trust_count: value.trust_count,
            trust_fallback_count: value.trust_fallback_count,
            hole_count: value.hole_count,
            drup_count: value.drup_count,
            th_resolution_count: value.th_resolution_count,
            other_rule_count: value.other_rule_count,
            total_steps: value.total_steps,
        }
    }
}

impl fmt::Display for AyProofQuality {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "steps={} verified={} axiom={} fallback={} (trust={} trust_fallback={} hole={}) \
             [assume={} resolution={} th_resolution={} theory_lemma={} drup={} other={}]",
            self.total_steps,
            self.verified_count(),
            self.axiom_count(),
            self.fallback_count(),
            self.trust_count,
            self.trust_fallback_count,
            self.hole_count,
            self.assume_count,
            self.resolution_count,
            self.th_resolution_count,
            self.theory_lemma_count,
            self.drup_count,
            self.other_rule_count,
        )
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
        /// The Alethe proof (if proof production was enabled)
        proof: Option<String>,
        /// Whether the proof was verified (tier 1+)
        verified: bool,
        /// Proof quality metrics from ay-proof native checker (if available)
        quality: Option<AyProofQuality>,
    },
    /// The solver could not determine satisfiability
    Unknown,
}

/// Ay backend with proof extraction support.
/// Uses ay's `Executor` for proof production (Alethe format).
pub struct AyProofBackend {
    pub(in crate::bridge::ay_backend) executor: Executor,
    pub(in crate::bridge::ay_backend) logic: AyLogic,
    pub(in crate::bridge::ay_backend) config: AyBackendConfig,
    pub(in crate::bridge::ay_backend) assertions: Vec<String>,
    pub(in crate::bridge::ay_backend) declarations: Vec<String>,
    pub(in crate::bridge::ay_backend) fresh_counter: u32,
    pub(in crate::bridge::ay_backend) last_problem: String,
}

impl AyProofBackend {
    /// Create a new proof-capable Ay backend with full configuration
    ///
    /// This is the preferred constructor. Use `AyBackendConfig::with_proofs(logic)`
    /// to enable proof production.
    ///
    /// Note: Executor does not yet support timeout - config.timeout_ms is ignored.
    /// For timeout support without proofs, use `AyBackend::with_config()` instead.
    pub fn with_config(config: AyBackendConfig) -> Self {
        let mut executor = Executor::new();
        let logic = config.logic();
        if config.produces_proofs() {
            executor.set_produce_proofs(true);
        }
        // Note: Executor API does not support timeout. File ay issue if needed.
        Self {
            executor,
            logic,
            config,
            assertions: Vec::new(),
            declarations: Vec::new(),
            fresh_counter: 0,
            last_problem: String::new(),
        }
    }

    /// Create a new proof-capable Ay backend with default config
    pub fn new_default(logic: AyLogic) -> Self {
        Self::with_config(AyBackendConfig::new(logic))
    }

    /// Create a new proof-capable Ay backend with proof production enabled
    pub fn new_with_proofs(logic: AyLogic) -> Self {
        Self::with_config(AyBackendConfig::with_proofs(logic))
    }

    /// Get the logic this backend is configured for
    pub fn logic(&self) -> AyLogic {
        self.logic
    }

    /// Get the configuration
    pub fn config(&self) -> &AyBackendConfig {
        &self.config
    }

    fn fresh_var(&mut self, name_hint: &str, sort: &str) -> String {
        let raw_name = format!("{}_{}", name_hint, self.fresh_counter);
        self.fresh_counter += 1;
        let quoted = quote_symbol(&raw_name);
        self.declarations
            .push(format!("(declare-const {} {})", quoted, sort));
        quoted
    }

    /// Declare a fresh integer variable and return its name
    ///
    /// The returned name is properly quoted for SMT-LIB use if the name_hint
    /// contains reserved words or special characters.
    pub fn fresh_int(&mut self, name_hint: &str) -> String {
        self.fresh_var(name_hint, "Int")
    }

    /// Declare a fresh boolean variable and return its name
    ///
    /// The returned name is properly quoted for SMT-LIB use if the name_hint
    /// contains reserved words or special characters.
    pub fn fresh_bool(&mut self, name_hint: &str) -> String {
        self.fresh_var(name_hint, "Bool")
    }

    /// Declare a fresh real variable and return its name
    ///
    /// The returned name is properly quoted for SMT-LIB use if the name_hint
    /// contains reserved words or special characters.
    pub fn fresh_real(&mut self, name_hint: &str) -> String {
        self.fresh_var(name_hint, "Real")
    }

    /// Assert a constraint (SMT-LIB formula string)
    pub fn assert_formula(&mut self, formula: &str) {
        self.assertions.push(format!("(assert {})", formula));
    }

    /// Add a raw SMT-LIB declaration (used by `SmtSolver::Verifiable` for translator decls).
    pub fn add_raw_declaration(&mut self, decl: &str) {
        self.declarations.push(decl.to_string());
    }

    /// Reset the backend for a new problem
    pub fn reset(&mut self) {
        self.assertions.clear();
        self.declarations.clear();
        self.fresh_counter = 0;
        self.last_problem.clear();
        self.executor = Executor::new();
        if self.config.produces_proofs() {
            self.executor.set_produce_proofs(true);
        }
    }

    /// Push a new scope for incremental solving
    pub fn push(&mut self) {
        self.assertions.push("(push 1)".to_string());
    }

    /// Pop the most recent scope
    pub fn pop(&mut self) {
        self.assertions.push("(pop 1)".to_string());
    }

    /// Check whether the configured proof profile accepts the current logic.
    ///
    /// Returns `Ok(())` if no profile is set, the profile's tier is below 1,
    /// or the theory is accepted. Returns `Err(TheoryRejected)` otherwise.
    ///
    /// Used by both `execution::check_sat` and `verification::verify_proof_if_required`
    /// to enforce the theory gate consistently.
    fn ensure_profile_accepts_current_logic(&self) -> super::AyResult<()> {
        if let Some(profile) = self.config.profile() {
            if profile.verification_tier() >= 1 {
                let logic_str = self.logic.to_string();
                if !profile.accepts_theory(&logic_str) {
                    return Err(AyError::TheoryRejected(format!(
                        "theory {} not accepted by proof profile",
                        logic_str
                    )));
                }
            }
        }
        Ok(())
    }
}
