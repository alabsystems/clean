// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `AyBackendConfig` builder surface.
//!
//! Moved from `mod.rs` as part of the root surface split (#2867).
//! Re-exported from the parent module for import stability.

use super::proof_format::ProofProfile;
use super::surface::AyLogic;
use super::triggers::TriggerPolicy;

/// Configuration options for Ay backend
///
/// Unified configuration struct following gamma-crown's `SmtVerifierConfig` pattern.
/// Use `AyBackendConfig::new(logic)` for defaults, or `AyBackend::with_config()`
/// for full configuration.
#[derive(Debug, Clone)]
#[must_use]
pub struct AyBackendConfig {
    /// Logic to use (required)
    logic: AyLogic,
    /// Timeout in milliseconds (None = no timeout)
    timeout_ms: Option<u64>,
    /// Whether to produce proofs on UNSAT results
    produce_proofs: bool,
    /// Verbose output (print SMT-LIB2 and result)
    verbose: bool,
    /// Proof profile for verified UNSAT acceptance
    proof_profile: Option<ProofProfile>,
    /// Policy for quantifier trigger selection
    ///
    /// Controls how user-provided triggers interact with solver-inferred triggers.
    /// Default: `TriggerPolicy::Auto` (solver chooses triggers automatically).
    trigger_policy: TriggerPolicy,
}

impl AyBackendConfig {
    /// Create a configuration with the specified logic and default options
    pub fn new(logic: AyLogic) -> Self {
        Self {
            logic,
            timeout_ms: None,
            produce_proofs: false,
            verbose: false,
            proof_profile: None,
            trigger_policy: TriggerPolicy::default(),
        }
    }

    /// Create a configuration with proof production enabled
    pub fn with_proofs(logic: AyLogic) -> Self {
        Self::new(logic).enable_proofs()
    }

    /// Set timeout in milliseconds
    pub fn timeout(mut self, ms: u64) -> Self {
        self.timeout_ms = Some(ms);
        self
    }

    /// Enable verbose output
    pub fn verbose(mut self) -> Self {
        self.verbose = true;
        self
    }

    /// Enable proof production while preserving the rest of the config.
    pub fn enable_proofs(mut self) -> Self {
        self.produce_proofs = true;
        self
    }

    /// Set proof profile for verified UNSAT acceptance
    ///
    /// When a proof profile is set with verification_tier >= 1,
    /// UNSAT results will be verified before being accepted.
    pub fn proof_profile(mut self, profile: ProofProfile) -> Self {
        // Automatically enable proof production if verification is requested
        if profile.verification_tier() >= 1 {
            self = self.enable_proofs();
        }
        self.proof_profile = Some(profile);
        self
    }

    /// Set the trigger policy for quantifier instantiation
    ///
    /// Controls how user-provided triggers interact with solver-inferred triggers.
    /// See [`TriggerPolicy`] for available options.
    pub fn trigger_policy(mut self, policy: TriggerPolicy) -> Self {
        self.trigger_policy = policy;
        self
    }

    /// Read-only accessors for the builder-backed config surface.
    pub fn logic(&self) -> AyLogic {
        self.logic
    }
    pub fn timeout_ms(&self) -> Option<u64> {
        self.timeout_ms
    }
    pub fn produces_proofs(&self) -> bool {
        self.produce_proofs
    }
    pub fn is_verbose(&self) -> bool {
        self.verbose
    }
    pub fn profile(&self) -> Option<&ProofProfile> {
        self.proof_profile.as_ref()
    }
    pub fn trigger_policy_value(&self) -> TriggerPolicy {
        self.trigger_policy
    }
}
