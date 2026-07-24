// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Bootstrap trust chain verification status tracking.
//!
//! Tracks which parts of the bootstrap trust chain have been verified:
//! Lean 4 proofs of the kernel model, self-verification by clean, and
//! the transitive trust implications.
//!
//! ## Trust Chain Structure
//!
//! ```text
//! Lean 4 metatheory (trusted)
//!   └─> Lean 4 proves: clean kernel model is sound
//!         └─> Cross-validation: model matches implementation
//!               └─> clean self-checks: kernel matches model
//!                     └─> Transitive trust: clean kernel is sound
//! ```

/// Trust level of the bootstrap verification.
///
/// Each level strictly subsumes the previous: a `FullyVerified` kernel
/// has passed all lower verification stages.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[non_exhaustive]
pub enum BootstrapTrustLevel {
    /// No verification has been performed.
    Unverified,
    /// Lean 4 has proved soundness of the kernel model.
    Lean4Proved,
    /// clean has self-verified against the kernel model.
    SelfVerified,
    /// Both Lean 4 external proof and clean self-verification are complete.
    FullyVerified,
}

/// Overall status of the trust chain.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum TrustChainStatus {
    /// No theorems have been verified.
    Unverified,
    /// Some but not all theorems are verified.
    Partial,
    /// All required theorems have been verified.
    Complete,
}

/// A report of the current trust chain verification state.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TrustChainReport {
    /// Overall trust chain status.
    pub status: TrustChainStatus,
    /// Theorems that have been proved in Lean 4.
    pub lean4_proved_theorems: Vec<String>,
    /// Theorems that have been self-verified by clean.
    pub self_verified_theorems: Vec<String>,
}

/// Verifier for the bootstrap trust chain.
///
/// Inspects the current state of Lean 4 proofs and self-verification
/// results to produce a [`TrustChainReport`].
#[derive(Debug, Clone)]
pub struct TrustChainVerifier {
    /// Theorems registered as proved by Lean 4 (manually curated).
    lean4_proved: Vec<String>,
    /// Theorems registered as self-verified by clean.
    self_verified: Vec<String>,
}

impl TrustChainVerifier {
    /// Create a new trust chain verifier with no verified theorems.
    #[must_use]
    pub fn new() -> Self {
        Self {
            lean4_proved: Vec::new(),
            self_verified: Vec::new(),
        }
    }

    /// Register a theorem as proved in Lean 4.
    pub fn add_lean4_proof(&mut self, theorem_name: &str) {
        self.lean4_proved.push(theorem_name.to_string());
    }

    /// Register a theorem as self-verified by clean.
    pub fn add_self_verification(&mut self, theorem_name: &str) {
        self.self_verified.push(theorem_name.to_string());
    }

    /// Produce a trust chain report for the current verification state.
    #[must_use]
    pub fn verify_trust_chain(&self) -> TrustChainReport {
        let status = if self.lean4_proved.is_empty() && self.self_verified.is_empty() {
            TrustChainStatus::Unverified
        } else if self.has_all_required_lean4_proofs() && self.has_all_required_self_verifications()
        {
            TrustChainStatus::Complete
        } else {
            TrustChainStatus::Partial
        };

        TrustChainReport {
            status,
            lean4_proved_theorems: self.lean4_proved.clone(),
            self_verified_theorems: self.self_verified.clone(),
        }
    }

    /// Check if all required Lean 4 proofs are present.
    ///
    /// The required theorems are: type preservation, progress, confluence.
    fn has_all_required_lean4_proofs(&self) -> bool {
        const REQUIRED: &[&str] = &["type_preservation", "progress", "confluence"];
        REQUIRED
            .iter()
            .all(|name| self.lean4_proved.iter().any(|p| p == name))
    }

    /// Check if all required self-verifications are present.
    fn has_all_required_self_verifications(&self) -> bool {
        const REQUIRED: &[&str] = &["model_fidelity", "cross_validation"];
        REQUIRED
            .iter()
            .all(|name| self.self_verified.iter().any(|p| p == name))
    }
}

impl Default for TrustChainVerifier {
    fn default() -> Self {
        Self::new()
    }
}
