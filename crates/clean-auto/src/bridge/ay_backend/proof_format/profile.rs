// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Runtime UNSAT-acceptance policy for SMT proof verification.
//!
//! Defines `ProofProfile` for configuring verification tiers and accepted theories.

use std::collections::HashSet;

use super::format::{proof_formats, ProofFormat};

/// SMT Proof Profile for verified UNSAT acceptance
///
/// Defines verification requirements for ay UNSAT results.
/// Part of #608: Define SMT proof profile for ay UNSAT proofs.
///
/// # Verification Tiers
///
/// | Tier | Method | Trust | Performance |
/// |------|--------|-------|-------------|
/// | 0 | No proof | Trusts ay | Fastest |
/// | 1 | Carcara check | Trusts Carcara | ~10x overhead |
/// | 2 | LRAT kernel check | Minimal TCB | ~100x overhead |
/// | 3 | Kernel reconstruction | Self-verified | ~10x vs standalone checkers; depends on proof granularity |
///
/// # ay Solver Configuration (Part of #616)
///
/// When using `AyProofBackend` with a proof profile:
///
/// ```no_run
/// use clean_auto::bridge::ay_contract::{AyBackendConfig, AyLogic, AyProofBackend, ProofProfile};
///
/// // Production: Carcara-verified Alethe proofs
/// let config = AyBackendConfig::new(AyLogic::QfLia)
///     .proof_profile(ProofProfile::kernel_accepted());
///
/// let _backend = AyProofBackend::with_config(config);
/// // Setting proof_profile with tier >= 1 automatically enables produce_proofs
/// ```
///
/// ## Required ay Flags by Tier
///
/// | Tier | `produce_proofs` | Verification | Trust Level |
/// |------|-----------------|--------------|-------------|
/// | 0 | false | None | Trusts ay |
/// | 1 | true (auto) | Carcara | Trusts Carcara |
/// | 2 | true (auto) | LRAT kernel | Minimal TCB |
/// | 3 | true (auto) | Kernel terms | Self-verified |
///
/// The `proof_profile()` method on `AyBackendConfig` automatically enables
/// `produce_proofs` when `verification_tier >= 1`.
///
/// See `designs/2026-03-01-smt-proof-verification-pipeline.md` for full specification.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
#[must_use]
pub struct ProofProfile {
    /// Proof format to produce (Alethe, LRAT, None)
    format: ProofFormat,
    /// Verification tier (0-3)
    ///
    /// - Tier 0: No verification (trust ay)
    /// - Tier 1: Native ay-proof verification (Carcara as fallback with `carcara-verify` feature)
    /// - Tier 2: LRAT kernel verification (not yet implemented)
    /// - Tier 3: Full kernel reconstruction (not yet implemented)
    verification_tier: u8,
    /// Accepted theories (whitelist)
    ///
    /// Only UNSAT results from these theories are accepted.
    /// Empty means all theories are accepted.
    accepted_theories: HashSet<String>,
}

impl ProofProfile {
    /// Get the configured proof format for this profile.
    #[cfg(test)]
    pub(crate) fn format(&self) -> &ProofFormat {
        &self.format
    }

    /// Get the verification tier for this profile.
    pub fn verification_tier(&self) -> u8 {
        self.verification_tier
    }

    /// Report whether this profile accepts every theory.
    pub fn accepts_all_theories(&self) -> bool {
        self.accepted_theories.is_empty()
    }

    /// Create a tier 0 profile (no verification, trusts ay)
    pub fn trusted() -> Self {
        Self::default()
    }

    /// Create a tier 1 profile (Carcara verification)
    ///
    /// Requires the `carcara-verify` feature to be enabled.
    pub fn carcara_verified() -> Self {
        Self {
            format: ProofFormat::alethe(),
            verification_tier: 1,
            accepted_theories: HashSet::new(),
        }
    }

    /// Create a tier 1 profile for specific theories
    pub fn carcara_verified_with_theories(theories: &[&str]) -> Self {
        Self {
            format: ProofFormat::alethe(),
            verification_tier: 1,
            accepted_theories: theories.iter().map(|s| s.to_string()).collect(),
        }
    }

    /// Check if a theory is accepted by this profile
    pub fn accepts_theory(&self, theory: &str) -> bool {
        self.accepted_theories.is_empty() || self.accepted_theories.contains(theory)
    }

    // =========================================================================
    // Kernel Acceptance Policy (Part of #617)
    // =========================================================================
    //
    // This section documents the acceptance policy for theory vs SAT-only proofs.
    // See `designs/2026-03-01-smt-proof-verification-pipeline.md` for the full design.
    //
    // ## Theory vs SAT-Only Proofs
    //
    // | Proof Type | Theories | Kernel Acceptance | Rationale |
    // |------------|----------|-------------------|-----------|
    // | SAT-only | Pure propositional | LRAT (Tier 2) | Verified checkers exist |
    // | Theory | QF_LIA, QF_LRA, QF_UF | Carcara (Tier 1) | Full Alethe support |
    // | Theory | QF_BV | Trusted (Tier 0) | No generic bitblast rule |
    // | Theory | Arrays | Trusted (Tier 0) | No standard Alethe rule |
    //
    // ## Policy Decision (per #617)
    //
    // **For Phase 4 self-verification:**
    // - Critical proofs: Require bit-blast to SAT + LRAT (Tier 2)
    // - Production proofs: Accept Carcara-verified Alethe (Tier 1) for QF_LIA/LRA/UF
    // - Development/testing: Accept unverified ay results (Tier 0)
    //
    // **BV and Arrays Policy:**
    // - Bitvector proofs using `trust` rule are accepted at Tier 0 only
    // - For verified BV, use bit-blasting to SAT + LRAT verification
    // - Array proofs are trusted (no Alethe rule exists)
    //
    // ## Usage Recommendations
    //
    // ```rust
    // // Development: Fast, trusts ay
    // let dev_profile = ProofProfile::trusted();
    //
    // // Production: Carcara-verified, excludes untrusted theories
    // let prod_profile = ProofProfile::kernel_accepted();
    //
    // // Critical: Only verified SAT proofs, strictest trust
    // let critical_profile = ProofProfile::kernel_critical();
    // ```

    /// Create a production profile with kernel-accepted theories only
    ///
    /// Accepts only theories with full Alethe proof support that Carcara
    /// can verify: QF_LIA, QF_LRA, QF_UF, QF_UFLIA, QF_UFLRA.
    ///
    /// **Excludes:** QF_BV (uses `trust` rule), QF_AUFLIA (no standard rule)
    ///
    /// Part of #617: Kernel acceptance policy for theory vs SAT-only proofs.
    pub fn kernel_accepted() -> Self {
        Self {
            format: ProofFormat::alethe(),
            verification_tier: 1,
            accepted_theories: proof_formats::CARCARA_VERIFIED_THEORIES
                .iter()
                .map(|s| s.to_string())
                .collect(),
        }
    }

    /// Create a critical profile for Phase 4 self-verification
    ///
    /// Uses SAT-only proofs with LRAT verification (Tier 2).
    /// This is the strictest trust level, suitable for kernel soundness proofs.
    ///
    /// **Note:** Tier 2 verification is not yet implemented. This profile
    /// will error at runtime until LRAT verification is added.
    ///
    /// Part of #617: Kernel acceptance policy for theory vs SAT-only proofs.
    pub fn kernel_critical() -> Self {
        Self {
            format: ProofFormat::Lrat { binary: true },
            verification_tier: 2,
            // Only SAT (no theory extensions)
            accepted_theories: HashSet::new(),
        }
    }

    /// Check if this profile requires Carcara verification
    pub fn requires_carcara(&self) -> bool {
        self.verification_tier == 1 && matches!(self.format, ProofFormat::Alethe { .. })
    }

    /// Check if this profile requires LRAT verification
    pub fn requires_lrat(&self) -> bool {
        self.verification_tier >= 2 && matches!(self.format, ProofFormat::Lrat { .. })
    }

    /// Check if a theory has full Carcara verification (no `trust` rules)
    ///
    /// Part of #619: Identify proof format/flags for Carcara acceptance.
    ///
    /// Returns `true` if the theory is in `proof_formats::CARCARA_VERIFIED_THEORIES`,
    /// meaning Carcara can verify all proof steps without `trust` rule fallback.
    pub fn is_fully_verified_theory(theory: &str) -> bool {
        proof_formats::CARCARA_VERIFIED_THEORIES.contains(&theory)
    }

    /// Check if a theory has partial Carcara support (may use `trust` rules)
    ///
    /// Part of #619: Identify proof format/flags for Carcara acceptance.
    ///
    /// Returns `true` if the theory is in `proof_formats::CARCARA_PARTIAL_THEORIES`,
    /// meaning some proof steps may use the `trust` rule and not be verified.
    pub fn is_partially_supported_theory(theory: &str) -> bool {
        proof_formats::CARCARA_PARTIAL_THEORIES.contains(&theory)
    }

    /// Check if a theory has any Carcara support (full or partial)
    ///
    /// Part of #619: Identify proof format/flags for Carcara acceptance.
    ///
    /// Returns `true` if the theory has either full verification support
    /// or partial support. Returns `false` for completely unsupported theories.
    pub fn has_carcara_support(theory: &str) -> bool {
        Self::is_fully_verified_theory(theory) || Self::is_partially_supported_theory(theory)
    }
}
