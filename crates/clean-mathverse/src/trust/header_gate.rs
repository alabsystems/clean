// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Unified trust-gate enforcement for Mathverse constant visibility.
//!
//! This module provides a small, standalone API for tactic-facing trust
//! filtering based only on [`MathverseConstantHeader::axiom_profile`]. It does not
//! use [`crate::types::TrustLevel`]. Instead, each [`GateTrustLevel`] maps to a
//! specific axiom-profile condition:
//!
//! - `KernelVerified`: no supported gate bits are present
//! - `TrustedOracle`: `AxiomProfile::SMT_ORACLE`
//! - `Axiomatized`: `AxiomProfile::AXIOMATIZED`
//! - `UniverseIncon`: `AxiomProfile::UNIVERSE_INCON`
//! - `FloatApprox`: `AxiomProfile::FLOAT_APPROX`
//! - `NnAbstraction`: `AxiomProfile::NN_ABSTRACTION`

use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::types::{AxiomProfile, MathverseConstantHeader};

pub(crate) const SUPPORTED_GATE_BITS: AxiomProfile =
    AxiomProfile::new(AxiomProfile::TRUST_GATED.0 | AxiomProfile::SMT_ORACLE.0);

pub(crate) const KERNEL_VERIFIED_MASK: u8 = 1 << 0;
pub(crate) const TRUSTED_ORACLE_MASK: u8 = 1 << 1;
pub(crate) const AXIOMATIZED_MASK: u8 = 1 << 2;
pub(crate) const UNIVERSE_INCON_MASK: u8 = 1 << 3;
pub(crate) const FLOAT_APPROX_MASK: u8 = 1 << 4;
pub(crate) const NN_ABSTRACTION_MASK: u8 = 1 << 5;
pub(crate) const ALL_LEVEL_MASKS: u8 = KERNEL_VERIFIED_MASK
    | TRUSTED_ORACLE_MASK
    | AXIOMATIZED_MASK
    | UNIVERSE_INCON_MASK
    | FLOAT_APPROX_MASK
    | NN_ABSTRACTION_MASK;

/// Errors from trust-gate level conversions.
#[derive(Clone, Debug, PartialEq, Eq, Error, Serialize, Deserialize)]
#[non_exhaustive]
pub enum TrustGateError {
    /// The provided bits do not correspond to exactly one gate level.
    #[error("axiom profile bits {bits:#018x} do not map to a single gate trust level")]
    InvalidLevelBits { bits: u64 },
}

/// Visibility classes enforced by the unified trust gate.
///
/// These levels are derived from axiom-profile bits and are not the same as
/// [`crate::types::TrustLevel`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum GateTrustLevel {
    /// No supported trust-gate bits are present.
    KernelVerified,
    /// The constant depends on an oracle-backed import (`SMT_ORACLE`).
    TrustedOracle,
    /// The constant has `AXIOMATIZED` in its profile.
    Axiomatized,
    /// The constant has `UNIVERSE_INCON` in its profile.
    UniverseIncon,
    /// The constant has `FLOAT_APPROX` in its profile.
    FloatApprox,
    /// The constant has `NN_ABSTRACTION` in its profile.
    NnAbstraction,
}

impl GateTrustLevel {
    /// Return the axiom-profile bit represented by this level.
    ///
    /// `KernelVerified` corresponds to the absence of any supported gate bits,
    /// so it maps to `AxiomProfile::NONE`.
    #[must_use]
    pub const fn axiom_profile_bits(self) -> AxiomProfile {
        match self {
            Self::KernelVerified => AxiomProfile::NONE,
            Self::TrustedOracle => AxiomProfile::SMT_ORACLE,
            Self::Axiomatized => AxiomProfile::AXIOMATIZED,
            Self::UniverseIncon => AxiomProfile::UNIVERSE_INCON,
            Self::FloatApprox => AxiomProfile::FLOAT_APPROX,
            Self::NnAbstraction => AxiomProfile::NN_ABSTRACTION,
        }
    }

    /// Convert a single axiom-profile bit to a gate trust level.
    ///
    /// # Errors
    ///
    /// Returns [`TrustGateError::InvalidLevelBits`] when the provided profile
    /// is not one of the supported single-bit gate markers.
    pub fn try_from_axiom_profile(bits: AxiomProfile) -> Result<Self, TrustGateError> {
        match bits.0 {
            0 => Ok(Self::KernelVerified),
            x if x == AxiomProfile::SMT_ORACLE.0 => Ok(Self::TrustedOracle),
            x if x == AxiomProfile::AXIOMATIZED.0 => Ok(Self::Axiomatized),
            x if x == AxiomProfile::UNIVERSE_INCON.0 => Ok(Self::UniverseIncon),
            x if x == AxiomProfile::FLOAT_APPROX.0 => Ok(Self::FloatApprox),
            x if x == AxiomProfile::NN_ABSTRACTION.0 => Ok(Self::NnAbstraction),
            bits => Err(TrustGateError::InvalidLevelBits { bits }),
        }
    }

    #[must_use]
    pub(crate) const fn policy_mask(self) -> u8 {
        match self {
            Self::KernelVerified => KERNEL_VERIFIED_MASK,
            Self::TrustedOracle => TRUSTED_ORACLE_MASK,
            Self::Axiomatized => AXIOMATIZED_MASK,
            Self::UniverseIncon => UNIVERSE_INCON_MASK,
            Self::FloatApprox => FLOAT_APPROX_MASK,
            Self::NnAbstraction => NN_ABSTRACTION_MASK,
        }
    }

    #[must_use]
    pub(crate) const fn is_present_in(self, profile: AxiomProfile) -> bool {
        match self {
            Self::KernelVerified => (profile.0 & SUPPORTED_GATE_BITS.0) == 0,
            _ => profile.has(self.axiom_profile_bits()),
        }
    }
}

/// Policy controlling which gate-trust levels are visible to tactics.
///
/// The default policy is strict: only constants with no supported gate bits are
/// visible. Additional levels can be enabled with [`GateTrustPolicy::with_level`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct GateTrustPolicy {
    visible_level_mask: u8,
}

impl GateTrustPolicy {
    /// Construct the default policy: only `KernelVerified` is visible.
    #[must_use]
    pub const fn new() -> Self {
        Self {
            visible_level_mask: KERNEL_VERIFIED_MASK,
        }
    }

    /// Enable a single gate level and return the updated policy.
    #[must_use]
    pub const fn with_level(self, level: GateTrustLevel) -> Self {
        Self {
            visible_level_mask: self.visible_level_mask | level.policy_mask(),
        }
    }

    /// Construct a policy that allows every supported gate level.
    #[must_use]
    pub const fn permissive() -> Self {
        Self {
            visible_level_mask: ALL_LEVEL_MASKS,
        }
    }

    /// Check whether a gate level is allowed by this policy.
    #[must_use]
    pub const fn allows(&self, level: GateTrustLevel) -> bool {
        (self.visible_level_mask & level.policy_mask()) != 0
    }

    /// Return the union of all non-kernel axiom bits allowed by the policy.
    #[must_use]
    pub const fn allowed_axiom_bits(&self) -> AxiomProfile {
        let mut bits = 0u64;

        if self.allows(GateTrustLevel::TrustedOracle) {
            bits |= AxiomProfile::SMT_ORACLE.0;
        }
        if self.allows(GateTrustLevel::Axiomatized) {
            bits |= AxiomProfile::AXIOMATIZED.0;
        }
        if self.allows(GateTrustLevel::UniverseIncon) {
            bits |= AxiomProfile::UNIVERSE_INCON.0;
        }
        if self.allows(GateTrustLevel::FloatApprox) {
            bits |= AxiomProfile::FLOAT_APPROX.0;
        }
        if self.allows(GateTrustLevel::NnAbstraction) {
            bits |= AxiomProfile::NN_ABSTRACTION.0;
        }

        AxiomProfile::new(bits)
    }
}

impl Default for GateTrustPolicy {
    fn default() -> Self {
        Self::new()
    }
}

/// Hard trust-gate enforcement based on header axiom-profile bits.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct TrustGateEnforcer;

impl TrustGateEnforcer {
    /// Check whether a constant header is visible under the supplied policy.
    ///
    /// Visibility is decided only from `header.axiom_profile`. A constant that
    /// carries multiple gate bits is visible if and only if the policy allows
    /// every matched [`GateTrustLevel`].
    #[must_use]
    pub fn is_visible(header: &MathverseConstantHeader, policy: &GateTrustPolicy) -> bool {
        let profile = header.axiom_profile;

        if GateTrustLevel::KernelVerified.is_present_in(profile) {
            return policy.allows(GateTrustLevel::KernelVerified);
        }

        if GateTrustLevel::TrustedOracle.is_present_in(profile)
            && !policy.allows(GateTrustLevel::TrustedOracle)
        {
            return false;
        }
        if GateTrustLevel::Axiomatized.is_present_in(profile)
            && !policy.allows(GateTrustLevel::Axiomatized)
        {
            return false;
        }
        if GateTrustLevel::UniverseIncon.is_present_in(profile)
            && !policy.allows(GateTrustLevel::UniverseIncon)
        {
            return false;
        }
        if GateTrustLevel::FloatApprox.is_present_in(profile)
            && !policy.allows(GateTrustLevel::FloatApprox)
        {
            return false;
        }
        if GateTrustLevel::NnAbstraction.is_present_in(profile)
            && !policy.allows(GateTrustLevel::NnAbstraction)
        {
            return false;
        }

        true
    }

    /// Filter a slice of headers down to those visible under the supplied policy.
    #[must_use]
    pub fn filter_visible<'a>(
        headers: &'a [MathverseConstantHeader],
        policy: &GateTrustPolicy,
    ) -> Vec<&'a MathverseConstantHeader> {
        headers
            .iter()
            .filter(|header| Self::is_visible(header, policy))
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::{ImportConfidence, SourceSystem, NO_VALUE};

    fn make_header(profile: AxiomProfile) -> MathverseConstantHeader {
        MathverseConstantHeader {
            name_idx: 7,
            type_idx: 11,
            value_idx: 13,
            source_system: SourceSystem::Lean4 as u8,
            import_confidence: ImportConfidence::KernelVerified as u8,
            content_domain: 0,
            decl_kind: 0,
            axiom_profile: profile,
            sidecar_digest: 0xABCD_EF01,
            provenance_idx: 17,
            level_params_start: 0,
            level_params_count: 0,
            _pad2: [0u8; 26],
        }
    }

    fn make_axiomatized(profile: AxiomProfile) -> MathverseConstantHeader {
        MathverseConstantHeader {
            name_idx: 19,
            type_idx: 23,
            value_idx: NO_VALUE,
            source_system: SourceSystem::SmtSolver as u8,
            import_confidence: ImportConfidence::Axiomatized as u8,
            content_domain: 0,
            decl_kind: 0,
            axiom_profile: profile,
            sidecar_digest: 0x1234_5678,
            provenance_idx: 29,
            level_params_start: 0,
            level_params_count: 0,
            _pad2: [0u8; 26],
        }
    }

    #[test]
    fn gate_level_to_axiom_profile_mapping_is_stable() {
        assert_eq!(
            GateTrustLevel::KernelVerified.axiom_profile_bits(),
            AxiomProfile::NONE
        );
        assert_eq!(
            GateTrustLevel::TrustedOracle.axiom_profile_bits(),
            AxiomProfile::SMT_ORACLE
        );
        assert_eq!(
            GateTrustLevel::Axiomatized.axiom_profile_bits(),
            AxiomProfile::AXIOMATIZED
        );
        assert_eq!(
            GateTrustLevel::UniverseIncon.axiom_profile_bits(),
            AxiomProfile::UNIVERSE_INCON
        );
        assert_eq!(
            GateTrustLevel::FloatApprox.axiom_profile_bits(),
            AxiomProfile::FLOAT_APPROX
        );
        assert_eq!(
            GateTrustLevel::NnAbstraction.axiom_profile_bits(),
            AxiomProfile::NN_ABSTRACTION
        );
    }

    #[test]
    fn try_from_axiom_profile_accepts_supported_singletons() {
        assert_eq!(
            GateTrustLevel::try_from_axiom_profile(AxiomProfile::NONE).unwrap(),
            GateTrustLevel::KernelVerified
        );
        assert_eq!(
            GateTrustLevel::try_from_axiom_profile(AxiomProfile::SMT_ORACLE).unwrap(),
            GateTrustLevel::TrustedOracle
        );
        assert_eq!(
            GateTrustLevel::try_from_axiom_profile(AxiomProfile::AXIOMATIZED).unwrap(),
            GateTrustLevel::Axiomatized
        );
    }

    #[test]
    fn try_from_axiom_profile_rejects_composite_or_unknown_bits() {
        let composite = GateTrustLevel::try_from_axiom_profile(
            AxiomProfile::SMT_ORACLE | AxiomProfile::AXIOMATIZED,
        );
        assert!(matches!(
            composite,
            Err(TrustGateError::InvalidLevelBits { .. })
        ));

        let unknown = GateTrustLevel::try_from_axiom_profile(AxiomProfile::CHOICE);
        assert!(matches!(
            unknown,
            Err(TrustGateError::InvalidLevelBits { .. })
        ));
    }

    #[test]
    fn default_policy_allows_only_kernel_verified_gate_class() {
        let policy = GateTrustPolicy::default();

        assert!(policy.allows(GateTrustLevel::KernelVerified));
        assert!(!policy.allows(GateTrustLevel::TrustedOracle));
        assert!(!policy.allows(GateTrustLevel::Axiomatized));
        assert!(!policy.allows(GateTrustLevel::UniverseIncon));
        assert!(!policy.allows(GateTrustLevel::FloatApprox));
        assert!(!policy.allows(GateTrustLevel::NnAbstraction));
        assert_eq!(policy.allowed_axiom_bits(), AxiomProfile::NONE);
    }

    #[test]
    fn with_level_builder_is_additive() {
        let policy = GateTrustPolicy::default()
            .with_level(GateTrustLevel::TrustedOracle)
            .with_level(GateTrustLevel::FloatApprox);

        assert!(policy.allows(GateTrustLevel::KernelVerified));
        assert!(policy.allows(GateTrustLevel::TrustedOracle));
        assert!(policy.allows(GateTrustLevel::FloatApprox));
        assert!(!policy.allows(GateTrustLevel::Axiomatized));
        assert_eq!(
            policy.allowed_axiom_bits(),
            AxiomProfile::SMT_ORACLE | AxiomProfile::FLOAT_APPROX
        );
    }

    #[test]
    fn permissive_policy_allows_every_level() {
        let policy = GateTrustPolicy::permissive();

        assert!(policy.allows(GateTrustLevel::KernelVerified));
        assert!(policy.allows(GateTrustLevel::TrustedOracle));
        assert!(policy.allows(GateTrustLevel::Axiomatized));
        assert!(policy.allows(GateTrustLevel::UniverseIncon));
        assert!(policy.allows(GateTrustLevel::FloatApprox));
        assert!(policy.allows(GateTrustLevel::NnAbstraction));
        assert_eq!(policy.allowed_axiom_bits(), SUPPORTED_GATE_BITS);
    }

    #[test]
    fn default_policy_allows_non_gated_axiom_profiles() {
        let header = make_header(AxiomProfile::CHOICE | AxiomProfile::LEM);
        let policy = GateTrustPolicy::default();

        assert!(TrustGateEnforcer::is_visible(&header, &policy));
    }

    #[test]
    fn default_policy_blocks_every_supported_non_kernel_gate_bit() {
        let policy = GateTrustPolicy::default();

        assert!(!TrustGateEnforcer::is_visible(
            &make_header(AxiomProfile::SMT_ORACLE),
            &policy
        ));
        assert!(!TrustGateEnforcer::is_visible(
            &make_axiomatized(AxiomProfile::AXIOMATIZED),
            &policy
        ));
        assert!(!TrustGateEnforcer::is_visible(
            &make_header(AxiomProfile::UNIVERSE_INCON),
            &policy
        ));
        assert!(!TrustGateEnforcer::is_visible(
            &make_header(AxiomProfile::FLOAT_APPROX),
            &policy
        ));
        assert!(!TrustGateEnforcer::is_visible(
            &make_header(AxiomProfile::NN_ABSTRACTION),
            &policy
        ));
    }

    #[test]
    fn multi_bit_profiles_require_every_matched_level() {
        let header = make_axiomatized(AxiomProfile::SMT_ORACLE | AxiomProfile::AXIOMATIZED);

        let oracle_only = GateTrustPolicy::default().with_level(GateTrustLevel::TrustedOracle);
        assert!(!TrustGateEnforcer::is_visible(&header, &oracle_only));

        let axiom_only = GateTrustPolicy::default().with_level(GateTrustLevel::Axiomatized);
        assert!(!TrustGateEnforcer::is_visible(&header, &axiom_only));

        let both = GateTrustPolicy::default()
            .with_level(GateTrustLevel::TrustedOracle)
            .with_level(GateTrustLevel::Axiomatized);
        assert!(TrustGateEnforcer::is_visible(&header, &both));
    }

    #[test]
    fn filter_visible_preserves_order_and_returns_references() {
        let headers = vec![
            make_header(AxiomProfile::NONE),
            make_header(AxiomProfile::SMT_ORACLE),
            make_axiomatized(AxiomProfile::AXIOMATIZED),
            make_header(AxiomProfile::FLOAT_APPROX),
            make_header(AxiomProfile::CHOICE),
        ];

        let policy = GateTrustPolicy::default().with_level(GateTrustLevel::Axiomatized);
        let visible = TrustGateEnforcer::filter_visible(&headers, &policy);

        assert_eq!(visible.len(), 3);
        assert!(std::ptr::eq(visible[0], &headers[0]));
        assert!(std::ptr::eq(visible[1], &headers[2]));
        assert!(std::ptr::eq(visible[2], &headers[4]));
    }

    #[test]
    fn kernel_verified_detection_uses_supported_gate_bits_only() {
        let header = make_header(AxiomProfile::HOL_AXIOMS | AxiomProfile::BRIDGE_AXIOM);
        let policy = GateTrustPolicy::default();

        assert!(GateTrustLevel::KernelVerified.is_present_in(header.axiom_profile));
        assert!(TrustGateEnforcer::is_visible(&header, &policy));
    }

    #[test]
    fn serde_roundtrip_preserves_policy() {
        let policy = GateTrustPolicy::default()
            .with_level(GateTrustLevel::TrustedOracle)
            .with_level(GateTrustLevel::UniverseIncon);

        let json = serde_json::to_string(&policy).unwrap();
        let restored: GateTrustPolicy = serde_json::from_str(&json).unwrap();

        assert_eq!(policy, restored);
        assert!(restored.allows(GateTrustLevel::KernelVerified));
        assert!(restored.allows(GateTrustLevel::TrustedOracle));
        assert!(restored.allows(GateTrustLevel::UniverseIncon));
        assert!(!restored.allows(GateTrustLevel::Axiomatized));
    }
}
