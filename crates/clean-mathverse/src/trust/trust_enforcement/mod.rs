// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Trust enforcement gates for the Mathverse Library.
//!
//! The [`TrustEnforcer`] provides hard enforcement that prevents axiomatized or
//! low-trust constants from contaminating kernel-verified ones. It acts as a
//! visibility filter: by default, only `KernelVerified` and `CertificateReplayed`
//! constants are visible. Axiomatized, universe-inconsistent, and float-approximate
//! constants require explicit opt-in via [`TrustPolicy`].
//!
//! The core invariant is **trust transitivity**: the effective trust level of a
//! theorem is `min(own_level, min(dep_levels))`. A constant cannot claim
//! `KernelVerified` if any transitive dependency is `Axiomatized` or lower.

use super::axiom_propagation::DependencyGraph;
use crate::types::{AxiomProfile, TrustLevel};

// ---------------------------------------------------------------------------
// TrustPolicy
// ---------------------------------------------------------------------------

/// Policy controlling which trust-gated constants are visible.
///
/// By default, all trust-gated categories are blocked. Each field must be
/// explicitly set to `true` to opt in to seeing those constants.
#[derive(Clone, Debug, Default)]
pub struct TrustPolicy {
    /// Allow constants with the `AXIOMATIZED` bit in their axiom profile.
    pub allow_axiomatized: bool,
    /// Allow constants with the `UNIVERSE_INCON` bit.
    pub allow_universe_inconsistent: bool,
    /// Allow constants with the `FLOAT_APPROX` bit.
    pub allow_float_approx: bool,
    /// Allow constants with the `NN_ABSTRACTION` bit.
    pub allow_nn_abstraction: bool,
    /// Allow constants at `TrustedOracle` trust level.
    pub allow_trusted_oracle: bool,
    /// Allow constants at `PartiallyAxiomatized` trust level.
    pub allow_partially_axiomatized: bool,
}

impl TrustPolicy {
    /// A policy that blocks everything trust-gated (the default).
    #[must_use]
    pub fn strict() -> Self {
        Self::default()
    }

    /// A policy that allows everything (for debugging or unrestricted use).
    #[must_use]
    pub fn permissive() -> Self {
        Self {
            allow_axiomatized: true,
            allow_universe_inconsistent: true,
            allow_float_approx: true,
            allow_nn_abstraction: true,
            allow_trusted_oracle: true,
            allow_partially_axiomatized: true,
        }
    }
}

// ---------------------------------------------------------------------------
// TrustEnforcementError
// ---------------------------------------------------------------------------

/// Errors from trust enforcement operations.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum TrustEnforcementError {
    /// A constant claims a higher trust level than its dependencies allow.
    #[error(
        "trust transitivity violation: constant {idx} claims {claimed:?} but \
         effective level is {effective:?} (dependency {dep_idx} has level {dep_level:?})"
    )]
    TransitivityViolation {
        idx: u32,
        claimed: TrustLevel,
        effective: TrustLevel,
        dep_idx: u32,
        dep_level: TrustLevel,
    },

    /// A constant is not visible under the current policy.
    #[error(
        "constant {idx} is trust-gated (profile bits: {profile_bits:#018x}, \
         trust level: {trust_level:?}) and the current policy does not allow it"
    )]
    NotVisible {
        idx: u32,
        profile_bits: u64,
        trust_level: TrustLevel,
    },

    /// Axiom profile contamination: a KernelVerified constant has axiomatized deps.
    #[error(
        "axiom contamination: constant {idx} is KernelVerified but has \
         axiomatized dependency {dep_idx} (profile: {dep_profile_bits:#018x})"
    )]
    AxiomContamination {
        idx: u32,
        dep_idx: u32,
        dep_profile_bits: u64,
    },
}

// ---------------------------------------------------------------------------
// TrustEnforcer
// ---------------------------------------------------------------------------

/// Hard enforcement gate for trust levels in the Mathverse Library.
///
/// The enforcer provides three capabilities:
///
/// 1. **Visibility filtering**: Only constants passing the [`TrustPolicy`] are
///    visible. By default, `KernelVerified` and `CertificateReplayed` constants
///    are visible; axiomatized/oracle constants require explicit opt-in.
///
/// 2. **Trust transitivity**: The effective trust level of a constant is
///    `min(own_level, min(dep_levels))`. A constant cannot claim a higher
///    trust level than its weakest transitive dependency.
///
/// 3. **Contamination detection**: If a `KernelVerified` constant has any
///    transitive dependency with `AXIOMATIZED`, `UNIVERSE_INCON`, or
///    `FLOAT_APPROX` bits, the enforcer rejects it.
pub struct TrustEnforcer {
    policy: TrustPolicy,
}

impl TrustEnforcer {
    /// Create a new trust enforcer with the given policy.
    #[must_use]
    pub fn new(policy: TrustPolicy) -> Self {
        Self { policy }
    }

    /// Create a strict enforcer (default policy: only KernelVerified and
    /// CertificateReplayed visible).
    #[must_use]
    pub fn strict() -> Self {
        Self::new(TrustPolicy::strict())
    }

    /// Create a permissive enforcer (all constants visible).
    #[must_use]
    pub fn permissive() -> Self {
        Self::new(TrustPolicy::permissive())
    }

    /// Check whether a single constant is visible under the current policy.
    ///
    /// # Errors
    ///
    /// Returns `TrustEnforcementError::NotVisible` if the constant is gated
    /// and the policy does not allow it.
    pub fn check_visible(
        &self,
        idx: u32,
        profile: AxiomProfile,
        trust_level: TrustLevel,
    ) -> Result<(), TrustEnforcementError> {
        // Check trust level visibility.
        match trust_level {
            TrustLevel::KernelVerified
            | TrustLevel::AxiomDependent
            | TrustLevel::CertificateReplayed => {
                // These are always visible (they represent verified work).
            }
            TrustLevel::PartiallyAxiomatized => {
                if !self.policy.allow_partially_axiomatized {
                    return Err(TrustEnforcementError::NotVisible {
                        idx,
                        profile_bits: profile.0,
                        trust_level,
                    });
                }
            }
            TrustLevel::TrustedOracle => {
                if !self.policy.allow_trusted_oracle {
                    return Err(TrustEnforcementError::NotVisible {
                        idx,
                        profile_bits: profile.0,
                        trust_level,
                    });
                }
            }
        }

        // Check axiom profile gating bits.
        if profile.has(AxiomProfile::AXIOMATIZED) && !self.policy.allow_axiomatized {
            return Err(TrustEnforcementError::NotVisible {
                idx,
                profile_bits: profile.0,
                trust_level,
            });
        }
        if profile.has(AxiomProfile::UNIVERSE_INCON) && !self.policy.allow_universe_inconsistent {
            return Err(TrustEnforcementError::NotVisible {
                idx,
                profile_bits: profile.0,
                trust_level,
            });
        }
        if profile.has(AxiomProfile::FLOAT_APPROX) && !self.policy.allow_float_approx {
            return Err(TrustEnforcementError::NotVisible {
                idx,
                profile_bits: profile.0,
                trust_level,
            });
        }
        if profile.has(AxiomProfile::NN_ABSTRACTION) && !self.policy.allow_nn_abstraction {
            return Err(TrustEnforcementError::NotVisible {
                idx,
                profile_bits: profile.0,
                trust_level,
            });
        }

        Ok(())
    }

    /// Filter a set of constants, returning indices of those visible under
    /// the current policy.
    #[must_use]
    pub fn filter_visible(&self, constants: &[(AxiomProfile, TrustLevel)]) -> Vec<u32> {
        constants
            .iter()
            .enumerate()
            .filter(|(i, (profile, trust))| self.check_visible(*i as u32, *profile, *trust).is_ok())
            .map(|(i, _)| i as u32)
            .collect()
    }

    /// Compute the effective trust level of a constant given its dependencies.
    ///
    /// The effective level is `min(own_level, min(dep_levels))`, using the
    /// `TrustLevel` ordering where `KernelVerified` is highest (most trusted).
    #[must_use]
    pub fn effective_trust_level(own_level: TrustLevel, dep_levels: &[TrustLevel]) -> TrustLevel {
        let mut effective = own_level;
        for &dep_level in dep_levels {
            if trust_level_rank(dep_level) > trust_level_rank(effective) {
                effective = dep_level;
            }
        }
        effective
    }

    /// Enforce trust transitivity across an entire dependency graph.
    ///
    /// For each node, verifies that the claimed trust level is not higher
    /// than the effective trust level (determined by its dependencies).
    ///
    /// # Errors
    ///
    /// Returns the first `TransitivityViolation` found.
    pub fn enforce_transitivity(
        &self,
        graph: &DependencyGraph,
        trust_levels: &[TrustLevel],
    ) -> Result<(), TrustEnforcementError> {
        for idx in 0..graph.node_count() {
            let claimed = match trust_levels.get(idx) {
                Some(&t) => t,
                None => continue,
            };

            for &dep_idx in graph.dependencies(idx as u32) {
                let dep_level = match trust_levels.get(dep_idx as usize) {
                    Some(&t) => t,
                    None => continue,
                };

                // If the dependency has a lower trust level (higher rank number)
                // than the claimed level, this is a violation.
                if trust_level_rank(dep_level) > trust_level_rank(claimed) {
                    return Err(TrustEnforcementError::TransitivityViolation {
                        idx: idx as u32,
                        claimed,
                        effective: dep_level,
                        dep_idx,
                        dep_level,
                    });
                }
            }
        }
        Ok(())
    }

    /// Detect axiom contamination: find KernelVerified constants that
    /// transitively depend on axiomatized material.
    ///
    /// This is the hard gate: if constant A depends on axiomatized constant B,
    /// then A cannot be KernelVerified.
    ///
    /// Returns all contamination violations found.
    #[must_use]
    pub fn detect_contamination(
        &self,
        graph: &DependencyGraph,
        trust_levels: &[TrustLevel],
        profiles: &[AxiomProfile],
    ) -> Vec<TrustEnforcementError> {
        let mut violations = Vec::new();

        for idx in 0..graph.node_count() {
            match trust_levels.get(idx) {
                Some(&TrustLevel::KernelVerified) => {}
                _ => continue,
            }

            // Check all transitive dependencies.
            let reachable = graph.reachable_from(idx as u32);
            for dep_idx in reachable {
                let dep_profile = profiles
                    .get(dep_idx as usize)
                    .copied()
                    .unwrap_or(AxiomProfile::NONE);

                // Check for trust-gated bits in any dependency.
                if dep_profile.is_trust_gated() {
                    violations.push(TrustEnforcementError::AxiomContamination {
                        idx: idx as u32,
                        dep_idx,
                        dep_profile_bits: dep_profile.0,
                    });
                }
            }
        }

        violations
    }

    /// Run all enforcement checks and return a summary.
    #[must_use]
    pub fn enforce_all(
        &self,
        graph: &DependencyGraph,
        trust_levels: &[TrustLevel],
        profiles: &[AxiomProfile],
    ) -> EnforcementReport {
        // Visibility check.
        let mut visibility_violations = Vec::new();
        for (idx, (profile, trust)) in profiles.iter().zip(trust_levels.iter()).enumerate() {
            if let Err(e) = self.check_visible(idx as u32, *profile, *trust) {
                visibility_violations.push(e);
            }
        }

        // Transitivity check.
        let transitivity_violation = self.enforce_transitivity(graph, trust_levels).err();

        // Contamination check.
        let contamination_violations = self.detect_contamination(graph, trust_levels, profiles);

        let total_violations = visibility_violations.len()
            + if transitivity_violation.is_some() {
                1
            } else {
                0
            }
            + contamination_violations.len();

        EnforcementReport {
            total_constants: trust_levels.len(),
            visible_count: self
                .filter_visible(
                    &profiles
                        .iter()
                        .zip(trust_levels.iter())
                        .map(|(&p, &t)| (p, t))
                        .collect::<Vec<_>>(),
                )
                .len(),
            visibility_violations,
            transitivity_violation,
            contamination_violations,
            is_clean: total_violations == 0,
        }
    }
}

// ---------------------------------------------------------------------------
// EnforcementReport
// ---------------------------------------------------------------------------

/// Summary report from running all enforcement checks.
#[derive(Debug)]
pub struct EnforcementReport {
    /// Total number of constants checked.
    pub total_constants: usize,
    /// Number of constants visible under the policy.
    pub visible_count: usize,
    /// Constants blocked by the visibility policy.
    pub visibility_violations: Vec<TrustEnforcementError>,
    /// First transitivity violation found (if any).
    pub transitivity_violation: Option<TrustEnforcementError>,
    /// KernelVerified constants contaminated by axiomatized dependencies.
    pub contamination_violations: Vec<TrustEnforcementError>,
    /// Whether all enforcement checks passed.
    pub is_clean: bool,
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Map trust levels to a numeric rank for ordering comparisons.
/// Lower rank = higher trust. KernelVerified is most trusted (rank 0).
fn trust_level_rank(level: TrustLevel) -> u8 {
    match level {
        TrustLevel::KernelVerified => 0,
        TrustLevel::AxiomDependent => 1,
        TrustLevel::CertificateReplayed => 2,
        TrustLevel::PartiallyAxiomatized => 3,
        TrustLevel::TrustedOracle => 4,
    }
}

#[cfg(test)]
mod tests_enforcement;
#[cfg(test)]
mod tests_self_verification;
