// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Trust gate enforcement: no leakage from axiomatized to kernel-verified.
//!
//! The trust gate enforces a hierarchy: constants at higher trust levels
//! cannot depend on constants at lower trust levels without explicit
//! acknowledgment. This prevents unsound conclusions from leaking into
//! the kernel-verified portion of the library.
//!
//! Trust level hierarchy (highest to lowest trust):
//! - `KernelVerified`: fully verified by the clean kernel, no axioms
//! - `AxiomDependent`: verified with known axiom dependencies
//! - `CertificateReplayed`: imported with proof certificate replay
//! - `PartiallyAxiomatized`: imported with axiomatized gaps
//! - `TrustedOracle`: trusted external solver without certificate

use hashbrown::{HashMap, HashSet};

use super::axiom_propagation::DependencyGraph;
use crate::types::{AxiomProfile, TrustLevel};

/// Errors from trust gate operations.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum TrustGateError {
    /// A dependency violates the trust gate policy.
    #[error(
        "trust violation: {parent_trust:?} (node {parent_idx}) depends on \
         {child_trust:?} (node {child_idx})"
    )]
    TrustViolation {
        parent_idx: u32,
        parent_trust: TrustLevel,
        child_idx: u32,
        child_trust: TrustLevel,
    },
}

/// A single trust violation record.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct TrustViolation {
    /// Index of the parent (dependent) node.
    pub parent_idx: u32,
    /// Trust level of the parent node.
    pub parent_trust: TrustLevel,
    /// Index of the child (dependency) node.
    pub child_idx: u32,
    /// Trust level of the child node.
    pub child_trust: TrustLevel,
    /// Human-readable violation description.
    pub violation: String,
}

/// Trust gate: enforces that no constant at a higher trust level depends on
/// a constant at a lower trust level without explicit acknowledgment.
///
/// The gate maintains a policy map from each `TrustLevel` to the set of
/// `TrustLevel`s it is allowed to depend on. Dependencies outside the allowed
/// set are violations.
pub struct TrustGate {
    /// Map from TrustLevel to the set of TrustLevels it may depend on.
    pub(crate) allowed_deps: HashMap<TrustLevel, HashSet<TrustLevel>>,
}

impl std::fmt::Debug for TrustGate {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("TrustGate")
            .field("policy_count", &self.allowed_deps.len())
            .finish()
    }
}

impl Clone for TrustGate {
    fn clone(&self) -> Self {
        Self {
            allowed_deps: self.allowed_deps.clone(),
        }
    }
}

impl TrustGate {
    /// Construct a trust gate with the default hierarchical policy.
    ///
    /// Default policy:
    /// - `KernelVerified` can only depend on `KernelVerified`
    /// - `AxiomDependent` can depend on `KernelVerified` + `AxiomDependent`
    /// - `CertificateReplayed` can depend on above + `CertificateReplayed`
    /// - `PartiallyAxiomatized` can depend on above + `PartiallyAxiomatized`
    /// - `TrustedOracle` can depend on any level
    #[must_use]
    pub fn default_policy() -> Self {
        let mut allowed_deps = HashMap::new();

        // KernelVerified: strictest — only depends on other kernel-verified constants.
        allowed_deps.insert(
            TrustLevel::KernelVerified,
            HashSet::from_iter([TrustLevel::KernelVerified]),
        );

        // AxiomDependent: can depend on kernel-verified and other axiom-dependent.
        allowed_deps.insert(
            TrustLevel::AxiomDependent,
            HashSet::from_iter([TrustLevel::KernelVerified, TrustLevel::AxiomDependent]),
        );

        // CertificateReplayed: can depend on the above plus other replayed.
        allowed_deps.insert(
            TrustLevel::CertificateReplayed,
            HashSet::from_iter([
                TrustLevel::KernelVerified,
                TrustLevel::AxiomDependent,
                TrustLevel::CertificateReplayed,
            ]),
        );

        // PartiallyAxiomatized: can depend on everything except TrustedOracle.
        allowed_deps.insert(
            TrustLevel::PartiallyAxiomatized,
            HashSet::from_iter([
                TrustLevel::KernelVerified,
                TrustLevel::AxiomDependent,
                TrustLevel::CertificateReplayed,
                TrustLevel::PartiallyAxiomatized,
            ]),
        );

        // TrustedOracle: can depend on any trust level.
        allowed_deps.insert(
            TrustLevel::TrustedOracle,
            HashSet::from_iter([
                TrustLevel::KernelVerified,
                TrustLevel::AxiomDependent,
                TrustLevel::CertificateReplayed,
                TrustLevel::PartiallyAxiomatized,
                TrustLevel::TrustedOracle,
            ]),
        );

        Self { allowed_deps }
    }

    /// Construct a trust gate with a custom policy.
    #[must_use]
    pub fn with_policy(allowed_deps: HashMap<TrustLevel, HashSet<TrustLevel>>) -> Self {
        Self { allowed_deps }
    }

    /// Check whether a single dependency relationship is allowed.
    ///
    /// # Errors
    ///
    /// Returns `TrustGateError::TrustViolation` if the dependency is not allowed
    /// by the policy.
    pub fn check_dependency(
        &self,
        parent_trust: TrustLevel,
        child_trust: TrustLevel,
    ) -> Result<(), TrustGateError> {
        let allowed = self
            .allowed_deps
            .get(&parent_trust)
            .is_some_and(|set| set.contains(&child_trust));

        if allowed {
            Ok(())
        } else {
            Err(TrustGateError::TrustViolation {
                parent_idx: 0,
                parent_trust,
                child_idx: 0,
                child_trust,
            })
        }
    }

    /// Scan the entire dependency graph for trust violations.
    ///
    /// Returns all violations found (not just the first one).
    #[must_use]
    pub fn audit_graph(
        &self,
        graph: &DependencyGraph,
        trust_levels: &[TrustLevel],
    ) -> Vec<TrustViolation> {
        let mut violations = Vec::new();

        for parent_idx in 0..graph.node_count() {
            let parent_trust = match trust_levels.get(parent_idx) {
                Some(&t) => t,
                None => continue,
            };

            for &child_idx in graph.dependencies(parent_idx as u32) {
                let child_trust = match trust_levels.get(child_idx as usize) {
                    Some(&t) => t,
                    None => continue,
                };

                let allowed = self
                    .allowed_deps
                    .get(&parent_trust)
                    .is_some_and(|set| set.contains(&child_trust));

                if !allowed {
                    violations.push(TrustViolation {
                        parent_idx: parent_idx as u32,
                        parent_trust,
                        child_idx,
                        child_trust,
                        violation: format!(
                            "{:?} (node {}) cannot depend on {:?} (node {})",
                            parent_trust, parent_idx, child_trust, child_idx
                        ),
                    });
                }
            }
        }

        violations
    }

    /// Check if a trust level is present in the policy.
    #[must_use]
    pub fn has_policy_for(&self, trust: TrustLevel) -> bool {
        self.allowed_deps.contains_key(&trust)
    }
}

/// Training data export gate: hard filter on what can be used for proof
/// generation training.
///
/// Only constants that are kernel-verified with no axiom dependencies can be
/// exported for AI proof generation training. This prevents training data
/// pollution from axiomatized or oracle-dependent material.
pub struct TrainingExportGate;

impl TrainingExportGate {
    /// Check if a single constant is exportable for proof generation training.
    ///
    /// Only `KernelVerified` constants with an empty axiom profile (no axiom
    /// dependencies) can be exported.
    #[must_use]
    pub fn can_export_for_training(profile: AxiomProfile, trust: TrustLevel) -> bool {
        profile.is_kernel_verified() && trust == TrustLevel::KernelVerified
    }

    /// Filter a set of constants to only those exportable for training.
    ///
    /// Returns indices into the input slice of constants that pass the export
    /// gate.
    #[must_use]
    pub fn filter_exportable(constants: &[(AxiomProfile, TrustLevel)]) -> Vec<usize> {
        constants
            .iter()
            .enumerate()
            .filter(|(_, (profile, trust))| Self::can_export_for_training(*profile, *trust))
            .map(|(idx, _)| idx)
            .collect()
    }

    /// Count how many constants in a set are exportable for training.
    #[must_use]
    pub fn count_exportable(constants: &[(AxiomProfile, TrustLevel)]) -> usize {
        constants
            .iter()
            .filter(|(profile, trust)| Self::can_export_for_training(*profile, *trust))
            .count()
    }
}
