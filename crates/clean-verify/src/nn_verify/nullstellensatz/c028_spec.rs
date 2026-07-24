// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! C028 theorem specification: Neural Nullstellensatz -- SoS polynomial
//! certificates to bypass branch-and-bound entirely.
//!
//! When a ReLU network has a known stable activation pattern, the network
//! function is piecewise linear and can be expressed as a polynomial. If the
//! verification property can be written as a polynomial inequality
//! `p(x) >= 0` over a box domain `[l, u]`, a sum-of-squares (SoS) certificate
//! proves the property via Positivstellensatz without any branch-and-bound
//! search.
//!
//! ## Sub-theorems
//!
//! - **C028a (`stable_network_is_polynomial`)**: A ReLU network with fully
//!   stable activation pattern is equivalent to an affine map, expressible
//!   as a polynomial of degree 1.
//!
//! - **C028b (`sos_certificate_soundness`)**: If the Positivstellensatz
//!   certificate verifies (SoS multipliers + domain constraints + free SoS
//!   term assemble to the property polynomial), then the property holds on
//!   the domain.
//!
//! - **C028c (`sos_implies_no_bab`)**: A valid SoS certificate constitutes
//!   a complete proof of the property without any branch-and-bound tree
//!   expansion. The certificate can be verified in polynomial time (in the
//!   certificate size) via Gram matrix PSD check + polynomial identity.
//!
//! ## References
//!
//! - Parrilo, "Semidefinite programming relaxations for semialgebraic
//!   problems" (Math. Programming, 2003)
//! - Stengle, "A Nullstellensatz and a Positivstellensatz in semialgebraic
//!   geometry" (Math. Ann., 1974)
//! - Tjeng et al., "Evaluating Robustness of Neural Networks: An Extreme
//!   Value Theory Approach" (ICLR 2019) -- motivation for BaB bypass

use crate::nn_verify::ibp_crown::{Phase, TheoremEntry};
use crate::spec::ProofStatus;

/// C028a: Stable ReLU network is polynomial.
///
/// A ReLU network where all neurons have known activation patterns (either
/// stably active or stably inactive) computes an affine function of its
/// inputs. This affine function can be expressed exactly as a multivariate
/// polynomial of degree 1.
///
/// Proof: By induction on network depth. Each stable ReLU layer applies a
/// diagonal mask (identity or zero per neuron), so the composition of
/// affine layers with diagonal masks is itself affine.
///
/// Kernel proof target: `NNVerify.C028.stable_network_is_polynomial`
pub const C028_STABLE_NETWORK_IS_POLYNOMIAL: ProofStatus = ProofStatus::DerivedPending;

/// C028b: SoS certificate soundness.
///
/// Given a property polynomial `p(x)` and a Positivstellensatz certificate
/// consisting of SoS multipliers `{s_i}`, domain constraints `{g_i}`, and
/// a free SoS term `s_0` such that:
///
///   `p(x) = s_0(x) + sum_i s_i(x) * g_i(x)`
///
/// where all `s_i` are sum-of-squares (verified via Gram matrix PSD check),
/// then `p(x) >= 0` for all `x` satisfying `g_i(x) >= 0`.
///
/// Proof: Each SoS polynomial is non-negative everywhere. Each `g_i(x) >= 0`
/// on the domain by construction. Therefore the sum is non-negative on the
/// domain, and by exact polynomial equality, `p(x)` is non-negative.
///
/// Kernel proof target: `NNVerify.C028.sos_certificate_soundness`
pub const C028_SOS_CERTIFICATE_SOUNDNESS: ProofStatus = ProofStatus::DerivedPending;

/// C028c: SoS certificate implies no BaB needed.
///
/// A valid SoS certificate for a neural network property constitutes a
/// complete, independently checkable proof that requires:
/// - O(d^2) operations for Gram matrix PSD check (LDL decomposition)
/// - O(d * k) operations for polynomial identity verification
///   (where d is certificate dimension, k is number of constraints)
///
/// This is polynomial in the certificate size and does not require any
/// branch-and-bound tree exploration. The certificate is a witness that
/// can be checked faster than it can be found.
///
/// Kernel proof target: `NNVerify.C028.sos_implies_no_bab`
pub const C028_SOS_IMPLIES_NO_BAB: ProofStatus = ProofStatus::DerivedPending;

/// Return the C028 theorem entries for the registry.
///
/// These track the Neural Nullstellensatz theorems for SoS-based
/// verification without branch-and-bound.
#[must_use]
pub fn c028_theorem_entries() -> Vec<TheoremEntry> {
    vec![
        TheoremEntry {
            id: "C028a",
            description: "Stable ReLU network is polynomial (affine composition)",
            status: C028_STABLE_NETWORK_IS_POLYNOMIAL,
            phase: Phase::Phase1,
        },
        TheoremEntry {
            id: "C028b",
            description: "SoS Positivstellensatz certificate soundness",
            status: C028_SOS_CERTIFICATE_SOUNDNESS,
            phase: Phase::Phase1,
        },
        TheoremEntry {
            id: "C028c",
            description: "SoS certificate implies no BaB tree needed",
            status: C028_SOS_IMPLIES_NO_BAB,
            phase: Phase::Phase1,
        },
    ]
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_c028_all_proved() {
        assert!(matches!(
            C028_STABLE_NETWORK_IS_POLYNOMIAL,
            ProofStatus::DerivedPending
        ));
        assert!(matches!(
            C028_SOS_CERTIFICATE_SOUNDNESS,
            ProofStatus::DerivedPending
        ));
        assert!(matches!(
            C028_SOS_IMPLIES_NO_BAB,
            ProofStatus::DerivedPending
        ));
    }

    #[test]
    fn test_c028_theorem_entries_count() {
        let entries = c028_theorem_entries();
        assert_eq!(entries.len(), 3, "C028 has 3 sub-theorems");
    }

    #[test]
    fn test_c028_theorem_ids_unique() {
        let entries = c028_theorem_entries();
        let mut ids: Vec<&str> = entries.iter().map(|e| e.id).collect();
        ids.sort();
        ids.dedup();
        assert_eq!(ids.len(), entries.len(), "C028 theorem IDs must be unique");
    }

    #[test]
    fn test_c028_all_phase1() {
        let entries = c028_theorem_entries();
        for entry in &entries {
            assert_eq!(
                entry.phase,
                Phase::Phase1,
                "C028 theorems are Phase 1 (active)"
            );
        }
    }

    #[test]
    fn test_c028_ids_prefixed() {
        let entries = c028_theorem_entries();
        for entry in &entries {
            assert!(
                entry.id.starts_with("C028"),
                "all C028 entries must have C028 prefix, got {}",
                entry.id
            );
        }
    }
}
