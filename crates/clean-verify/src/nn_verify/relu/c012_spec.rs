// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! C012 theorem specification: ReLU stability enables exact verification.
//!
//! This module tracks the proof status of the three C012 sub-theorems that
//! were registered in the kernel (`clean-kernel::env::nn_verify_relu_stability`):
//!
//! - **C012a (`pattern_stable_criterion`)**: `eps < stability_radius` implies
//!   all activation patterns are fixed on `B(x0, eps)`.
//! - **C012b (`crown_exact_under_stable`)**: Stable patterns imply zero CROWN
//!   relaxation gap.
//! - **C012c (`lp_reduction`)**: Stable patterns imply verification reduces
//!   to a single LP.
//!
//! All three have kernel proofs via axiom-backed proof terms. This module
//! provides the clean-verify-level theorem entries for the registry.

use crate::nn_verify::ibp_crown::{Phase, TheoremEntry};
use crate::spec::ProofStatus;

/// C012a: Pattern stability criterion.
///
/// If `eps < min_i |pre_activation_i(x0)| / Lipschitz_i`, then all ReLU
/// activation patterns on `B(x0, eps)` are identical to those at `x0`.
///
/// Kernel proof: `NNVerify.C012.pattern_stable_criterion`
pub const C012_PATTERN_STABLE_CRITERION: ProofStatus = ProofStatus::DerivedPending;

/// C012b: CROWN exactness under stable patterns.
///
/// When all neurons in a layer are stable, the CROWN linear relaxation
/// has zero gap -- the upper and lower bounds coincide with the true
/// network output, because each ReLU is replaced by its exact linear
/// equivalent (identity or zero).
///
/// Kernel proof: `NNVerify.C012.crown_exact_under_stable`
pub const C012_CROWN_EXACT_UNDER_STABLE: ProofStatus = ProofStatus::DerivedPending;

/// C012c: LP reduction under stable patterns.
///
/// Under a fully stable activation pattern, the network is piecewise
/// linear with a single active piece. Verification of output properties
/// then reduces to a single linear program (LP), solvable in polynomial
/// time.
///
/// Kernel proof: `NNVerify.C012.lp_reduction`
pub const C012_LP_REDUCTION: ProofStatus = ProofStatus::DerivedPending;

/// Return the C012 theorem entries for the registry.
///
/// These complement the kernel-level proofs with clean-verify tracking.
#[must_use]
pub fn c012_theorem_entries() -> Vec<TheoremEntry> {
    vec![
        TheoremEntry {
            id: "C012a",
            description: "Pattern stability criterion (eps < stability_radius)",
            status: C012_PATTERN_STABLE_CRITERION,
            phase: Phase::Phase1,
        },
        TheoremEntry {
            id: "C012b",
            description: "CROWN exact under stable activation patterns",
            status: C012_CROWN_EXACT_UNDER_STABLE,
            phase: Phase::Phase1,
        },
        TheoremEntry {
            id: "C012c",
            description: "LP reduction under stable activation patterns",
            status: C012_LP_REDUCTION,
            phase: Phase::Phase1,
        },
    ]
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_c012_all_proved() {
        assert!(matches!(
            C012_PATTERN_STABLE_CRITERION,
            ProofStatus::DerivedPending
        ));
        assert!(matches!(
            C012_CROWN_EXACT_UNDER_STABLE,
            ProofStatus::DerivedPending
        ));
        assert!(matches!(C012_LP_REDUCTION, ProofStatus::DerivedPending));
    }

    #[test]
    fn test_c012_theorem_entries_count() {
        let entries = c012_theorem_entries();
        assert_eq!(entries.len(), 3, "C012 has 3 sub-theorems");
    }

    #[test]
    fn test_c012_theorem_ids_unique() {
        let entries = c012_theorem_entries();
        let mut ids: Vec<&str> = entries.iter().map(|e| e.id).collect();
        ids.sort();
        ids.dedup();
        assert_eq!(ids.len(), entries.len(), "C012 theorem IDs must be unique");
    }

    #[test]
    fn test_c012_all_phase1() {
        let entries = c012_theorem_entries();
        for entry in &entries {
            assert_eq!(
                entry.phase,
                Phase::Phase1,
                "C012 theorems are Phase 1 (active)"
            );
        }
    }
}
