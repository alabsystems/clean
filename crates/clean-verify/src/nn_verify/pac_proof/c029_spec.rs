// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! C029 theorem specification: PAC-to-Proof for PGD adversarial certification.
//!
//! Three sub-theorems tracking the proof status of PAC-to-Proof certification:
//!
//! - **C029a (`lipschitz_certified_radius`)**: First-order certification radius
//!   r = (f(x_adv) - t) / L guarantees no better adversarial in B(x_adv, r).
//!
//! - **C029b (`hessian_quadratic_refinement`)**: Second-order Hessian refinement
//!   gives a tighter radius via the quadratic formula when gradient information
//!   is available.
//!
//! - **C029c (`region_verification_sound`)**: The certified region B(x_adv, r)
//!   soundly overapproximates the set of inputs where f(x) >= threshold.

use crate::nn_verify::ibp_crown::{Phase, TheoremEntry};
use crate::spec::ProofStatus;

/// C029a: Lipschitz certified radius.
///
/// For a network f with Lipschitz constant L, if f(x_adv) > threshold, then
/// for all x in B(x_adv, r) where r = (f(x_adv) - threshold) / L:
///   f(x) >= f(x_adv) - L * ||x - x_adv|| >= f(x_adv) - L * r = threshold
///
/// This means no point in B(x_adv, r) can have output below threshold,
/// certifying that x_adv is locally optimal within this ball.
pub const C029_LIPSCHITZ_CERTIFIED_RADIUS: ProofStatus = ProofStatus::DerivedPending;

/// C029b: Hessian quadratic refinement.
///
/// When a Hessian bound H is available (||nabla^2 f|| <= H), Taylor's theorem
/// gives a tighter lower bound on f(x) near x_adv:
///   f(x) >= f(x_adv) - ||grad f(x_adv)|| * r - (H/2) * r^2
///
/// Solving for f(x) >= threshold yields:
///   r = (-||grad|| + sqrt(||grad||^2 + 2*H*(f(x_adv) - threshold))) / H
///
/// This radius is tighter than the first-order bound when the gradient
/// at x_adv is small (i.e., x_adv is near a local extremum of f).
pub const C029_HESSIAN_QUADRATIC_REFINEMENT: ProofStatus = ProofStatus::DerivedPending;

/// C029c: Region verification soundness.
///
/// The certified region B(x_adv, r) is a sound overapproximation:
///   - If r was computed via first-order: uses only Lipschitz continuity (T30/T32).
///   - If r was computed via second-order: uses Lipschitz + Hessian bound.
///   - The max(first_order_r, second_order_r) strategy is sound because
///     each radius independently guarantees f(x) >= threshold in its ball,
///     and the union of two sound regions is sound.
pub const C029_REGION_VERIFICATION_SOUND: ProofStatus = ProofStatus::DerivedPending;

/// Return the C029 theorem entries for the registry.
///
/// These integrate into the NN verification theorem registry alongside
/// IBP/CROWN, ReLU stability, and softmax relaxation theorems.
#[must_use]
pub fn c029_theorem_entries() -> Vec<TheoremEntry> {
    vec![
        TheoremEntry {
            id: "C029a",
            description: "Lipschitz certified radius for PGD adversarial",
            status: C029_LIPSCHITZ_CERTIFIED_RADIUS,
            phase: Phase::Phase3,
        },
        TheoremEntry {
            id: "C029b",
            description: "Hessian quadratic refinement of certified radius",
            status: C029_HESSIAN_QUADRATIC_REFINEMENT,
            phase: Phase::Phase3,
        },
        TheoremEntry {
            id: "C029c",
            description: "Certified region verification soundness",
            status: C029_REGION_VERIFICATION_SOUND,
            phase: Phase::Phase3,
        },
    ]
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_c029_all_pending() {
        assert!(matches!(
            C029_LIPSCHITZ_CERTIFIED_RADIUS,
            ProofStatus::DerivedPending
        ));
        assert!(matches!(
            C029_HESSIAN_QUADRATIC_REFINEMENT,
            ProofStatus::DerivedPending
        ));
        assert!(matches!(
            C029_REGION_VERIFICATION_SOUND,
            ProofStatus::DerivedPending
        ));
    }

    #[test]
    fn test_c029_theorem_entries_count() {
        let entries = c029_theorem_entries();
        assert_eq!(entries.len(), 3, "C029 has 3 sub-theorems");
    }

    #[test]
    fn test_c029_theorem_ids_unique() {
        let entries = c029_theorem_entries();
        let mut ids: Vec<&str> = entries.iter().map(|e| e.id).collect();
        ids.sort();
        ids.dedup();
        assert_eq!(ids.len(), entries.len(), "C029 theorem IDs must be unique");
    }

    #[test]
    fn test_c029_all_phase3() {
        let entries = c029_theorem_entries();
        for entry in &entries {
            assert_eq!(
                entry.phase,
                Phase::Phase3,
                "C029 theorems are Phase 3 (pending kernel proofs)"
            );
        }
    }
}
