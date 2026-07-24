// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! C030 theorem specification: Orbit-CROWN symmetry quotienting soundness.
//!
//! This module tracks the proof status of the three C030 sub-theorems:
//!
//! - **C030a (`equivariance_verification`)**: Given weight matrix W and group
//!   generators {g_1, ..., g_k}, verify that `||W * rho(g_i) - rho(g_i) * W||_F < eps`
//!   for all i. Suffices because generator commutativity implies full group
//!   commutativity.
//!
//! - **C030b (`orbit_crown_soundness`)**: If W is G-equivariant, then computing
//!   CROWN bounds only on orbit representatives and extending by symmetry
//!   produces sound bounds: `quotient_lower[i] <= f(x)[i] <= quotient_upper[i]`
//!   for all x in the input region and all i.
//!
//! - **C030c (`orbit_crown_tightness`)**: The orbit-quotiented bounds are at
//!   least as tight as full CROWN restricted to the fundamental domain, because
//!   averaging over the orbit exploits the equivariance constraint.
//!
//! All three are `DerivedPending` — the computational implementations exist but
//! kernel-level formal proofs have not been registered.

use crate::nn_verify::ibp_crown::{Phase, TheoremEntry};
use crate::spec::ProofStatus;

/// C030a: Equivariance verification via generators.
///
/// **Statement:** If `||W * rho(g_i) - rho(g_i) * W||_F < eps` for all
/// generators g_i of G, then `||W * rho(g) - rho(g) * W||_F < |g|_gen * eps`
/// for all g in G, where `|g|_gen` is the generator-word length of g.
///
/// **Proof sketch:** By induction on generator-word length. For a product
/// `g = g_a * g_b`, the commutator `[W, rho(g)]` decomposes via the
/// Leibniz-like rule: `[W, rho(g_a) * rho(g_b)] = [W, rho(g_a)] * rho(g_b)
/// + rho(g_a) * [W, rho(g_b)]`, and submultiplicativity of the Frobenius
///   norm gives the bound.
pub const C030_EQUIVARIANCE_VERIFICATION: ProofStatus = ProofStatus::DerivedPending;

/// C030b: Orbit-CROWN bound soundness.
///
/// **Statement:** Let W be G-equivariant (exact: `W * rho(g) = rho(g) * W`).
/// Let `[l_r, u_r]` be the IBP/CROWN bound at orbit representative r.
/// Then for every index i in the orbit of r, the true output satisfies
/// `l_r <= f(x)[i] <= u_r` for all x in the input interval.
///
/// **Proof sketch:** By equivariance, `f(x)[g.r] = (g.f(x))[g.r] = f(x)[r]`
/// when G acts trivially on the output (invariant case). More generally,
/// for equivariant (not invariant) outputs, the bound at `g.r` equals the
/// group-rotated bound at r, which has the same interval since the input
/// region is G-invariant.
pub const C030_ORBIT_CROWN_SOUNDNESS: ProofStatus = ProofStatus::DerivedPending;

/// C030c: Orbit-CROWN tightness relative to full CROWN.
///
/// **Statement:** The orbit-averaged CROWN bounds are at least as tight as
/// full CROWN restricted to orbit representatives. Specifically, for any
/// representative r:
///   `orbit_lower[r] >= crown_lower[r]` and `orbit_upper[r] <= crown_upper[r]`
/// when the orbit-averaging exploits equivariance constraints.
///
/// **Proof sketch:** Averaging coefficient matrices within an orbit projects
/// onto the G-invariant subspace. By Jensen's inequality applied to the
/// concretization, the averaged bound is at least as tight as any single
/// orbit member's bound.
pub const C030_ORBIT_CROWN_TIGHTNESS: ProofStatus = ProofStatus::DerivedPending;

/// Return the C030 theorem entries for the registry.
#[must_use]
pub fn c030_theorem_entries() -> Vec<TheoremEntry> {
    vec![
        TheoremEntry {
            id: "C030a",
            description: "Equivariance verification via generator commutativity",
            status: C030_EQUIVARIANCE_VERIFICATION,
            phase: Phase::Phase3,
        },
        TheoremEntry {
            id: "C030b",
            description: "Orbit-CROWN soundness (quotient bounds contain true output)",
            status: C030_ORBIT_CROWN_SOUNDNESS,
            phase: Phase::Phase3,
        },
        TheoremEntry {
            id: "C030c",
            description: "Orbit-CROWN tightness (quotient >= full CROWN on fundamental domain)",
            status: C030_ORBIT_CROWN_TIGHTNESS,
            phase: Phase::Phase3,
        },
    ]
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_c030_all_pending() {
        assert!(matches!(
            C030_EQUIVARIANCE_VERIFICATION,
            ProofStatus::DerivedPending
        ));
        assert!(matches!(
            C030_ORBIT_CROWN_SOUNDNESS,
            ProofStatus::DerivedPending
        ));
        assert!(matches!(
            C030_ORBIT_CROWN_TIGHTNESS,
            ProofStatus::DerivedPending
        ));
    }

    #[test]
    fn test_c030_theorem_entries_count() {
        let entries = c030_theorem_entries();
        assert_eq!(entries.len(), 3, "C030 has 3 sub-theorems");
    }

    #[test]
    fn test_c030_theorem_ids_unique() {
        let entries = c030_theorem_entries();
        let mut ids: Vec<&str> = entries.iter().map(|e| e.id).collect();
        ids.sort();
        ids.dedup();
        assert_eq!(ids.len(), entries.len(), "C030 theorem IDs must be unique");
    }

    #[test]
    fn test_c030_all_phase3() {
        let entries = c030_theorem_entries();
        for entry in &entries {
            assert_eq!(
                entry.phase,
                Phase::Phase3,
                "C030 theorems are Phase 3 (pending formal proof)"
            );
        }
    }
}
