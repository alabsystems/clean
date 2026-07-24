// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Zonotope type and core theorems (T01-T08).
//!
//! A zonotope is a center vector plus n generator vectors in d dimensions.
//! Points in the zonotope are { center + sum_i eps_i * gen_i | eps_i in [-1,1] }.
//!
//! T03-T07 cover ReLU overapproximation via lambda-relaxation and
//! affine+ReLU composition for neural network forward-pass analysis.

pub mod affine_relu;
pub(crate) mod c010_equiv;
pub mod compress;
pub mod concrete;
pub mod minkowski;
pub(crate) mod order_reduction;
pub mod proofs;
pub mod relu;
pub(crate) mod spec_registration;
#[cfg(test)]
mod tests_affine_relu;
#[cfg(test)]
mod tests_c010_equiv;
#[cfg(test)]
mod tests_composition_proptest;
#[cfg(test)]
mod tests_compress;
#[cfg(test)]
mod tests_concrete;
#[cfg(test)]
mod tests_minkowski;
#[cfg(test)]
mod tests_order_reduction;
#[cfg(test)]
mod tests_proofs;
#[cfg(test)]
mod tests_proptest;
#[cfg(test)]
mod tests_relu;
#[cfg(test)]
mod tests_verify;
#[cfg(test)]
mod tests_zonotope_kernel;
pub mod verify;

use crate::spec::ProofStatus;

pub use affine_relu::{compare_zonotope_ibp, zonotope_affine_relu, zonotope_forward_pass};
pub use concrete::{ConcreteZonotope, ZonotopeError};
pub use proofs::{proof_statuses, ProofWitness};
pub use relu::{verify_relu_soundness, verify_relu_tightness, zonotope_relu};
pub use verify::{
    verify_compress_hull_exact as verify_compress_hull_exact_sampling, verify_hull_soundness,
    verify_linear_transform, verify_minkowski_sum,
};

/// T01: interval_hull_sound
/// Z.contains x -> Z.to_interval.contains x
/// Proof: For each dimension j, |sum eps_i * g_ij| <= sum |g_ij| by triangle inequality.
/// See [`proofs::verify_t01_hull_soundness`] for constructive witness.
pub const T01_INTERVAL_HULL_SOUND: ProofStatus = ProofStatus::DerivedPending;

/// T02: linear_transform_exact
/// Z.contains x -> (W*Z+b).contains (W*x+b)
/// Proof: Same coefficients eps_i in [-1,1] work in the transformed zonotope.
/// See [`proofs::verify_t02_linear_transform`] for constructive witness.
pub const T02_LINEAR_TRANSFORM_EXACT: ProofStatus = ProofStatus::DerivedPending;

/// T03: relu_overapprox_sound
/// For x in Z, max(0, x) in relu(Z) where relu(Z) uses lambda-relaxation
/// on crossing dimensions.
/// See [`proofs::verify_t03_relu_soundness`] for constructive witness.
pub const T03_RELU_OVERAPPROX_SOUND: ProofStatus = ProofStatus::DerivedPending;

/// T04: relu_lambda_relaxation_tight
/// The lambda-relaxation is the tightest parallelotope overapproximation
/// of ReLU on a crossing interval [l, u] with l < 0 < u.
/// See [`proofs::verify_t04_lambda_tightness`] for constructive witness.
pub const T04_RELU_LAMBDA_RELAXATION_TIGHT: ProofStatus = ProofStatus::DerivedPending;

/// T05: relu_always_active_exact
/// For all-positive intervals [l, u] with l >= 0, ReLU is identity:
/// relu(Z) = Z (no overestimation, no new generators).
/// See [`proofs::verify_t05_always_active`] for constructive witness.
pub const T05_RELU_ALWAYS_ACTIVE_EXACT: ProofStatus = ProofStatus::DerivedPending;

/// T06: relu_always_inactive_exact
/// For all-negative intervals [l, u] with u <= 0, ReLU outputs zero:
/// relu(Z) is the origin (no overestimation).
/// See [`proofs::verify_t06_always_inactive`] for constructive witness.
pub const T06_RELU_ALWAYS_INACTIVE_EXACT: ProofStatus = ProofStatus::DerivedPending;

/// T07: affine_relu_composition_sound
/// If affine transform is exact (T02) and ReLU is sound (T03), then
/// their composition (affine then ReLU) is a sound overapproximation.
/// See [`proofs::verify_t07_affine_relu_composition`] for constructive witness.
pub const T07_AFFINE_RELU_COMPOSITION_SOUND: ProofStatus = ProofStatus::DerivedPending;

/// T08: zonotope_minkowski_sum_sound
/// x1 in Z1, x2 in Z2 => x1 + x2 in Z1 + Z2
/// Proof: Concatenate the coefficient vectors.
/// See [`proofs::verify_t08_minkowski_sum`] for constructive witness.
pub const T08_MINKOWSKI_SUM_SOUND: ProofStatus = ProofStatus::DerivedPending;

/// Zonotope specification in Lean 4 syntax.
pub struct ZonotopeSpec;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_proof_status_tracking() {
        assert!(matches!(
            T01_INTERVAL_HULL_SOUND,
            ProofStatus::DerivedPending
        ));
        assert!(matches!(
            T02_LINEAR_TRANSFORM_EXACT,
            ProofStatus::DerivedPending
        ));
        assert!(matches!(
            T03_RELU_OVERAPPROX_SOUND,
            ProofStatus::DerivedPending
        ));
        assert!(matches!(
            T04_RELU_LAMBDA_RELAXATION_TIGHT,
            ProofStatus::DerivedPending
        ));
        assert!(matches!(
            T05_RELU_ALWAYS_ACTIVE_EXACT,
            ProofStatus::DerivedPending
        ));
        assert!(matches!(
            T06_RELU_ALWAYS_INACTIVE_EXACT,
            ProofStatus::DerivedPending
        ));
        assert!(matches!(
            T07_AFFINE_RELU_COMPOSITION_SOUND,
            ProofStatus::DerivedPending
        ));
        assert!(matches!(
            T08_MINKOWSKI_SUM_SOUND,
            ProofStatus::DerivedPending
        ));
    }

    #[test]
    fn test_all_proof_statuses() {
        let statuses = proof_statuses();
        assert_eq!(statuses.len(), 8);
        let proved = statuses
            .iter()
            .filter(|(_, _, s)| matches!(s, ProofStatus::DerivedPending))
            .count();
        assert_eq!(
            proved, 8,
            "all 8 zonotope theorems should be DerivedPending"
        );
    }
}
