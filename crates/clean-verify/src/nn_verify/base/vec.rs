// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Vector type over rationals (T05).
//!
//! `Vec n` is formalized as `Fin n -> Rat` in the clean spec layer.
//! This module defines the Rust-side specification and proof status tracking.

use crate::spec::ProofStatus;

/// T05: vec_l1_triangle
/// ‖u + v‖₁ ≤ ‖u‖₁ + ‖v‖₁
/// Proof: positivity + Fin.sum linearity + |a + b| <= |a| + |b| per component.
pub const T05_VEC_L1_TRIANGLE: ProofStatus = ProofStatus::DerivedPending;

/// Vector type specification.
///
/// In the clean formalization:
/// ```text
/// def Vec (n : Nat) := Fin n -> Rat
///
/// def Vec.add (u v : Vec n) : Vec n := fun i => u i + v i
/// def Vec.smul (c : Rat) (v : Vec n) : Vec n := fun i => c * v i
/// def Vec.dot (u v : Vec n) : Rat := Fin.sum (fun i => u i * v i)
/// def Vec.l1_norm (v : Vec n) : Rat := Fin.sum (fun i => |v i|)
/// ```
pub struct Vec;

/// Matrix type specification.
///
/// In the clean formalization:
/// ```text
/// def Mat (m n : Nat) := Fin m -> Fin n -> Rat
///
/// def Mat.mulVec (A : Mat m n) (v : Vec n) : Vec m :=
///   fun i => Fin.sum (fun j => A i j * v j)
///
/// -- W+ / W- decomposition for IBP
/// def Mat.pos (A : Mat m n) : Mat m n := fun i j => max 0 (A i j)
/// def Mat.neg (A : Mat m n) : Mat m n := fun i j => min 0 (A i j)
/// -- Property: A = A.pos + A.neg
/// ```
pub struct Mat;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_proof_status_tracking() {
        assert!(matches!(T05_VEC_L1_TRIANGLE, ProofStatus::DerivedPending));
    }
}
