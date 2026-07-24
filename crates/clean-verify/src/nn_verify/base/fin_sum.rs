// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Finite sum lemmas (T06, T07).
//!
//! All NN verification proofs depend on reasoning about finite sums.
//! This module provides the base lemmas that `linarith` needs.

use crate::spec::ProofStatus;

/// T06: fin_sum_nonneg
/// If f(i) >= 0 for all i, then sum(f) >= 0.
/// Proof: kernel axiom `Fin.sum_nonneg` registered in nn_verify_fin_sum.rs.
pub const T06_FIN_SUM_NONNEG: ProofStatus = ProofStatus::DerivedPending;

/// T07: fin_sum_le
/// If f(i) <= g(i) for all i, then sum(f) <= sum(g).
/// Proof: kernel axiom `Fin.sum_le` registered in nn_verify_fin_sum.rs.
pub const T07_FIN_SUM_LE: ProofStatus = ProofStatus::DerivedPending;

/// Finite sum over `Fin n` of a rational-valued function.
///
/// In the clean formalization, this maps to:
/// ```text
/// def Fin.sum (n : Nat) (f : Fin n -> Rat) : Rat :=
///   match n with
///   | 0 => 0
///   | n + 1 => f ⟨n, lt_succ⟩ + Fin.sum n (fun i => f ⟨i.val, lt_trans i.isLt (lt_succ)⟩)
/// ```
///
/// Properties proven in the spec layer (not executable Rust):
/// - `sum_zero`: `Fin.sum 0 f = 0`
/// - `sum_succ`: `Fin.sum (n+1) f = f n + Fin.sum n f`
/// - `sum_nonneg` (T06): `(∀ i, 0 ≤ f i) → 0 ≤ Fin.sum n f`
/// - `sum_le` (T07): `(∀ i, f i ≤ g i) → Fin.sum n f ≤ Fin.sum n g`
/// - `sum_add`: `Fin.sum n (f + g) = Fin.sum n f + Fin.sum n g`
/// - `sum_smul`: `Fin.sum n (c * f) = c * Fin.sum n f`
/// - `sum_const`: `Fin.sum n (fun _ => c) = n * c`
pub struct FinSumSpec;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_proof_status_tracking() {
        // Promoted to DerivedPending: kernel axioms registered in nn_verify_fin_sum.rs
        assert!(matches!(T06_FIN_SUM_NONNEG, ProofStatus::DerivedPending));
        assert!(matches!(T07_FIN_SUM_LE, ProofStatus::DerivedPending));
    }
}
