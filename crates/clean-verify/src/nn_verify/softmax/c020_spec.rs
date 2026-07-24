// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! C020 theorem specification: Softmax convex relaxation with O(range) tightness.
//!
//! This module tracks the proof status of the C020 sub-theorems for softmax
//! convex relaxation via LSE decomposition:
//!
//! - **C020a (`lse_convexity`)**: LSE(x) = log(sum exp(x_j)) is convex.
//!   Proof sketch: Hessian = diag(softmax) - softmax * softmax^T is PSD.
//!
//! - **C020b (`softmax_bound_soundness`)**: Interval-arithmetic softmax bounds
//!   are sound. For x in [l, u]:
//!   `exp(l_i) / (exp(l_i) + sum_{j!=i} exp(u_j)) <= softmax(x)_i`
//!   `softmax(x)_i <= exp(u_i) / (exp(u_i) + sum_{j!=i} exp(l_j))`
//!
//! - **C020c (`o_range_tightness`)**: The bound gap is O(range) where
//!   range = max(u) - min(l). When range -> 0, the gap -> 0, confirming
//!   the relaxation tightens as the input interval shrinks.
//!
//! - **C020d (`lse_squeeze`)**: max(x) <= LSE(x) <= max(x) + ln(n).
//!   This bounds LSE between the max function and max + log(dim).
//!
//! ## References
//!
//! - Boyd & Vandenberghe, "Convex Optimization" (2004), Section 3.1.5
//! - Shi et al., "Robustness Verification for Transformers" (ICLR 2020)

use crate::nn_verify::ibp_crown::{Phase, TheoremEntry};
use crate::spec::ProofStatus;

/// C020a: LSE convexity.
///
/// The log-sum-exp function `LSE(x) = log(sum_j exp(x_j))` is convex.
/// This follows from the Hessian being positive semidefinite:
/// `H = diag(softmax(x)) - softmax(x) * softmax(x)^T`
/// which is a rank-1 perturbation of a diagonal matrix, and is PSD
/// because `v^T H v = E[v^2] - E[v]^2 = Var(v) >= 0` where the
/// expectation is under the softmax distribution.
///
/// Status: DerivedPending (computational verification exists, formal proof planned)
pub const C020_LSE_CONVEXITY: ProofStatus = ProofStatus::DerivedPending;

/// C020b: Softmax bound soundness.
///
/// The interval-arithmetic bounds on softmax are sound:
/// for all x in [l, u], the computed lower and upper bounds contain
/// the true softmax output.
///
/// Proof: Follows from monotonicity of exp and the standard interval
/// arithmetic rule for a/b where a is increasing and b is decreasing
/// in the quantity of interest.
///
/// Status: DerivedPending (computational verification exists, formal proof planned)
pub const C020_SOFTMAX_BOUND_SOUNDNESS: ProofStatus = ProofStatus::DerivedPending;

/// C020c: O(range) tightness.
///
/// The gap between upper and lower softmax bounds is O(range) where
/// range = max(u) - min(l). This means:
/// - As the input box shrinks (range -> 0), bounds become exact
/// - The relaxation quality degrades gracefully with input uncertainty
/// - For typical transformer inputs with bounded range, bounds are practical
///
/// Proof sketch: When range = 0, all x_i are equal, softmax = 1/n,
/// and bounds are exact. Taylor expansion around the uniform case
/// shows the gap grows linearly with range to first order.
///
/// Status: DerivedPending (empirical verification exists, formal proof planned)
pub const C020_O_RANGE_TIGHTNESS: ProofStatus = ProofStatus::DerivedPending;

/// C020d: LSE squeeze property.
///
/// For all x in R^n: `max(x) <= LSE(x) <= max(x) + ln(n)`
///
/// The lower bound follows from `exp(max(x)) <= sum exp(x_j)`.
/// The upper bound follows from `sum exp(x_j) <= n * exp(max(x))`.
///
/// Status: DerivedPending (computational verification exists, formal proof planned)
pub const C020_LSE_SQUEEZE: ProofStatus = ProofStatus::DerivedPending;

/// Return the C020 theorem entries for the registry.
///
/// These track the softmax convex relaxation theorems alongside
/// the existing IBP/CROWN proof registry.
#[must_use]
pub fn c020_theorem_entries() -> Vec<TheoremEntry> {
    vec![
        TheoremEntry {
            id: "C020a",
            description: "LSE convexity (Hessian PSD via softmax variance)",
            status: C020_LSE_CONVEXITY,
            phase: Phase::Phase3,
        },
        TheoremEntry {
            id: "C020b",
            description: "Softmax interval-arithmetic bound soundness",
            status: C020_SOFTMAX_BOUND_SOUNDNESS,
            phase: Phase::Phase3,
        },
        TheoremEntry {
            id: "C020c",
            description: "Softmax O(range) tightness guarantee",
            status: C020_O_RANGE_TIGHTNESS,
            phase: Phase::Phase3,
        },
        TheoremEntry {
            id: "C020d",
            description: "LSE squeeze: max(x) <= LSE(x) <= max(x) + ln(n)",
            status: C020_LSE_SQUEEZE,
            phase: Phase::Phase3,
        },
    ]
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_c020_all_pending() {
        assert!(matches!(C020_LSE_CONVEXITY, ProofStatus::DerivedPending));
        assert!(matches!(
            C020_SOFTMAX_BOUND_SOUNDNESS,
            ProofStatus::DerivedPending
        ));
        assert!(matches!(
            C020_O_RANGE_TIGHTNESS,
            ProofStatus::DerivedPending
        ));
        assert!(matches!(C020_LSE_SQUEEZE, ProofStatus::DerivedPending));
    }

    #[test]
    fn test_c020_theorem_entries_count() {
        let entries = c020_theorem_entries();
        assert_eq!(entries.len(), 4, "C020 has 4 sub-theorems");
    }

    #[test]
    fn test_c020_theorem_ids_unique() {
        let entries = c020_theorem_entries();
        let mut ids: Vec<&str> = entries.iter().map(|e| e.id).collect();
        ids.sort();
        ids.dedup();
        assert_eq!(ids.len(), entries.len(), "C020 theorem IDs must be unique");
    }

    #[test]
    fn test_c020_all_phase3() {
        let entries = c020_theorem_entries();
        for entry in &entries {
            assert_eq!(
                entry.phase,
                Phase::Phase3,
                "C020 theorems are Phase 3 (softmax relaxation)"
            );
        }
    }

    #[test]
    fn test_c020_ids_prefixed() {
        let entries = c020_theorem_entries();
        for entry in &entries {
            assert!(
                entry.id.starts_with("C020"),
                "all C020 entries must have C020 prefix, got {}",
                entry.id
            );
        }
    }
}
