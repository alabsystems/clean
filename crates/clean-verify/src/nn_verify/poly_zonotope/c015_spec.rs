// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! C015 theorem specification: Polynomial zonotope attention verification
//! with O(eps) tightness for Vision Transformers.
//!
//! This module tracks the proof status of the C015 sub-theorems:
//!
//! - **C015a (`poly_zonotope_product_sound`)**: The polynomial zonotope
//!   Hadamard product overapproximation is sound. For noise symbols in
//!   [-1, 1], the true product value is contained in the result.
//!
//! - **C015b (`attention_bound_sound`)**: Polynomial zonotope attention
//!   bounds (q*k*v) are sound. For all perturbations within eps, the
//!   true attention value is in [lower, upper].
//!
//! - **C015c (`poly_o_eps_tightness`)**: The polynomial zonotope attention
//!   gap is O(eps). The bound gap scales linearly with the perturbation
//!   radius, not quadratically as with linear zonotopes.
//!
//! - **C015d (`linear_o_eps_squared`)**: The linear zonotope attention gap
//!   is O(eps^2). This confirms that dropping quadratic generators causes
//!   a strictly worse (quadratic) scaling in the bound gap.
//!
//! - **C015e (`poly_dominates_linear`)**: For all eps > 0, the polynomial
//!   zonotope gap is <= the linear zonotope gap. Polynomial zonotopes
//!   never lose information compared to linear zonotopes.
//!
//! ## References
//!
//! - Kochdumper & Althoff, "Sparse Polynomial Zonotopes" (2020)
//! - Bonaert et al., "Fast and Precise Certification of Transformers" (PLDI 2021)
//! - Shi et al., "Robustness Verification for Transformers" (ICLR 2020)

use crate::nn_verify::ibp_crown::{Phase, TheoremEntry};
use crate::spec::ProofStatus;

/// C015a: Polynomial zonotope Hadamard product soundness.
///
/// For polynomial zonotopes x, y sharing noise symbols eps_i in [-1, 1],
/// the Hadamard product `x.hadamard_product_scalar(y)` produces a
/// polynomial zonotope that contains the true product x*y for all valid
/// noise symbol assignments.
///
/// Proof sketch: The quadratic generators capture the eps_i*eps_j cross-terms
/// exactly. The cubic and quartic remainder terms are bounded by absolute-value
/// sums and added to the interval hull. Since |eps_i| <= 1, the bounds on
/// higher-order terms are conservative.
///
/// Status: DerivedPending (computational verification via sampling exists)
pub const C015_POLY_PRODUCT_SOUND: ProofStatus = ProofStatus::DerivedPending;

/// C015b: Polynomial zonotope attention bound soundness.
///
/// For the attention operation attn(q, k, v) = q * k * v where q, k, v
/// are polynomial zonotopes with perturbation radius eps, the computed
/// bounds [lower, upper] contain the true attention value for all
/// perturbations.
///
/// Proof: Follows from C015a applied twice (q*k, then (q*k)*v).
///
/// Status: DerivedPending (computational verification via grid sampling)
pub const C015_ATTENTION_BOUND_SOUND: ProofStatus = ProofStatus::DerivedPending;

/// C015c: Polynomial zonotope O(eps) tightness.
///
/// The gap `upper - lower` of the polynomial zonotope attention bound
/// is O(eps) as eps -> 0. Specifically:
///
/// ```text
/// gap_poly(eps) <= C_poly * eps
/// ```
///
/// for some constant C_poly depending on the nominal values q0, k0, v0.
///
/// Proof sketch: The polynomial zonotope tracks quadratic terms exactly.
/// The remaining overapproximation comes from:
/// 1. Cubic/quartic remainder in Hadamard product: O(eps^3)
/// 2. Interval hull extraction: O(eps) for the linear generators
///    The dominant contribution is (2), giving O(eps) total gap.
///
/// Status: DerivedPending (empirical log-log regression verification)
pub const C015_POLY_O_EPS_TIGHTNESS: ProofStatus = ProofStatus::DerivedPending;

/// C015d: Linear zonotope O(eps^2) gap.
///
/// The gap of the linear (interval-arithmetic) attention bound is O(eps^2):
///
/// ```text
/// gap_lin(eps) >= C_lin * eps^2
/// ```
///
/// Proof: The interval product of two O(eps)-wide intervals is O(eps^2)-wide.
/// The product q*k gives an interval of width O(eps^2), which then multiplied
/// by the O(eps)-wide interval for v gives O(eps^2) gap (dominated by q*k).
///
/// Status: DerivedPending (empirical log-log regression verification)
pub const C015_LINEAR_O_EPS_SQUARED: ProofStatus = ProofStatus::DerivedPending;

/// C015e: Polynomial zonotope dominance.
///
/// For all eps > 0, the polynomial zonotope attention gap is at most the
/// linear zonotope gap:
///
/// ```text
/// gap_poly(eps) <= gap_lin(eps)
/// ```
///
/// Proof: The polynomial zonotope retains all information that the linear
/// zonotope has (via the linear generators), plus additional quadratic
/// dependency information. The interval hull of a polynomial zonotope
/// is always at least as tight as the interval product of the marginal
/// intervals.
///
/// Status: DerivedPending (computational verification at sampled eps values)
pub const C015_POLY_DOMINATES_LINEAR: ProofStatus = ProofStatus::DerivedPending;

/// Return the C015 theorem entries for the registry.
///
/// These track the polynomial zonotope attention verification theorems
/// alongside the existing IBP/CROWN and softmax proof registries.
#[must_use]
pub fn c015_theorem_entries() -> Vec<TheoremEntry> {
    vec![
        TheoremEntry {
            id: "C015a",
            description: "Polynomial zonotope Hadamard product soundness",
            status: C015_POLY_PRODUCT_SOUND,
            phase: Phase::Phase3,
        },
        TheoremEntry {
            id: "C015b",
            description: "Polynomial zonotope attention bound soundness (q*k*v)",
            status: C015_ATTENTION_BOUND_SOUND,
            phase: Phase::Phase3,
        },
        TheoremEntry {
            id: "C015c",
            description: "Polynomial zonotope O(eps) tightness for attention",
            status: C015_POLY_O_EPS_TIGHTNESS,
            phase: Phase::Phase3,
        },
        TheoremEntry {
            id: "C015d",
            description: "Linear zonotope O(eps^2) gap for attention (baseline)",
            status: C015_LINEAR_O_EPS_SQUARED,
            phase: Phase::Phase3,
        },
        TheoremEntry {
            id: "C015e",
            description: "Polynomial zonotope dominates linear zonotope for attention",
            status: C015_POLY_DOMINATES_LINEAR,
            phase: Phase::Phase3,
        },
    ]
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_c015_all_pending() {
        assert!(matches!(
            C015_POLY_PRODUCT_SOUND,
            ProofStatus::DerivedPending
        ));
        assert!(matches!(
            C015_ATTENTION_BOUND_SOUND,
            ProofStatus::DerivedPending
        ));
        assert!(matches!(
            C015_POLY_O_EPS_TIGHTNESS,
            ProofStatus::DerivedPending
        ));
        assert!(matches!(
            C015_LINEAR_O_EPS_SQUARED,
            ProofStatus::DerivedPending
        ));
        assert!(matches!(
            C015_POLY_DOMINATES_LINEAR,
            ProofStatus::DerivedPending
        ));
    }

    #[test]
    fn test_c015_theorem_entries_count() {
        let entries = c015_theorem_entries();
        assert_eq!(entries.len(), 5, "C015 has 5 sub-theorems");
    }

    #[test]
    fn test_c015_theorem_ids_unique() {
        let entries = c015_theorem_entries();
        let mut ids: Vec<&str> = entries.iter().map(|e| e.id).collect();
        ids.sort();
        ids.dedup();
        assert_eq!(ids.len(), entries.len(), "C015 theorem IDs must be unique");
    }

    #[test]
    fn test_c015_all_phase3() {
        let entries = c015_theorem_entries();
        for entry in &entries {
            assert_eq!(
                entry.phase,
                Phase::Phase3,
                "C015 theorems are Phase 3 (polynomial zonotope attention)"
            );
        }
    }

    #[test]
    fn test_c015_ids_prefixed() {
        let entries = c015_theorem_entries();
        for entry in &entries {
            assert!(
                entry.id.starts_with("C015"),
                "all C015 entries must have C015 prefix, got {}",
                entry.id
            );
        }
    }
}
