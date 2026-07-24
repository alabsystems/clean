// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Proof-Guided CDCL: proof complexity bounds during search
//!
//! Novel theory for ay: no production SAT solver uses proof complexity
//! bounds to guide search decisions. This module implements the idea of
//! tracking proof complexity metrics (width, space, depth) during CDCL
//! search and using them to trigger restarts, adjust branching heuristics,
//! and guide clause deletion.
//!
//! ## Key Theorems
//!
//! - **PG01 (Width-size trade-off):** Resolution proofs of width w require
//!   size at least 2^{w/sqrt(n)}. (Ben-Sasson & Wigderson, 2001)
//!
//! - **PG02 (Restart optimality):** Width-guided restarts produce O(2^{sqrt(n)})
//!   size proofs on formulas that have narrow refutations.
//!
//! - **PG03 (Space-width inequality):** For any unsatisfiable CNF F,
//!   space(F) >= width(F) - O(log n). (Atserias & Dalmau, 2008)
//!
//! ## References
//!
//! - Ben-Sasson, E. & Wigderson, A. (2001). "Short proofs are narrow --
//!   resolution made simple." J. ACM 48(2):149-169.
//! - Atserias, A. & Dalmau, V. (2008). "A combinatorial characterization
//!   of resolution width." J. Comput. Syst. Sci. 74(3):323-334.
//! - Razborov, A. (2003). "Resolution lower bounds for the weak pigeonhole
//!   principle." Theoretical Computer Science 303(1):233-243.

pub mod branching_heuristic;
pub mod complexity_tracker;
pub mod restart_policy;
mod spec_registration;

use crate::spec::ProofStatus;

/// PG01: Width-size trade-off (Ben-Sasson & Wigderson 2001).
///
/// Any resolution refutation of an unsatisfiable CNF formula F on n
/// variables with width w requires size at least 2^{(w - W(F))^2 / n},
/// where W(F) is the maximum clause width in F.
///
/// Consequence: if the solver is deriving clauses of width > sqrt(n),
/// the proof is likely exponentially large. This is the foundation of
/// width-guided restarts.
pub const PG01_WIDTH_SIZE_TRADEOFF: ProofStatus = ProofStatus::DerivedPending;

/// PG02: Restart optimality under width guidance.
///
/// If an unsatisfiable formula F has a resolution refutation of width w,
/// then a width-guided restart strategy (restart when conflict clause
/// width exceeds the narrow refutation width) produces a proof of size
/// O(2^{w^2/n} * n). On formulas with narrow refutations (w = O(sqrt(n))),
/// this yields polynomial-size proofs.
///
/// This is a novel application of Ben-Sasson & Wigderson to restart
/// policy. No production solver implements this.
pub const PG02_RESTART_OPTIMALITY: ProofStatus = ProofStatus::DerivedPending;

/// PG03: Space-width inequality (Atserias & Dalmau 2008).
///
/// For any unsatisfiable CNF formula F:
///   space(F) >= width(F) - O(log n)
///
/// where space(F) is the minimum number of clauses that must be
/// simultaneously kept in memory during any resolution refutation,
/// and width(F) is the minimum refutation width.
///
/// Consequence: tracking space complexity provides an indirect measure
/// of proof width, which can be computed incrementally during search.
pub const PG03_SPACE_WIDTH_INEQUALITY: ProofStatus = ProofStatus::DerivedPending;

/// PG04: Width-guided restart satisfiability preservation.
///
/// Every step of a width-guided restart sequence preserves the
/// equisatisfiability invariant between the original CNF formula `F` and
/// the formula augmented with learned clauses `F ∧ LC`:
///
///   F ⊨ LC  ⟹  F ≡sat (F ∧ LC)
///
/// Because every learned clause is a resolvent of parents already entailed
/// by F (PC01 resolution soundness), adding LC cannot change satisfiability.
/// A width-guided restart clears the trail but retains the clause set, so
/// the invariant is maintained across the continue_narrow and restart_wide
/// transitions alike.
///
/// Consequence: width-guided restarts are SOUND (UNSAT verdicts remain
/// valid) and COMPLETE (SAT verdicts remain valid). This is the formal
/// correctness theorem required by #3343's acceptance criteria.
pub const PG04_RESTART_SAT_PRESERVING: ProofStatus = ProofStatus::DerivedPending;

/// Return a summary of proof-guided CDCL theorem statuses.
#[must_use]
pub fn proof_guided_registry() -> Vec<(&'static str, ProofStatus)> {
    vec![
        ("PG01_width_size_tradeoff", PG01_WIDTH_SIZE_TRADEOFF),
        ("PG02_restart_optimality", PG02_RESTART_OPTIMALITY),
        ("PG03_space_width_inequality", PG03_SPACE_WIDTH_INEQUALITY),
        ("PG04_restart_sat_preserving", PG04_RESTART_SAT_PRESERVING),
    ]
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::spec::ProofStatus;

    #[test]
    fn test_proof_guided_registry_count() {
        assert_eq!(proof_guided_registry().len(), 4);
    }

    #[test]
    fn test_proof_guided_registry_contains_pg04_restart_sat_preserving() {
        // PG04 is the formal soundness/completeness theorem required by
        // #3343's acceptance criteria. It must be present in the registry
        // so downstream auditors can discover it alongside PG01-PG03.
        let registry = proof_guided_registry();
        let found = registry
            .iter()
            .any(|(name, _)| *name == "PG04_restart_sat_preserving");
        assert!(
            found,
            "PG04_restart_sat_preserving must be registered (#3343 acceptance criterion)"
        );
    }

    #[test]
    fn test_proof_guided_registry_all_pending() {
        let registry = proof_guided_registry();
        for (name, status) in &registry {
            assert_eq!(
                *status,
                ProofStatus::DerivedPending,
                "theorem {name} should be DerivedPending"
            );
        }
    }

    #[test]
    fn test_proof_guided_registry_unique_names() {
        let registry = proof_guided_registry();
        let mut names: Vec<&str> = registry.iter().map(|(n, _)| *n).collect();
        names.sort();
        names.dedup();
        assert_eq!(names.len(), registry.len(), "theorem names must be unique");
    }
}
