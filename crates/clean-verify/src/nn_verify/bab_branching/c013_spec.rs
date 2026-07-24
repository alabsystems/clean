// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! C013 theorem specification: optimal BaB branching via proof complexity.
//!
//! This module tracks the proof status of the three C013 sub-theorems:
//!
//! - **C013a (`balanced_split_optimality`)**: Branching on the neuron that
//!   maximizes `min(complexity_left, complexity_right)` minimizes worst-case
//!   BaB tree size.
//! - **C013b (`complexity_monotonicity`)**: Fixing any neuron (either active
//!   or inactive) does not increase the proof complexity lower bound of the
//!   remaining subproblem.
//! - **C013c (`tree_size_bound`)**: The total BaB tree size under optimal
//!   branching is bounded by `O(C * log C)` where C is the initial proof
//!   complexity lower bound.

use crate::nn_verify::ibp_crown::{Phase, TheoremEntry};
use crate::spec::ProofStatus;

/// C013a: Balanced split optimality.
///
/// The proof-complexity-balanced branching heuristic selects the neuron
/// maximizing `min(complexity(F_active), complexity(F_inactive))`. This
/// minimizes the worst-case BaB tree size because it prevents the adversary
/// from exploiting an easy branch.
///
/// Proof sketch: By the minimax theorem on game trees, the value of the
/// search tree is determined by the minimum-complexity branch at each node.
/// Maximizing this minimum at every step yields the optimal strategy.
pub const C013_BALANCED_SPLIT_OPTIMALITY: ProofStatus = ProofStatus::DerivedPending;

/// C013b: Complexity monotonicity under neuron fixing.
///
/// For any unfixed neuron in a BaB subproblem, forcing it active or inactive
/// produces a subproblem whose proof complexity lower bound is at most the
/// complexity of the original problem. This ensures the BaB tree terminates.
///
/// Proof sketch: Fixing a variable in a CNF formula can only reduce the
/// minimum refutation width (Ben-Sasson & Wigderson), and width lower bounds
/// imply size lower bounds. Since the NN verification encoding maps neuron
/// fixing to variable restriction, monotonicity follows.
pub const C013_COMPLEXITY_MONOTONICITY: ProofStatus = ProofStatus::DerivedPending;

/// C013c: Tree size bound under optimal branching.
///
/// Under the balanced complexity heuristic, the total BaB tree has at most
/// `O(C * log C)` nodes, where C is the proof complexity lower bound of the
/// root problem. This provides a worst-case guarantee on verification time.
///
/// Proof sketch: Each balanced split reduces the minimum branch complexity
/// by a constant factor (at least halving the number of unfixed neurons on
/// the harder branch). The tree depth is therefore O(log n) where n is the
/// initial number of unfixed neurons, and each level has O(C/log C) nodes
/// in the worst case.
pub const C013_TREE_SIZE_BOUND: ProofStatus = ProofStatus::DerivedPending;

/// Return the C013 theorem entries for the registry.
///
/// These track the proof status of the branching optimality theorems.
#[must_use]
pub fn c013_theorem_entries() -> Vec<TheoremEntry> {
    vec![
        TheoremEntry {
            id: "C013a",
            description: "Balanced split optimality (max min-complexity branching)",
            status: C013_BALANCED_SPLIT_OPTIMALITY,
            phase: Phase::Phase1,
        },
        TheoremEntry {
            id: "C013b",
            description: "Proof complexity monotonicity under neuron fixing",
            status: C013_COMPLEXITY_MONOTONICITY,
            phase: Phase::Phase1,
        },
        TheoremEntry {
            id: "C013c",
            description: "BaB tree size bound O(C log C) under optimal branching",
            status: C013_TREE_SIZE_BOUND,
            phase: Phase::Phase1,
        },
    ]
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_c013_all_pending() {
        assert!(matches!(
            C013_BALANCED_SPLIT_OPTIMALITY,
            ProofStatus::DerivedPending
        ));
        assert!(matches!(
            C013_COMPLEXITY_MONOTONICITY,
            ProofStatus::DerivedPending
        ));
        assert!(matches!(C013_TREE_SIZE_BOUND, ProofStatus::DerivedPending));
    }

    #[test]
    fn test_c013_theorem_entries_count() {
        let entries = c013_theorem_entries();
        assert_eq!(entries.len(), 3, "C013 has 3 sub-theorems");
    }

    #[test]
    fn test_c013_theorem_ids_unique() {
        let entries = c013_theorem_entries();
        let mut ids: Vec<&str> = entries.iter().map(|e| e.id).collect();
        ids.sort();
        ids.dedup();
        assert_eq!(ids.len(), entries.len(), "C013 theorem IDs must be unique");
    }

    #[test]
    fn test_c013_all_phase1() {
        let entries = c013_theorem_entries();
        for entry in &entries {
            assert_eq!(
                entry.phase,
                Phase::Phase1,
                "C013 theorems are Phase 1 (active)"
            );
        }
    }
}
