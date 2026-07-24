// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Optimal Branch-and-Bound (BaB) branching via proof complexity lower bounds (C013).
//!
//! Neural network verifiers using branch-and-bound must choose which neuron to
//! split on at each step. This module formalizes the theory that optimal branching
//! is guided by proof complexity lower bounds: the neuron whose split maximizes
//! the minimum proof complexity of the resulting subproblems minimizes total
//! tree size.
//!
//! ## Architecture
//!
//! - [`tree`]: BaB tree formalization (nodes, tree structure, metrics)
//! - [`branching`]: Branching heuristics with proof complexity scoring
//! - [`c013_spec`]: C013 theorem specification with proof status tracking
//!
//! ## Key Theorem (C013)
//!
//! For an unsatisfiable NN verification subproblem encoded as a formula F,
//! branching on the neuron that maximizes `min(complexity(F_left), complexity(F_right))`
//! minimizes the total BaB tree size in the worst case. This follows from the
//! game-tree evaluation bound: a balanced complexity split forces the adversary
//! to provide long proofs on both branches.
//!
//! ## References
//!
//! - Bunel et al., "Branch and Bound for Piecewise Linear Neural Network
//!   Verification" (JMLR 2020)
//! - De Palma et al., "Improved Branch and Bound for Neural Network
//!   Verification via Lagrangian Decomposition" (2021)
//! - Ben-Sasson & Wigderson, "Short proofs are narrow -- resolution made
//!   simple" (1999) -- width-complexity connection used for lower bounds
//! - Haken, "The intractability of resolution" (1985) -- exponential lower
//!   bounds for PHP, applied to subproblem hardness estimation

pub mod branching;
pub mod c013_spec;
pub mod tree;

#[cfg(test)]
mod tests_branching;
#[cfg(test)]
mod tests_tree;

pub use branching::{
    proof_complexity_lower_bound, score_candidate, select_best_branch, BranchCandidate,
    BranchScore, BranchingHeuristic,
};
pub use c013_spec::{
    c013_theorem_entries, C013_BALANCED_SPLIT_OPTIMALITY, C013_COMPLEXITY_MONOTONICITY,
    C013_TREE_SIZE_BOUND,
};
pub use tree::{BabNode, BabTree, NodeId, SplitDirection, VerificationResult};
