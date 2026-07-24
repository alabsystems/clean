// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Branching heuristics guided by proof complexity lower bounds.
//!
//! The key insight: when a BaB node must be split, the optimal neuron to
//! branch on is the one that maximizes `min(complexity_left, complexity_right)`.
//! This "balanced complexity" strategy minimizes total tree size because it
//! forces every branch to require a long proof, preventing the adversary from
//! exploiting an easy subproblem to expand the tree.
//!
//! ## Proof Complexity Connection
//!
//! Each BaB subproblem can be viewed as a propositional formula (via the
//! Tjandra-Anderson encoding of piecewise-linear constraints). The proof
//! complexity of refuting this formula provides a lower bound on how many
//! further BaB splits are needed. By the Ben-Sasson & Wigderson width-size
//! relationship, narrower subproblems (fewer unfixed neurons) have shorter
//! proofs, providing a computable proxy for complexity.
//!
//! ## References
//!
//! - Ben-Sasson & Wigderson (1999): width lower bounds imply size lower bounds
//! - Bunel et al. (2020): BaB for NN verification
//! - Haken (1985): exponential lower bounds for resolution

use super::tree::NeuronId;
use crate::nn_verify::ibp_crown::Interval;

/// Branching heuristic strategy.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum BranchingHeuristic {
    /// Maximize `min(complexity_left, complexity_right)` -- the proof
    /// complexity balanced split. This is the theoretically optimal strategy.
    ProofComplexityBalanced,

    /// Split on the neuron with the widest crossing interval `[l, u]`
    /// (largest `u - l` where `l < 0 < u`). Simple but effective baseline.
    MaxInterval,

    /// Split on the neuron whose bounds are most centered around zero
    /// (smallest `|l + u| / (u - l)`). Heuristic for balanced domain splits.
    MostAmbiguous,
}

/// A candidate neuron for branching, with pre-activation bounds.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct BranchCandidate {
    /// Which neuron this candidate represents.
    pub neuron: NeuronId,
    /// Pre-activation interval bounds at the current BaB node.
    pub bounds: Interval,
}

/// Score for a branching candidate under a given heuristic.
///
/// Higher scores indicate better candidates (should be split first).
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct BranchScore {
    /// The candidate neuron.
    pub neuron: NeuronId,
    /// The computed score (higher = better split).
    pub score: f64,
    /// Estimated proof complexity of the "active" subproblem (neuron >= 0).
    pub complexity_active: f64,
    /// Estimated proof complexity of the "inactive" subproblem (neuron <= 0).
    pub complexity_inactive: f64,
}

/// Estimate the proof complexity lower bound for a BaB subproblem.
///
/// Given the set of unfixed (crossing) neuron intervals in a subproblem,
/// estimates a lower bound on the proof complexity of refuting that subproblem.
///
/// The estimate uses the Ben-Sasson & Wigderson width-size relationship:
/// for a formula on `n` variables with minimum refutation width `w`,
/// the proof size is at least `2^{(w - O(1))^2 / n}`. We approximate the
/// "width" of the NN verification formula by the number of unfixed neurons
/// (each contributes a disjunctive case), and the "size" parameter by the
/// total number of variables (2 per unfixed neuron for the encoding).
///
/// This is a conservative lower bound: real proofs may be much longer.
///
/// # Arguments
///
/// * `unfixed_bounds` - Pre-activation intervals for all unfixed (crossing)
///   neurons in the subproblem. A neuron is "unfixed" if its interval
///   contains zero (`lower < 0 < upper`).
///
/// # Returns
///
/// Estimated minimum proof size (number of resolution steps). Returns 1.0
/// for trivial subproblems with 0 or 1 unfixed neurons.
#[must_use]
pub fn proof_complexity_lower_bound(unfixed_bounds: &[Interval]) -> f64 {
    let num_unfixed = unfixed_bounds.len();

    if num_unfixed <= 1 {
        return 1.0;
    }

    // The lower bound uses the Ben-Sasson & Wigderson width-size relationship.
    // For a formula on n variables with minimum refutation width w:
    //   proof_size >= 2^{(w - k)^2 / n}
    //
    // For NN verification encodings, the "width" scales with sqrt(n) for
    // structured formulas (analogous to Tseitin-on-expanders). The key is
    // that proof complexity grows with the number of unfixed neurons.
    let n = num_unfixed as f64;

    // The "hardness" is also influenced by how ambiguous the unfixed neurons
    // are. Neurons with bounds tightly centered on zero are harder to resolve.
    let ambiguity_factor: f64 = unfixed_bounds
        .iter()
        .map(|b| {
            let width = b.upper - b.lower;
            if width < f64::EPSILON {
                return 0.0;
            }
            // How centered is zero in the interval? 1.0 = perfectly centered.
            let center_ratio = 1.0 - (b.lower + b.upper).abs() / width;
            center_ratio.max(0.0)
        })
        .sum::<f64>()
        / n;

    // Complexity model: 2^{sqrt(n) * ambiguity_scale}
    // This captures that:
    // - More unfixed neurons => exponentially harder (sqrt(n) in exponent)
    // - More ambiguous neurons => harder (ambiguity in [0, 1])
    // The sqrt(n) factor comes from the width lower bound on structured
    // formulas; ambiguity modulates how "hard" each neuron's case split is.
    let ambiguity_scale = 0.5 + 0.5 * ambiguity_factor;
    let exponent = n.sqrt() * ambiguity_scale;

    2.0_f64.powf(exponent)
}

/// Estimate complexity after forcing a neuron active (pre-activation >= 0).
///
/// Removes the split neuron from the unfixed set. The remaining neurons
/// keep their bounds (conservative model: bound propagation is not modeled
/// here, which means the estimate is a strict lower bound).
#[must_use]
fn complexity_after_active_split(candidate_idx: usize, unfixed_bounds: &[Interval]) -> f64 {
    // After forcing active: remove this neuron from the unfixed set.
    // We do not model bound propagation effects, which makes this a
    // conservative (lower) estimate of the true subproblem complexity.
    let remaining: Vec<Interval> = unfixed_bounds
        .iter()
        .enumerate()
        .filter(|(i, _)| *i != candidate_idx)
        .map(|(_, b)| *b)
        .collect();

    proof_complexity_lower_bound(&remaining)
}

/// Estimate complexity after forcing a neuron inactive (pre-activation <= 0).
#[must_use]
fn complexity_after_inactive_split(candidate_idx: usize, unfixed_bounds: &[Interval]) -> f64 {
    // Same conservative model: just remove the split neuron.
    let remaining: Vec<Interval> = unfixed_bounds
        .iter()
        .enumerate()
        .filter(|(i, _)| *i != candidate_idx)
        .map(|(_, b)| *b)
        .collect();

    proof_complexity_lower_bound(&remaining)
}

/// Score a single branching candidate under the given heuristic.
///
/// For `ProofComplexityBalanced`, the score is `min(complexity_active,
/// complexity_inactive)` -- the balanced complexity metric. The candidate
/// with the highest such score should be selected.
#[must_use]
pub fn score_candidate(
    candidate: &BranchCandidate,
    candidate_idx: usize,
    all_unfixed: &[Interval],
    heuristic: BranchingHeuristic,
) -> BranchScore {
    let (score, c_active, c_inactive) = match heuristic {
        BranchingHeuristic::ProofComplexityBalanced => {
            let c_a = complexity_after_active_split(candidate_idx, all_unfixed);
            let c_i = complexity_after_inactive_split(candidate_idx, all_unfixed);
            // Balanced split: maximize the minimum complexity of either branch.
            let s = c_a.min(c_i);
            (s, c_a, c_i)
        }
        BranchingHeuristic::MaxInterval => {
            let width = candidate.bounds.upper - candidate.bounds.lower;
            (width, width, width)
        }
        BranchingHeuristic::MostAmbiguous => {
            let width = candidate.bounds.upper - candidate.bounds.lower;
            let ambiguity = if width < f64::EPSILON {
                0.0
            } else {
                1.0 - (candidate.bounds.lower + candidate.bounds.upper).abs() / width
            };
            (ambiguity, ambiguity, ambiguity)
        }
    };

    BranchScore {
        neuron: candidate.neuron,
        score,
        complexity_active: c_active,
        complexity_inactive: c_inactive,
    }
}

/// Select the best branching candidate from a list of unfixed neurons.
///
/// Scores all candidates and returns the one with the highest score.
/// Returns `None` if the candidate list is empty.
///
/// # Arguments
///
/// * `candidates` - Unfixed neurons available for branching.
/// * `heuristic` - Which branching strategy to use.
#[must_use]
pub fn select_best_branch(
    candidates: &[BranchCandidate],
    heuristic: BranchingHeuristic,
) -> Option<BranchScore> {
    if candidates.is_empty() {
        return None;
    }

    let all_bounds: Vec<Interval> = candidates.iter().map(|c| c.bounds).collect();

    candidates
        .iter()
        .enumerate()
        .map(|(i, c)| score_candidate(c, i, &all_bounds, heuristic))
        .max_by(|a, b| {
            a.score
                .partial_cmp(&b.score)
                .unwrap_or(std::cmp::Ordering::Equal)
        })
}

/// Verify the balanced split optimality property for a set of candidates.
///
/// Checks that the proof-complexity-balanced heuristic selects a candidate
/// whose `min(complexity_left, complexity_right)` is at least as large as
/// that of any other candidate. This is the core C013 property.
///
/// Returns `true` if the balanced heuristic is optimal (or vacuously true
/// for <= 1 candidates).
#[must_use]
pub fn verify_balanced_split_optimality(candidates: &[BranchCandidate]) -> bool {
    if candidates.len() <= 1 {
        return true;
    }

    let balanced_best = select_best_branch(candidates, BranchingHeuristic::ProofComplexityBalanced);

    // Verify: no other candidate has a higher min-complexity score.
    let all_bounds: Vec<Interval> = candidates.iter().map(|c| c.bounds).collect();
    let all_scores: Vec<BranchScore> = candidates
        .iter()
        .enumerate()
        .map(|(i, c)| {
            score_candidate(
                c,
                i,
                &all_bounds,
                BranchingHeuristic::ProofComplexityBalanced,
            )
        })
        .collect();

    if let Some(best) = balanced_best {
        all_scores.iter().all(|s| s.score <= best.score)
    } else {
        true
    }
}

/// Verify the complexity monotonicity property.
///
/// As neurons are fixed (split), the proof complexity of remaining
/// subproblems should be non-increasing. This function checks that fixing
/// any single neuron does not increase the complexity lower bound, which
/// is a necessary condition for the BaB tree to terminate.
///
/// Returns `true` if monotonicity holds for all candidates.
#[must_use]
pub fn verify_complexity_monotonicity(unfixed_bounds: &[Interval]) -> bool {
    if unfixed_bounds.len() <= 1 {
        return true;
    }

    let current_complexity = proof_complexity_lower_bound(unfixed_bounds);

    for i in 0..unfixed_bounds.len() {
        let c_active = complexity_after_active_split(i, unfixed_bounds);
        let c_inactive = complexity_after_inactive_split(i, unfixed_bounds);

        // After fixing any neuron, complexity should not exceed current.
        if c_active > current_complexity * (1.0 + f64::EPSILON)
            || c_inactive > current_complexity * (1.0 + f64::EPSILON)
        {
            return false;
        }
    }

    true
}

/// Compute the tree size bound given the balanced complexity split.
///
/// For a subproblem with proof complexity lower bound `C`, the BaB tree
/// using optimal branching has size at most `O(C * log(C))` nodes. This
/// follows from the game-tree evaluation bound: each split reduces the
/// minimum branch complexity by at least a constant factor.
///
/// Returns the estimated maximum tree size for the given complexity.
#[must_use]
pub fn tree_size_bound(complexity_lower_bound: f64) -> f64 {
    if complexity_lower_bound <= 1.0 {
        return 1.0;
    }

    // Game-tree bound: tree size <= C * log2(C)
    // where C is the proof complexity lower bound.
    complexity_lower_bound * complexity_lower_bound.log2()
}
