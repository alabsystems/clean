// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Proof trace: records all union operations for proof path reconstruction.

use super::{ProofStep, UnionReason};
use clean_kernel::name::Name;
use clean_kernel::Expr;
use std::collections::{HashMap, HashSet, VecDeque};

/// Proof trace recording all union operations
#[derive(Debug, Clone, Default)]
pub struct ProofTrace {
    /// Sequence of union operations with reasons
    pub steps: Vec<(u32, u32, UnionReason)>, // (e-class1, e-class2, reason)
    /// Mapping from (e-class, e-class) to proof index
    proof_index: HashMap<(u32, u32), usize>,
}

impl ProofTrace {
    /// Create a new empty proof trace
    pub fn new() -> Self {
        ProofTrace {
            steps: Vec::new(),
            proof_index: HashMap::new(),
        }
    }

    fn index_step(&mut self, ec1: u32, ec2: u32, idx: usize) {
        self.proof_index.insert((ec1, ec2), idx);
        self.proof_index.insert((ec2, ec1), idx);
    }

    /// Return the number of recorded union steps.
    pub fn len(&self) -> usize {
        self.steps.len()
    }

    /// Truncate the trace to the given prefix length and rebuild lookup indices.
    pub fn truncate(&mut self, len: usize) {
        assert!(
            len <= self.steps.len(),
            "cannot truncate ProofTrace from {} to {}",
            self.steps.len(),
            len
        );
        if len == self.steps.len() {
            return;
        }

        self.steps.truncate(len);
        self.proof_index.clear();
        for idx in 0..self.steps.len() {
            let (ec1, ec2) = {
                let (ec1, ec2, _) = &self.steps[idx];
                (*ec1, *ec2)
            };
            self.index_step(ec1, ec2, idx);
        }
    }

    /// Record a union with its reason
    pub fn record_union(&mut self, ec1: u32, ec2: u32, reason: UnionReason) -> usize {
        let idx = self.steps.len();
        self.steps.push((ec1, ec2, reason));

        // Index both directions for lookup
        self.index_step(ec1, ec2, idx);

        idx
    }

    /// Get the proof index for a union
    pub fn get_proof_index(&self, ec1: u32, ec2: u32) -> Option<usize> {
        self.proof_index.get(&(ec1, ec2)).copied()
    }

    /// Get the reason for a specific proof step
    #[cfg(test)]
    pub fn get_reason(&self, idx: usize) -> Option<&UnionReason> {
        self.steps.get(idx).map(|(_, _, r)| r)
    }

    /// Build a proof step from an e-class equality
    /// Returns None if no proof path exists
    pub fn build_proof(&self, ec1: u32, ec2: u32) -> Option<ProofStep> {
        if ec1 == ec2 {
            // Reflexivity - need a term ID, but we don't have it here
            // This should be handled by the caller
            return None;
        }

        // Direct proof exists?
        if let Some(&idx) = self.proof_index.get(&(ec1, ec2)) {
            return self.step_to_proof(idx, ec1, ec2);
        }

        // Need to find a path through the trace
        // This is a BFS through the union-find history
        self.find_proof_path(ec1, ec2)
    }

    /// Convert a trace step to a ProofStep
    fn step_to_proof(
        &self,
        idx: usize,
        requested_ec1: u32,
        _requested_ec2: u32,
    ) -> Option<ProofStep> {
        let (ec1, _ec2, reason) = self.steps.get(idx)?;

        // Check if we need to flip the proof
        let needs_flip = *ec1 != requested_ec1;

        let proof = match reason {
            UnionReason::Asserted {
                hypothesis,
                lhs,
                rhs,
            } => {
                if let Some(fvar) = hypothesis {
                    ProofStep::Hypothesis(*fvar)
                } else {
                    // No hypothesis means this was asserted directly.
                    // Use reflexivity if lhs == rhs, otherwise proof reconstruction fails.
                    // We MUST NOT generate unverified Axiom placeholders as that
                    // undermines the soundness of the proof system.
                    if lhs == rhs {
                        ProofStep::Refl(*lhs)
                    } else {
                        // Proof reconstruction failed - assertion has no justification
                        // The caller must handle this case (e.g., report error to user)
                        return None;
                    }
                }
            }
            UnionReason::Congruence {
                func, arg_reasons, ..
            } => {
                // Build proofs for each argument equality
                let arg_proofs: Vec<ProofStep> = arg_reasons
                    .iter()
                    .filter_map(|&arg_idx| {
                        if let Some((ec1, ec2, _)) = self.steps.get(arg_idx as usize) {
                            self.step_to_proof(arg_idx as usize, *ec1, *ec2)
                        } else {
                            None
                        }
                    })
                    .collect();

                // If arg_reasons is empty but we have congruence, that means the
                // children were already in the same e-class (reflexive case).
                // However, without actual proofs we cannot construct a valid proof term.
                //
                // We MUST NOT generate unverified Axiom placeholders as that
                // undermines the soundness of the proof system.
                if arg_proofs.len() != arg_reasons.len() {
                    // Some or all arg proofs failed - reconstruction failed.
                    // Producing a Congr with mismatched arg count would generate
                    // an ill-typed kernel term. (Algorithm audit: P1 810)
                    return None;
                }
                // Note: empty arg_reasons with empty arg_proofs is valid for nullary functions.
                // The trace only has the function name, not universe levels.
                // Phase A operates in a universe-monomorphic context (empty levels OK).
                // Phase B+ callers should supply the full Expr via try_congruence_proof.
                ProofStep::Congr(Expr::const_(Name::from_string(func), vec![]), arg_proofs)
            }
        };

        if needs_flip {
            Some(ProofStep::symm(proof))
        } else {
            Some(proof)
        }
    }

    /// Find a proof path using BFS
    fn find_proof_path(&self, start: u32, end: u32) -> Option<ProofStep> {
        // BFS to find a path
        let mut visited: HashSet<u32> = HashSet::new();
        let mut queue: VecDeque<(u32, ProofStep)> = VecDeque::new();

        // Initialize with all edges from start
        visited.insert(start);
        for (idx, (ec1, ec2, _)) in self.steps.iter().enumerate() {
            if *ec1 == start {
                if let Some(step) = self.step_to_proof(idx, *ec1, *ec2) {
                    if *ec2 == end {
                        return Some(step);
                    }
                    queue.push_back((*ec2, step));
                }
            } else if *ec2 == start {
                if let Some(step) = self.step_to_proof(idx, *ec2, *ec1) {
                    if *ec1 == end {
                        return Some(step);
                    }
                    queue.push_back((*ec1, step));
                }
            }
        }

        // BFS
        while let Some((current, current_proof)) = queue.pop_front() {
            if !visited.insert(current) {
                continue;
            }

            // Find all edges from current
            for (idx, (ec1, ec2, _)) in self.steps.iter().enumerate() {
                let (next, next_ec1, next_ec2) = if *ec1 == current && !visited.contains(ec2) {
                    (*ec2, *ec1, *ec2)
                } else if *ec2 == current && !visited.contains(ec1) {
                    (*ec1, *ec2, *ec1)
                } else {
                    continue;
                };

                if let Some(next_step) = self.step_to_proof(idx, next_ec1, next_ec2) {
                    let combined = ProofStep::trans(current_proof.clone(), next_step);

                    if next == end {
                        return Some(combined);
                    }

                    queue.push_back((next, combined));
                }
            }
        }

        None
    }
}
