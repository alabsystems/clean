// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::EqualityTheory;
use crate::cdcl::Lit;
use crate::smt::TermId;

#[cfg(test)]
use crate::proof::ProofForest;

impl EqualityTheory {
    /// Collect all equality assertion literals that contributed to making
    /// t1 and t2 in the same equivalence class (#2270).
    ///
    /// Conservative over-approximation: returns all asserted equality literals
    /// at the current and prior levels. Sound (over-approximate conflict
    /// clauses are still valid for CDCL learning), but less precise than a
    /// minimal explanation using E-graph proof traces.
    pub(crate) fn explain_equality(&self) -> Vec<Lit> {
        let mut lits = Vec::new();
        for level_trail in &self.equality_trail {
            for &(_, _, lit) in level_trail {
                lits.push(lit);
            }
        }
        lits
    }

    /// Extract the set of asserted SAT literals explaining why t1 and t2
    /// are in the same E-class (#2352).
    ///
    /// Uses the proof forest (per-term parent pointer tree) with NCA traversal
    /// for precise explanations immune to post-merge canonical ID changes.
    ///
    /// Falls back to the conservative over-approximation if the forest cannot
    /// produce a complete path (e.g., terms not registered in the forest).
    pub(super) fn explain_why_equal(&mut self, t1: TermId, t2: TermId) -> Vec<Lit> {
        match self.proof_forest.explain(t1, t2) {
            Ok(lits) if !lits.is_empty() || t1 == t2 => {
                self.explanation_stats.precise_count += 1;
                return lits;
            }
            Ok(_) => {
                self.explanation_stats.fallback_count += 1;
            }
            Err(reason) => {
                self.explanation_stats.record_fallback(reason);
            }
        }

        self.explain_equality()
    }

    #[cfg(test)]
    pub(crate) fn set_proof_forest_for_test(&mut self, proof_forest: ProofForest) {
        self.proof_forest = proof_forest;
    }
}
