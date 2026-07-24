// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::EqualityTheory;
use crate::proof::ExplainFailure;

/// Statistics for equality theory
#[derive(Clone, Debug, Default)]
pub struct EqualityStats {
    pub num_eclasses: usize,
    pub num_enodes: usize,
    pub num_disequalities: usize,
    pub num_terms: usize,
}

/// Runtime counters for precise-vs-fallback EUF explanations.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct ExplanationStats {
    pub precise_count: u64,
    pub fallback_count: u64,
    pub recursion_limit_count: u64,
    pub forest_depth_limit_count: u64,
    pub disconnected_terms_count: u64,
    pub broken_ancestor_path_count: u64,
    pub congruence_argument_failure_count: u64,
}

impl ExplanationStats {
    pub(super) fn record_fallback(&mut self, reason: ExplainFailure) {
        self.fallback_count += 1;
        match reason {
            ExplainFailure::RecursionLimit => self.recursion_limit_count += 1,
            ExplainFailure::ForestDepthLimit => self.forest_depth_limit_count += 1,
            ExplainFailure::DisconnectedTerms => self.disconnected_terms_count += 1,
            ExplainFailure::BrokenAncestorPath => self.broken_ancestor_path_count += 1,
            ExplainFailure::CongruenceArgumentUnexplained => {
                self.congruence_argument_failure_count += 1;
            }
        }
    }
}

impl EqualityTheory {
    /// Get runtime counters for precise-vs-fallback EUF explanations.
    pub fn explanation_stats(&self) -> &ExplanationStats {
        &self.explanation_stats
    }

    /// Get statistics
    pub fn stats(&self) -> EqualityStats {
        EqualityStats {
            num_eclasses: self.egraph.num_classes(),
            num_enodes: self.egraph.num_nodes(),
            num_disequalities: self.disequalities.len(),
            num_terms: self.term_to_eclass.len(),
        }
    }
}
