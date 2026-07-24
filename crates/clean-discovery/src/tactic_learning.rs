// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tactic learning types: corpus, records, and tactic sequences.
//!
//! After accumulating proven theorems, the tactic learning system analyzes
//! which tactic sequences worked for which goal patterns. This module
//! provides the core data types; the k-NN recommender lives in
//! [`crate::tactic_recommender`].
//!
//! Part of #3187.

use std::path::Path;

use serde::{Deserialize, Serialize};

use crate::error::DiscoveryError;
use crate::goal_features::{FeatureVector, GoalFeatures};

/// An ordered sequence of tactic names applied to close a goal.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct TacticSequence {
    /// Tactic names in application order.
    pub tactics: Vec<String>,
}

impl TacticSequence {
    /// Create from a slice of tactic name strings.
    pub fn from_names(names: &[&str]) -> Self {
        Self {
            tactics: names.iter().map(|s| (*s).to_string()).collect(),
        }
    }

    /// Number of tactics in the sequence.
    #[must_use]
    pub fn len(&self) -> usize {
        self.tactics.len()
    }

    /// Whether the sequence is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.tactics.is_empty()
    }
}

/// A single record in the tactic corpus: a successful tactic sequence
/// paired with the goal it solved and performance metadata.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct TacticRecord {
    /// Features of the goal that was solved.
    pub goal_features: GoalFeatures,
    /// Cached normalized feature vector (avoids recomputing on each lookup).
    pub feature_vector: FeatureVector,
    /// The tactic sequence that successfully closed the goal.
    pub tactic_sequence: TacticSequence,
    /// Proof verification time in nanoseconds (lower is better).
    pub proof_time_ns: u64,
    /// Optional human-readable description of the source theorem.
    pub source_name: Option<String>,
}

/// A tactic recommendation from the k-NN recommender.
#[derive(Debug, Clone)]
pub struct TacticRecommendation {
    /// The recommended tactic sequence.
    pub tactic_sequence: TacticSequence,
    /// Similarity score in [0, 1] (higher is more similar).
    pub similarity: f64,
    /// Name of the source theorem this recommendation comes from.
    pub source_name: Option<String>,
}

/// Persistent collection of tactic records, serializable to JSON.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TacticCorpus {
    records: Vec<TacticRecord>,
}

impl TacticCorpus {
    /// Create an empty corpus.
    #[must_use]
    pub fn new() -> Self {
        Self {
            records: Vec::new(),
        }
    }

    /// Add a record to the corpus.
    pub fn add_record(&mut self, record: TacticRecord) {
        self.records.push(record);
    }

    /// Number of records in the corpus.
    #[must_use]
    pub fn len(&self) -> usize {
        self.records.len()
    }

    /// Whether the corpus is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.records.is_empty()
    }

    /// Immutable access to all records.
    pub fn records(&self) -> &[TacticRecord] {
        &self.records
    }

    /// Save the corpus to a JSON file.
    pub fn save(&self, path: impl AsRef<Path>) -> Result<(), DiscoveryError> {
        let json = serde_json::to_string_pretty(self)
            .map_err(|e| DiscoveryError::Serialization(e.to_string()))?;
        std::fs::write(path.as_ref(), json)?;
        Ok(())
    }

    /// Load a corpus from a JSON file.
    pub fn load(path: impl AsRef<Path>) -> Result<Self, DiscoveryError> {
        let data = std::fs::read_to_string(path.as_ref())?;
        let corpus: Self = serde_json::from_str(&data)
            .map_err(|e| DiscoveryError::Serialization(e.to_string()))?;
        Ok(corpus)
    }
}

impl Default for TacticCorpus {
    fn default() -> Self {
        Self::new()
    }
}

/// Weights for the k-NN distance function.
///
/// Indices correspond to the feature vector produced by
/// [`GoalFeatures::to_feature_vector`]:
/// 0=depth, 1=size, 2=binders, 3=apps, 4=args, 5=has_prop, 6=has_nat_lit.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DistanceWeights {
    /// Per-dimension weights. Missing dimensions default to 1.0.
    pub weights: Vec<f64>,
}

impl Default for DistanceWeights {
    fn default() -> Self {
        Self {
            weights: vec![
                1.0, // depth
                1.5, // size (slightly more important)
                1.0, // num_binders
                1.2, // num_apps
                1.0, // arg_count
                2.0, // has_prop (strong signal)
                1.5, // has_nat_lit
            ],
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::goal_features::extract_goal_features;
    use clean_kernel::Expr;

    #[test]
    fn test_tactic_sequence_from_names() {
        let seq = TacticSequence::from_names(&["intro", "simp", "ring"]);
        assert_eq!(seq.len(), 3);
        assert!(!seq.is_empty());
        assert_eq!(seq.tactics[0], "intro");
    }

    #[test]
    fn test_tactic_corpus_add_and_len() {
        let mut corpus = TacticCorpus::new();
        assert!(corpus.is_empty());

        let features = extract_goal_features(&Expr::const_str("Nat.add"));
        let record = TacticRecord {
            goal_features: features.clone(),
            feature_vector: features.to_feature_vector(),
            tactic_sequence: TacticSequence::from_names(&["ring"]),
            proof_time_ns: 100,
            source_name: Some("test_thm".to_string()),
        };
        corpus.add_record(record);
        assert_eq!(corpus.len(), 1);
    }

    #[test]
    fn test_corpus_save_load_roundtrip() {
        let path = std::env::temp_dir().join("clean_tactic_corpus_test.json");

        let mut corpus = TacticCorpus::new();
        let features = extract_goal_features(&Expr::const_str("f"));
        corpus.add_record(TacticRecord {
            goal_features: features.clone(),
            feature_vector: features.to_feature_vector(),
            tactic_sequence: TacticSequence::from_names(&["exact"]),
            proof_time_ns: 50,
            source_name: None,
        });

        corpus.save(&path).expect("should save corpus");
        let loaded = TacticCorpus::load(&path).expect("should load corpus");
        assert_eq!(loaded.len(), 1);
        assert_eq!(loaded.records()[0].tactic_sequence.tactics[0], "exact");

        let _ = std::fs::remove_file(&path);
    }

    #[test]
    fn test_distance_weights_default() {
        let w = DistanceWeights::default();
        assert_eq!(w.weights.len(), 7);
        // has_prop should have highest weight.
        assert!(w.weights[5] >= w.weights[0]);
    }
}
