// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! k-NN tactic recommender and corpus builder.
//!
//! Given a new goal, [`KnnRecommender`] finds the k most similar goals
//! in a [`TacticCorpus`] and recommends their tactic sequences.
//! [`CorpusBuilder`] extracts tactic records from a [`LemmaLibrary`] or
//! from explicit `(Expr, tactic_sequence)` pairs.
//!
//! Part of #3187.

use crate::goal_features::{extract_goal_features, GoalFeatures};
use crate::lemma_library::LemmaLibrary;
use crate::tactic_learning::{
    DistanceWeights, TacticCorpus, TacticRecommendation, TacticRecord, TacticSequence,
};

/// k-Nearest-Neighbor recommender over goal features.
///
/// Given a query goal, finds the k most similar goals in the corpus and
/// returns their tactic sequences ranked by similarity.
pub struct KnnRecommender<'a> {
    corpus: &'a TacticCorpus,
    weights: DistanceWeights,
}

impl<'a> KnnRecommender<'a> {
    /// Create a recommender backed by the given corpus.
    pub fn new(corpus: &'a TacticCorpus, weights: DistanceWeights) -> Self {
        Self { corpus, weights }
    }

    /// Create a recommender with default distance weights.
    pub fn with_defaults(corpus: &'a TacticCorpus) -> Self {
        Self::new(corpus, DistanceWeights::default())
    }

    /// Recommend tactic sequences for a goal, returning up to `k` results
    /// sorted by descending similarity.
    ///
    /// Returns empty if the corpus is empty.
    #[must_use]
    pub fn recommend(&self, goal_features: &GoalFeatures, k: usize) -> Vec<TacticRecommendation> {
        if self.corpus.is_empty() || k == 0 {
            return Vec::new();
        }

        let query_vec = goal_features.to_feature_vector();

        // Compute distances to all corpus entries.
        let mut scored: Vec<(usize, f64)> = self
            .corpus
            .records()
            .iter()
            .enumerate()
            .map(|(idx, record)| {
                let dist =
                    query_vec.weighted_distance(&record.feature_vector, &self.weights.weights);
                (idx, dist)
            })
            .collect();

        // Sort by distance ascending (smallest distance = most similar).
        scored.sort_by(|a, b| a.1.partial_cmp(&b.1).unwrap_or(std::cmp::Ordering::Equal));

        // Take top-k and convert distance to similarity.
        let max_dist = scored
            .last()
            .map(|(_, d)| *d)
            .unwrap_or(1.0)
            .max(f64::EPSILON);

        scored
            .into_iter()
            .take(k)
            .map(|(idx, dist)| {
                let record = &self.corpus.records()[idx];
                TacticRecommendation {
                    tactic_sequence: record.tactic_sequence.clone(),
                    similarity: 1.0 - (dist / max_dist).min(1.0),
                    source_name: record.source_name.clone(),
                }
            })
            .collect()
    }

    /// Quick check: does the corpus have any record whose head symbol matches?
    #[must_use]
    pub fn has_head_symbol_match(&self, head: &str) -> bool {
        self.corpus
            .records()
            .iter()
            .any(|r| r.goal_features.head_symbol.as_deref() == Some(head))
    }
}

/// Builder that extracts tactic records from a lemma library.
///
/// Since lemma entries store proof terms as strings (not parsed Expr trees),
/// the builder uses a heuristic to infer tactic sequences from the proof
/// term structure. For entries that include tactic annotations in their
/// name or proof term, it parses those directly.
pub struct CorpusBuilder<'a> {
    library: &'a LemmaLibrary,
}

impl<'a> CorpusBuilder<'a> {
    /// Create a builder reading from the given library.
    pub fn new(library: &'a LemmaLibrary) -> Self {
        Self { library }
    }

    /// Build a corpus from all lemma entries in the library.
    ///
    /// For each lemma, creates a feature vector from the type signature
    /// and infers a tactic sequence from the proof term. Lemmas without
    /// a parseable proof term are skipped.
    #[must_use]
    pub fn build_corpus(&self) -> TacticCorpus {
        let mut corpus = TacticCorpus::new();

        for entry in self.library.entries() {
            let tactics = infer_tactics_from_proof_term(&entry.proof_term);
            if tactics.is_empty() {
                continue;
            }

            let goal_features = features_from_type_string(&entry.type_signature);
            let feature_vector = goal_features.to_feature_vector();

            corpus.add_record(TacticRecord {
                goal_features,
                feature_vector,
                tactic_sequence: TacticSequence { tactics },
                proof_time_ns: 0,
                source_name: Some(entry.name.clone()),
            });
        }

        corpus
    }

    /// Build a corpus from explicit (goal_expr, tactic_sequence) pairs.
    ///
    /// This is the preferred path when parsed `Expr` goals are available
    /// (e.g., from a live proof session).
    pub fn build_from_expr_pairs(pairs: &[(&clean_kernel::Expr, &[&str], u64)]) -> TacticCorpus {
        let mut corpus = TacticCorpus::new();

        for (expr, tactics, time_ns) in pairs {
            let goal_features = extract_goal_features(expr);
            let feature_vector = goal_features.to_feature_vector();

            corpus.add_record(TacticRecord {
                goal_features,
                feature_vector,
                tactic_sequence: TacticSequence::from_names(tactics),
                proof_time_ns: *time_ns,
                source_name: None,
            });
        }

        corpus
    }
}

/// Heuristically infer tactic names from a proof term string.
///
/// Looks for common tactic-like keywords. Returns empty vec if no
/// recognizable tactics are found.
fn infer_tactics_from_proof_term(proof: &str) -> Vec<String> {
    const KNOWN_TACTICS: &[&str] = &[
        "rfl",
        "exact",
        "apply",
        "intro",
        "intros",
        "simp",
        "ring",
        "mathverse",
        "linarith",
        "norm_num",
        "decide",
        "trivial",
        "assumption",
        "constructor",
        "cases",
        "induction",
        "rewrite",
        "rw",
        "have",
        "let",
        "suffices",
        "calc",
        "conv",
        "ext",
        "funext",
    ];

    let lower = proof.to_lowercase();
    KNOWN_TACTICS
        .iter()
        .filter(|t| lower.contains(*t))
        .map(|t| (*t).to_string())
        .collect()
}

/// Build synthetic GoalFeatures from a type signature string.
///
/// Since LemmaEntry stores type signatures as strings rather than
/// parsed Expr, this provides a rough feature extraction based on
/// string patterns. Less accurate than `extract_goal_features` on
/// an actual Expr, but sufficient for corpus bootstrapping.
fn features_from_type_string(sig: &str) -> GoalFeatures {
    let arrow_count = sig.matches("->").count() + sig.matches('\u{2192}').count();
    let has_prop = sig.contains("Prop");
    let has_nat = sig.contains("Nat") || sig.contains('\u{2115}');

    let head_symbol = sig.split(['\u{2192}', '-']).next_back().and_then(|s| {
        let trimmed = s.trim();
        if trimmed.is_empty() {
            None
        } else {
            trimmed.split_whitespace().next().map(|w| w.to_string())
        }
    });

    GoalFeatures {
        head_symbol,
        arg_count: arrow_count,
        depth: arrow_count + 1,
        size: sig.split_whitespace().count(),
        num_binders: arrow_count,
        num_apps: 0,
        has_prop,
        has_nat_lit: has_nat,
        arg_type_fingerprint: Vec::new(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::Expr;

    #[test]
    fn test_knn_recommend_empty_corpus() {
        let corpus = TacticCorpus::new();
        let recommender = KnnRecommender::with_defaults(&corpus);
        let features = extract_goal_features(&Expr::const_str("anything"));
        let recs = recommender.recommend(&features, 5);
        assert!(recs.is_empty());
    }

    #[test]
    fn test_knn_recommend_single_record() {
        let mut corpus = TacticCorpus::new();
        let features = extract_goal_features(&Expr::const_str("Nat.add"));
        corpus.add_record(TacticRecord {
            goal_features: features.clone(),
            feature_vector: features.to_feature_vector(),
            tactic_sequence: TacticSequence::from_names(&["ring"]),
            proof_time_ns: 100,
            source_name: Some("add_comm".to_string()),
        });

        let recommender = KnnRecommender::with_defaults(&corpus);
        let recs = recommender.recommend(&features, 3);
        assert_eq!(recs.len(), 1);
        assert_eq!(recs[0].tactic_sequence.tactics[0], "ring");
        assert!(recs[0].similarity > 0.99);
    }

    #[test]
    fn test_knn_recommend_most_similar_first() {
        let mut corpus = TacticCorpus::new();

        let f1 = extract_goal_features(&Expr::const_str("Nat.add"));
        corpus.add_record(TacticRecord {
            goal_features: f1.clone(),
            feature_vector: f1.to_feature_vector(),
            tactic_sequence: TacticSequence::from_names(&["ring"]),
            proof_time_ns: 50,
            source_name: None,
        });

        let nested = Expr::app(
            Expr::app(
                Expr::app(Expr::const_str("h"), Expr::const_str("a")),
                Expr::const_str("b"),
            ),
            Expr::const_str("c"),
        );
        let f2 = extract_goal_features(&nested);
        corpus.add_record(TacticRecord {
            goal_features: f2.clone(),
            feature_vector: f2.to_feature_vector(),
            tactic_sequence: TacticSequence::from_names(&["apply", "exact"]),
            proof_time_ns: 200,
            source_name: None,
        });

        let recommender = KnnRecommender::with_defaults(&corpus);
        let query = extract_goal_features(&Expr::const_str("Nat.mul"));
        let recs = recommender.recommend(&query, 2);
        assert_eq!(recs.len(), 2);
        assert_eq!(recs[0].tactic_sequence.tactics[0], "ring");
    }

    #[test]
    fn test_knn_k_limits_results() {
        let mut corpus = TacticCorpus::new();
        for i in 0..10 {
            let f = extract_goal_features(&Expr::const_str(&format!("f{i}")));
            corpus.add_record(TacticRecord {
                goal_features: f.clone(),
                feature_vector: f.to_feature_vector(),
                tactic_sequence: TacticSequence::from_names(&["tac"]),
                proof_time_ns: 0,
                source_name: None,
            });
        }

        let recommender = KnnRecommender::with_defaults(&corpus);
        let query = extract_goal_features(&Expr::const_str("query"));
        let recs = recommender.recommend(&query, 3);
        assert_eq!(recs.len(), 3);
    }

    #[test]
    fn test_has_head_symbol_match() {
        let mut corpus = TacticCorpus::new();
        let f = extract_goal_features(&Expr::const_str("Nat.add"));
        corpus.add_record(TacticRecord {
            goal_features: f.clone(),
            feature_vector: f.to_feature_vector(),
            tactic_sequence: TacticSequence::from_names(&["ring"]),
            proof_time_ns: 0,
            source_name: None,
        });

        let recommender = KnnRecommender::with_defaults(&corpus);
        assert!(recommender.has_head_symbol_match("Nat.add"));
        assert!(!recommender.has_head_symbol_match("Nat.sub"));
    }

    #[test]
    fn test_infer_tactics_from_proof_term() {
        let tactics = infer_tactics_from_proof_term("fun a b => by intro h; simp; ring");
        assert!(tactics.contains(&"intro".to_string()));
        assert!(tactics.contains(&"simp".to_string()));
        assert!(tactics.contains(&"ring".to_string()));
    }

    #[test]
    fn test_infer_tactics_empty_proof() {
        let tactics = infer_tactics_from_proof_term("fun a b => le_refl a");
        assert!(tactics.is_empty());
    }

    #[test]
    fn test_features_from_type_string() {
        let features = features_from_type_string("Nat -> Nat -> Prop");
        assert!(features.has_prop);
        assert!(features.has_nat_lit);
        assert_eq!(features.num_binders, 2);
    }

    #[test]
    fn test_corpus_builder_from_expr_pairs() {
        let goal_a = Expr::const_str("Nat.add");
        let goal_b = Expr::app(Expr::const_str("f"), Expr::const_str("x"));

        let pairs: Vec<(&Expr, &[&str], u64)> = vec![
            (&goal_a, &["ring"], 100),
            (&goal_b, &["apply", "exact"], 200),
        ];

        let corpus = CorpusBuilder::build_from_expr_pairs(&pairs);
        assert_eq!(corpus.len(), 2);
        assert_eq!(corpus.records()[0].tactic_sequence.tactics[0], "ring");
        assert_eq!(corpus.records()[1].tactic_sequence.len(), 2);
    }
}
