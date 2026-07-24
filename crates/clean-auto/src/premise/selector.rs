// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Premise selectors: MePo (symbol-based), MaSh (ML-based), and Hybrid.

use super::{Feature, FeatureExtractor, FeatureSet, Premise, PremiseDatabase, PremiseId};
use clean_kernel::{Expr, ExprKind, Name};
use std::cmp::Ordering;
use std::collections::{HashMap, HashSet};

/// Weight multiplier for a goal symbol that overlaps a premise's *hypotheses*
/// only (not its conclusion). Conclusion overlap scores full weight; a symbol
/// that appears only in a premise's antecedents is a weaker relevance signal.
const HYP_OVERLAP_DISCOUNT: f64 = 0.4;

/// Fraction of a relevant premise's score propagated to each of its recorded
/// dependencies, so a lemma needed by a highly-relevant lemma is pulled in even
/// when its own symbol overlap with the goal is thin (dependency scoring).
const DEPENDENCY_BONUS: f64 = 0.5;

/// Record of a successful proof for learning
#[derive(Clone, Debug)]
pub(crate) struct ProofRecord {
    /// Features of the proved goal
    pub(crate) goal_features: FeatureSet,
    /// Premises that were useful
    pub(crate) useful_premises: Vec<PremiseId>,
}

pub(super) fn cmp_score_desc_then_id(
    score_a: f64,
    id_a: PremiseId,
    score_b: f64,
    id_b: PremiseId,
) -> Ordering {
    match (score_a.is_nan(), score_b.is_nan()) {
        (true, true) => id_a.0.cmp(&id_b.0),
        (true, false) => Ordering::Greater,
        (false, true) => Ordering::Less,
        (false, false) => score_b
            .total_cmp(&score_a)
            .then_with(|| id_a.0.cmp(&id_b.0)),
    }
}

/// MePo (Meng-Paulson) Symbol-Based Premise Selection
///
/// Ranks premises by weighted symbol overlap with the goal.
/// Rare symbols receive higher weight using the formula:
///   weight(c) = 1 + 2 / ln(freq(c) + 1)
pub struct MePoSelector<'a> {
    db: &'a PremiseDatabase,
    /// Relevance threshold (0.0 to 1.0)
    threshold: f64,
    /// Maximum number of premises to select
    max_premises: usize,
}

impl<'a> MePoSelector<'a> {
    /// Create a new MePo selector
    pub fn new(db: &'a PremiseDatabase) -> Self {
        Self {
            db,
            threshold: 0.1,
            max_premises: 64,
        }
    }

    /// Set the relevance threshold
    #[must_use]
    pub fn with_threshold(mut self, threshold: f64) -> Self {
        self.threshold = threshold;
        self
    }

    /// Set the maximum number of premises
    #[must_use]
    pub fn with_max_premises(mut self, max: usize) -> Self {
        self.max_premises = max;
        self
    }

    /// Compute the weight of a constant based on its rarity
    pub(super) fn const_weight(&self, name: &Name) -> f64 {
        let freq = self.db.const_frequency(name);
        1.0 + 2.0 / (freq as f64 + 1.0).ln()
    }

    /// Compute relevance score for a premise given goal constants
    fn relevance(&self, premise: &Premise, goal_constants: &HashSet<Name>) -> f64 {
        let mut score = 0.0;
        let mut max_possible = 0.0;

        // Compute weighted overlap
        for c in goal_constants {
            let w = self.const_weight(c);
            max_possible += w;
            if premise.constants.contains(c) {
                score += w;
            }
        }

        // Normalize by maximum possible score
        if max_possible > 0.0 {
            score / max_possible
        } else {
            0.0
        }
    }

    /// Select relevant premises for a goal
    ///
    /// REQUIRES: `goal` is a well-formed Lean expression
    /// ENSURES: Returns premises sorted by relevance score (descending)
    /// ENSURES: All returned premises have score >= threshold
    /// ENSURES: Returns at most max_premises premises
    /// ENSURES: Returns empty Vec if goal contains no constants
    pub fn select(&self, goal: &Expr) -> Vec<&Premise> {
        let extractor = FeatureExtractor::new();
        let goal_constants = extractor.extract_constants(goal);

        if goal_constants.is_empty() {
            return Vec::new();
        }

        // Score all premises
        let mut scored: Vec<_> = self
            .db
            .iter()
            .map(|p| {
                let score = self.relevance(p, &goal_constants);
                (p, score)
            })
            .filter(|(_, score)| *score >= self.threshold)
            .collect();

        // Sort by score (descending), then by premise ID for stability
        scored.sort_by(|a, b| cmp_score_desc_then_id(a.1, a.0.id, b.1, b.0.id));

        // Take top N
        scored
            .into_iter()
            .take(self.max_premises)
            .map(|(p, _)| p)
            .collect()
    }

    /// Select with scores (for debugging/analysis)
    ///
    /// REQUIRES: `goal` is a well-formed Lean expression
    /// ENSURES: Returns (premise, score) pairs sorted by score (descending)
    /// ENSURES: All scores are in range [threshold, 1.0]
    /// ENSURES: Returns at most max_premises pairs
    pub fn select_with_scores(&self, goal: &Expr) -> Vec<(&Premise, f64)> {
        let extractor = FeatureExtractor::new();
        let goal_constants = extractor.extract_constants(goal);

        if goal_constants.is_empty() {
            return Vec::new();
        }

        let mut scored: Vec<_> = self
            .db
            .iter()
            .map(|p| {
                let score = self.relevance(p, &goal_constants);
                (p, score)
            })
            .filter(|(_, score)| *score >= self.threshold)
            .collect();

        // Sort by score (descending), then by premise ID for stability
        scored.sort_by(|a, b| cmp_score_desc_then_id(a.1, a.0.id, b.1, b.0.id));
        scored.into_iter().take(self.max_premises).collect()
    }

    /// Refined weighted symbol overlap that distinguishes *where* in the premise
    /// a goal symbol occurs.
    ///
    /// Identical normalisation to [`Self::relevance`], but a goal symbol that
    /// overlaps a symbol in the premise's **conclusion** (the statement with its
    /// leading binders/antecedents stripped) scores full weight, while a symbol
    /// that overlaps only the premise's *hypotheses* is discounted by
    /// [`HYP_OVERLAP_DISCOUNT`]. The conclusion is what the premise actually
    /// proves *about*, so it is the stronger relevance signal — this is the
    /// standard MePo "conclusion-weighted" refinement and improves precision for
    /// equational/rewriting goals (`f (g x) = …`) where the head symbol matters.
    fn relevance_refined(&self, premise: &Premise, goal_constants: &HashSet<Name>) -> f64 {
        let conclusion = conclusion_constants(&premise.statement);
        let mut score = 0.0;
        let mut max_possible = 0.0;
        for c in goal_constants {
            let w = self.const_weight(c);
            max_possible += w;
            if premise.constants.contains(c) {
                let factor = if conclusion.contains(c) {
                    1.0
                } else {
                    HYP_OVERLAP_DISCOUNT
                };
                score += w * factor;
            }
        }
        if max_possible > 0.0 {
            score / max_possible
        } else {
            0.0
        }
    }

    /// Select the most relevant premises for `goal`, best-first, capped at `max`.
    ///
    /// Two improvements over [`Self::select`] / [`Self::select_with_scores`],
    /// both motivated by feeding the *right specific lemma* to the engines:
    ///
    ///   1. **conclusion-weighted overlap** ([`Self::relevance_refined`]) — a
    ///      lemma that *concludes* about a goal symbol outranks one that only
    ///      *mentions* it in a hypothesis;
    ///   2. **dependency propagation** — each relevant premise lifts the score
    ///      of the premises it recorded as proof dependencies (by
    ///      [`DEPENDENCY_BONUS`] × its own score), so a supporting lemma with
    ///      thin direct overlap is still surfaced.
    ///
    /// Returns premises with a strictly-positive score, sorted by score then id.
    pub fn select_relevant(&self, goal: &Expr, max: usize) -> Vec<&Premise> {
        let extractor = FeatureExtractor::new();
        let goal_constants = extractor.extract_constants(goal);
        if goal_constants.is_empty() {
            return Vec::new();
        }

        let mut scores: HashMap<PremiseId, f64> = self
            .db
            .iter()
            .map(|p| (p.id, self.relevance_refined(p, &goal_constants)))
            .filter(|(_, score)| *score > 0.0)
            .collect();

        // Dependency propagation: snapshot the base scores first so the bonus
        // derives only from direct-overlap relevance (not from other bonuses).
        let base: Vec<(PremiseId, f64)> = scores.iter().map(|(id, s)| (*id, *s)).collect();
        for (id, base_score) in base {
            if let Some(premise) = self.db.get(id) {
                for dep in &premise.dependencies {
                    *scores.entry(*dep).or_insert(0.0) += DEPENDENCY_BONUS * base_score;
                }
            }
        }

        let mut scored: Vec<(PremiseId, f64)> = scores.into_iter().collect();
        scored.sort_by(|a, b| cmp_score_desc_then_id(a.1, a.0, b.1, b.0));
        scored
            .into_iter()
            .take(max)
            .filter_map(|(id, _)| self.db.get(id))
            .collect()
    }
}

/// Constants appearing in the *conclusion* of a premise statement.
///
/// Strips leading `Pi` binders (universal quantifiers and implication
/// antecedents) to reach the conclusion, then extracts its constants. For an
/// equational lemma `∀ x y, f x y = f y x` this returns `{Eq, f}`; for an
/// implication `a = b → g a = g b` it returns `{Eq, g}` (the antecedent `Eq`/`a`/`b`
/// occurrences are excluded — they belong to the hypotheses).
fn conclusion_constants(statement: &Expr) -> HashSet<Name> {
    let mut current = statement.clone();
    loop {
        let stripped = current.strip_mdata().clone();
        match stripped.kind() {
            ExprKind::Pi(_, _, body) => current = (**body).clone(),
            _ => break,
        }
    }
    FeatureExtractor::new().extract_constants(&current)
}

/// MaSh (Machine Learning for Sledgehammer) Feature-Based Premise Selection
///
/// Uses k-NN and/or Naive Bayes to predict useful premises based on
/// feature similarity and learning from past proof attempts.
pub struct MaShSelector<'a> {
    db: &'a PremiseDatabase,
    /// Proof history: goal features -> useful premises
    proof_history: Vec<ProofRecord>,
    /// k for k-NN
    k: usize,
    /// Maximum premises to return
    max_premises: usize,
    /// Use naive Bayes in addition to k-NN
    use_naive_bayes: bool,
}

impl<'a> MaShSelector<'a> {
    /// Create a new MaSh selector
    pub fn new(db: &'a PremiseDatabase) -> Self {
        Self {
            db,
            proof_history: Vec::new(),
            k: 16,
            max_premises: 64,
            use_naive_bayes: true,
        }
    }

    /// Set k for k-NN
    #[must_use]
    pub fn with_k(mut self, k: usize) -> Self {
        self.k = k;
        self
    }

    /// Set maximum premises
    #[must_use]
    pub fn with_max_premises(mut self, max: usize) -> Self {
        self.max_premises = max;
        self
    }

    /// Enable/disable Naive Bayes
    #[must_use]
    pub fn with_naive_bayes(mut self, use_nb: bool) -> Self {
        self.use_naive_bayes = use_nb;
        self
    }

    /// Record a successful proof for learning
    pub fn record_proof(&mut self, goal: &Expr, useful_premises: Vec<PremiseId>) {
        let extractor = FeatureExtractor::new();
        let goal_features = extractor.extract(goal);
        self.proof_history.push(ProofRecord {
            goal_features,
            useful_premises,
        });
    }

    /// Select premises using k-NN
    fn select_knn(&self, goal_features: &FeatureSet) -> HashMap<PremiseId, f64> {
        let mut premise_scores: HashMap<PremiseId, f64> = HashMap::new();

        if self.proof_history.is_empty() {
            return premise_scores;
        }

        // Find k nearest neighbors by feature similarity
        let mut neighbors: Vec<_> = self
            .proof_history
            .iter()
            .enumerate()
            .map(|(idx, record)| {
                let sim = goal_features.jaccard(&record.goal_features);
                (record, sim, idx)
            })
            .collect();

        neighbors.sort_by(|a, b| match (a.1.is_nan(), b.1.is_nan()) {
            (true, true) => a.2.cmp(&b.2),
            (true, false) => Ordering::Greater,
            (false, true) => Ordering::Less,
            (false, false) => b.1.total_cmp(&a.1).then_with(|| a.2.cmp(&b.2)),
        });
        let k_nearest: Vec<_> = neighbors.into_iter().take(self.k).collect();

        // Aggregate premise scores from neighbors
        for (record, sim, _) in k_nearest {
            for &premise_id in &record.useful_premises {
                *premise_scores.entry(premise_id).or_insert(0.0) += sim;
            }
        }

        premise_scores
    }

    /// Select premises using Naive Bayes
    fn select_naive_bayes(&self, goal_features: &FeatureSet) -> HashMap<PremiseId, f64> {
        let mut premise_scores: HashMap<PremiseId, f64> = HashMap::new();

        // Compute feature -> premise associations from history
        let mut feature_premise_count: HashMap<&Feature, HashMap<PremiseId, usize>> =
            HashMap::new();
        let mut feature_count: HashMap<&Feature, usize> = HashMap::new();
        let mut premise_count: HashMap<PremiseId, usize> = HashMap::new();

        for record in &self.proof_history {
            for feature in record.goal_features.features() {
                *feature_count.entry(feature).or_insert(0) += 1;
                for &premise_id in &record.useful_premises {
                    *feature_premise_count
                        .entry(feature)
                        .or_default()
                        .entry(premise_id)
                        .or_insert(0) += 1;
                }
            }
            for &premise_id in &record.useful_premises {
                *premise_count.entry(premise_id).or_insert(0) += 1;
            }
        }

        let total_records = self.proof_history.len() as f64;
        if total_records == 0.0 {
            return premise_scores;
        }

        // For each premise, compute P(premise | goal_features) using Naive Bayes
        for premise in self.db.iter() {
            let prior = (*premise_count.get(&premise.id).unwrap_or(&0) as f64 + 1.0)
                / (total_records + 2.0);

            let mut log_likelihood = prior.ln();

            for feature in goal_features.features() {
                if let Some(fp_count) = feature_premise_count.get(feature) {
                    let count = *fp_count.get(&premise.id).unwrap_or(&0) as f64;
                    let feat_count = *feature_count.get(feature).unwrap_or(&0) as f64;
                    // Laplace smoothing
                    let prob = (count + 1.0) / (feat_count + 2.0);
                    log_likelihood += prob.ln();
                }
            }

            if log_likelihood.is_finite() {
                premise_scores.insert(premise.id, log_likelihood);
            }
        }

        premise_scores
    }

    /// Select premises for a goal
    pub fn select(&self, goal: &Expr) -> Vec<&Premise> {
        let extractor = FeatureExtractor::new();
        let goal_features = extractor.extract(goal);

        // Combine k-NN and Naive Bayes scores
        let knn_scores = self.select_knn(&goal_features);

        let mut combined_scores: HashMap<PremiseId, f64> = knn_scores;

        if self.use_naive_bayes {
            let nb_scores = self.select_naive_bayes(&goal_features);

            // Normalize Naive Bayes scores to [0, 1]
            let nb_max = nb_scores
                .values()
                .copied()
                .fold(f64::NEG_INFINITY, f64::max);
            let nb_min = nb_scores.values().copied().fold(f64::INFINITY, f64::min);
            let nb_range = nb_max - nb_min;

            for (id, score) in nb_scores {
                let normalized = if nb_range > 0.0 {
                    (score - nb_min) / nb_range
                } else {
                    0.5
                };
                *combined_scores.entry(id).or_insert(0.0) += normalized;
            }
        }

        // Fallback: if no proof history, use feature similarity to premises
        if combined_scores.is_empty() {
            for premise in self.db.iter() {
                let sim = goal_features.jaccard(&premise.features);
                if sim > 0.0 {
                    combined_scores.insert(premise.id, sim);
                }
            }
        }

        // Sort by score (descending), then by premise ID for stability
        let mut scored: Vec<_> = combined_scores.into_iter().collect();
        scored.sort_by(|a, b| cmp_score_desc_then_id(a.1, a.0, b.1, b.0));

        scored
            .into_iter()
            .take(self.max_premises)
            .filter_map(|(id, _)| self.db.get(id))
            .collect()
    }
}

/// Combined premise selector using both MePo and MaSh
pub struct HybridSelector<'a> {
    db: &'a PremiseDatabase,
    /// Weight for MePo scores (0.0 to 1.0)
    mepo_weight: f64,
    /// Weight for MaSh scores (0.0 to 1.0)
    mash_weight: f64,
    /// Maximum premises to return
    max_premises: usize,
    /// Proof history for MaSh
    proof_history: Vec<ProofRecord>,
}

impl<'a> HybridSelector<'a> {
    /// Create a new hybrid selector
    pub fn new(db: &'a PremiseDatabase) -> Self {
        Self {
            db,
            mepo_weight: 0.5,
            mash_weight: 0.5,
            max_premises: 64,
            proof_history: Vec::new(),
        }
    }

    /// Set MePo weight
    #[must_use]
    pub fn with_mepo_weight(mut self, weight: f64) -> Self {
        self.mepo_weight = weight;
        self
    }

    /// Set MaSh weight
    #[must_use]
    pub fn with_mash_weight(mut self, weight: f64) -> Self {
        self.mash_weight = weight;
        self
    }

    /// Set maximum premises
    #[must_use]
    pub fn with_max_premises(mut self, max: usize) -> Self {
        self.max_premises = max;
        self
    }

    /// Record a successful proof
    pub fn record_proof(&mut self, goal: &Expr, useful_premises: Vec<PremiseId>) {
        let extractor = FeatureExtractor::new();
        let goal_features = extractor.extract(goal);
        self.proof_history.push(ProofRecord {
            goal_features,
            useful_premises,
        });
    }

    /// Select premises combining MePo and MaSh
    pub fn select(&self, goal: &Expr) -> Vec<&Premise> {
        let extractor = FeatureExtractor::new();
        let goal_features = extractor.extract(goal);
        let goal_constants = extractor.extract_constants(goal);

        let mut combined_scores: HashMap<PremiseId, f64> = HashMap::new();

        // MePo scoring
        if self.mepo_weight > 0.0 {
            let mepo = MePoSelector::new(self.db).with_threshold(0.0);
            for (premise, score) in mepo.select_with_scores(goal) {
                *combined_scores.entry(premise.id).or_insert(0.0) += self.mepo_weight * score;
            }
        }

        // MaSh scoring (k-NN component)
        if self.mash_weight > 0.0 && !self.proof_history.is_empty() {
            // Find similar past goals
            let mut neighbors: Vec<_> = self
                .proof_history
                .iter()
                .enumerate()
                .map(|(idx, record)| {
                    let sim = goal_features.jaccard(&record.goal_features);
                    (record, sim, idx)
                })
                .filter(|(_, sim, _)| *sim > 0.0)
                .collect();

            neighbors.sort_by(|a, b| match (a.1.is_nan(), b.1.is_nan()) {
                (true, true) => a.2.cmp(&b.2),
                (true, false) => Ordering::Greater,
                (false, true) => Ordering::Less,
                (false, false) => b.1.total_cmp(&a.1).then_with(|| a.2.cmp(&b.2)),
            });

            let k = 16.min(neighbors.len());
            for (record, sim, _) in neighbors.into_iter().take(k) {
                for &premise_id in &record.useful_premises {
                    *combined_scores.entry(premise_id).or_insert(0.0) += self.mash_weight * sim;
                }
            }
        }

        // Fallback: feature similarity to premises
        if combined_scores.is_empty() {
            for premise in self.db.iter() {
                let feat_sim = goal_features.jaccard(&premise.features);
                let const_overlap = premise.constants.intersection(&goal_constants).count() as f64
                    / (goal_constants.len().max(1)) as f64;
                let score = 0.5 * feat_sim + 0.5 * const_overlap;
                if score > 0.0 {
                    combined_scores.insert(premise.id, score);
                }
            }
        }

        // Sort by score (descending), then by premise ID for stability
        let mut scored: Vec<_> = combined_scores.into_iter().collect();
        scored.sort_by(|a, b| cmp_score_desc_then_id(a.1, a.0, b.1, b.0));

        scored
            .into_iter()
            .take(self.max_premises)
            .filter_map(|(id, _)| self.db.get(id))
            .collect()
    }
}
