// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Novelty filtering and interest scoring for verified candidates.
//!
//! After the kernel accepts a candidate theorem, the `NoveltyFilter` checks
//! whether it is structurally distinct from previously seen results and
//! scores its mathematical interest based on bound tightness, parameter
//! novelty, and proof compactness.
//!
//! Part of #3272.

use crate::candidate::CandidateTheorem;
use crate::scoring;

/// Novelty and interest scores for a verified candidate theorem.
#[derive(Debug, Clone, PartialEq)]
pub struct NoveltyScore {
    /// How tight the bound is (Linear > QuadraticWidth > QuadraticDepth > QuadraticBoth).
    /// Range: 0.0 (loosest) to 1.0 (tightest).
    pub bound_tightness: f64,
    /// How unusual the parameter combination is.
    /// Range: 0.0 (common) to 1.0 (rare).
    pub parameter_novelty: f64,
    /// How compact the proof term is (fewer nodes = higher score).
    /// Range: 0.0 (large) to 1.0 (minimal).
    pub proof_compactness: f64,
    /// Weighted total score.
    pub total: f64,
}

/// Weight constants for the total score computation.
const WEIGHT_BOUND_TIGHTNESS: f64 = 0.5;
const WEIGHT_PARAMETER_NOVELTY: f64 = 0.2;
const WEIGHT_PROOF_COMPACTNESS: f64 = 0.3;

/// Filters duplicate theorems and ranks candidates by mathematical interest.
pub struct NoveltyFilter;

impl NoveltyFilter {
    /// Create a new novelty filter.
    #[must_use]
    pub fn new() -> Self {
        Self
    }

    /// Check if a candidate theorem is structurally equivalent to any
    /// existing theorem in the collection.
    ///
    /// Uses the `Debug` representation of the statement `Expr` as a proxy
    /// for alpha-equivalence. This is sound (if Debug strings differ, the
    /// exprs differ) and conservative (some alpha-equivalent exprs may have
    /// different Debug output, but we err on the side of keeping both).
    #[must_use]
    pub fn is_duplicate(&self, theorem: &CandidateTheorem, existing: &[CandidateTheorem]) -> bool {
        let stmt_repr = format!("{:?}", theorem.statement);
        existing
            .iter()
            .any(|other| format!("{:?}", other.statement) == stmt_repr)
    }

    /// Score the mathematical interest of a single candidate theorem.
    #[must_use]
    pub fn score(&self, theorem: &CandidateTheorem) -> NoveltyScore {
        let bound_tightness = scoring::score_bound_tightness(theorem);
        let parameter_novelty = scoring::score_parameter_novelty(theorem);
        let proof_compactness = scoring::score_proof_compactness(theorem);

        let total = WEIGHT_BOUND_TIGHTNESS * bound_tightness
            + WEIGHT_PARAMETER_NOVELTY * parameter_novelty
            + WEIGHT_PROOF_COMPACTNESS * proof_compactness;

        NoveltyScore {
            bound_tightness,
            parameter_novelty,
            proof_compactness,
            total,
        }
    }

    /// Deduplicate candidates and rank them by novelty score.
    ///
    /// Returns a vector of `(original_index, score)` pairs sorted by
    /// descending total score. Duplicates are removed (only the first
    /// occurrence is kept).
    #[must_use]
    pub fn filter_and_rank(&self, candidates: &[CandidateTheorem]) -> Vec<(usize, NoveltyScore)> {
        let mut seen_stmts: Vec<String> = Vec::new();
        let mut unique: Vec<(usize, NoveltyScore)> = Vec::new();

        for (idx, candidate) in candidates.iter().enumerate() {
            let stmt_repr = format!("{:?}", candidate.statement);
            if seen_stmts.contains(&stmt_repr) {
                continue;
            }
            seen_stmts.push(stmt_repr);
            let score = self.score(candidate);
            unique.push((idx, score));
        }

        // Sort by descending total score.
        unique.sort_by(|a, b| {
            b.1.total
                .partial_cmp(&a.1.total)
                .unwrap_or(std::cmp::Ordering::Equal)
        });

        unique
    }
}

impl Default for NoveltyFilter {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::candidate::{CandidateId, ParamValue, ParamVec};
    use crate::family::TheoremFamily;
    use clean_kernel::Expr;

    fn make_candidate(
        id: u64,
        family: TheoremFamily,
        params: ParamVec,
        statement: Expr,
        proof: Option<Expr>,
    ) -> CandidateTheorem {
        CandidateTheorem {
            id: CandidateId(id),
            family,
            params,
            statement,
            proof,
        }
    }

    #[test]
    fn test_duplicate_detection_same_statement() {
        let filter = NoveltyFilter::new();
        let stmt = Expr::prop();
        let c1 = make_candidate(
            0,
            TheoremFamily::CertSizeBound,
            ParamVec::new(),
            stmt.clone(),
            None,
        );
        let c2 = make_candidate(1, TheoremFamily::CertSizeBound, ParamVec::new(), stmt, None);
        assert!(
            filter.is_duplicate(&c2, &[c1]),
            "same statement should be detected as duplicate"
        );
    }

    #[test]
    fn test_duplicate_detection_different_statement() {
        let filter = NoveltyFilter::new();
        let c1 = make_candidate(
            0,
            TheoremFamily::CertSizeBound,
            ParamVec::new(),
            Expr::prop(),
            None,
        );
        let c2 = make_candidate(
            1,
            TheoremFamily::CertSizeBound,
            ParamVec::new(),
            Expr::type_(),
            None,
        );
        assert!(
            !filter.is_duplicate(&c2, &[c1]),
            "different statements should not be duplicates"
        );
    }

    #[test]
    fn test_duplicate_detection_empty_existing() {
        let filter = NoveltyFilter::new();
        let c = make_candidate(
            0,
            TheoremFamily::CertSizeBound,
            ParamVec::new(),
            Expr::prop(),
            None,
        );
        assert!(
            !filter.is_duplicate(&c, &[]),
            "should not be duplicate with empty existing set"
        );
    }

    #[test]
    fn test_score_linear_bound_higher_than_quadratic() {
        let filter = NoveltyFilter::new();
        let linear = make_candidate(
            0,
            TheoremFamily::CertSizeBound,
            ParamVec(vec![
                ParamValue::Choice(0),
                ParamValue::Nat(1),
                ParamValue::Nat(2),
                ParamValue::Nat(2),
            ]),
            Expr::prop(),
            None,
        );
        let quadratic = make_candidate(
            1,
            TheoremFamily::CertSizeBound,
            ParamVec(vec![
                ParamValue::Choice(3),
                ParamValue::Nat(1),
                ParamValue::Nat(2),
                ParamValue::Nat(2),
            ]),
            Expr::prop(),
            None,
        );
        let linear_score = filter.score(&linear);
        let quad_score = filter.score(&quadratic);
        assert!(
            linear_score.bound_tightness > quad_score.bound_tightness,
            "linear ({}) > quadratic ({})",
            linear_score.bound_tightness,
            quad_score.bound_tightness
        );
    }

    #[test]
    fn test_score_lower_c_higher_tightness() {
        let filter = NoveltyFilter::new();
        let low_c = make_candidate(
            0,
            TheoremFamily::CertSizeBound,
            ParamVec(vec![
                ParamValue::Choice(1),
                ParamValue::Nat(1),
                ParamValue::Nat(2),
                ParamValue::Nat(2),
            ]),
            Expr::prop(),
            None,
        );
        let high_c = make_candidate(
            1,
            TheoremFamily::CertSizeBound,
            ParamVec(vec![
                ParamValue::Choice(1),
                ParamValue::Nat(5),
                ParamValue::Nat(2),
                ParamValue::Nat(2),
            ]),
            Expr::prop(),
            None,
        );
        let low_c_score = filter.score(&low_c);
        let high_c_score = filter.score(&high_c);
        assert!(
            low_c_score.bound_tightness > high_c_score.bound_tightness,
            "C=1 ({}) > C=5 ({})",
            low_c_score.bound_tightness,
            high_c_score.bound_tightness
        );
    }

    #[test]
    fn test_filter_and_rank_removes_duplicates() {
        let filter = NoveltyFilter::new();
        let stmt = Expr::prop();
        let candidates = vec![
            make_candidate(
                0,
                TheoremFamily::CertSizeBound,
                ParamVec::new(),
                stmt.clone(),
                None,
            ),
            make_candidate(1, TheoremFamily::CertSizeBound, ParamVec::new(), stmt, None),
            make_candidate(
                2,
                TheoremFamily::CertSizeBound,
                ParamVec::new(),
                Expr::type_(),
                None,
            ),
        ];
        let ranked = filter.filter_and_rank(&candidates);
        assert_eq!(ranked.len(), 2, "should have 2 unique after dedup");
    }

    #[test]
    fn test_filter_and_rank_sorted_by_score() {
        let filter = NoveltyFilter::new();
        let candidates = vec![
            make_candidate(
                0,
                TheoremFamily::CertSizeBound,
                ParamVec(vec![
                    ParamValue::Choice(3),
                    ParamValue::Nat(5),
                    ParamValue::Nat(1),
                    ParamValue::Nat(1),
                ]),
                Expr::prop(),
                None,
            ),
            make_candidate(
                1,
                TheoremFamily::CertSizeBound,
                ParamVec(vec![
                    ParamValue::Choice(0),
                    ParamValue::Nat(1),
                    ParamValue::Nat(5),
                    ParamValue::Nat(5),
                ]),
                Expr::type_(),
                None,
            ),
        ];
        let ranked = filter.filter_and_rank(&candidates);
        assert_eq!(ranked.len(), 2);
        assert_eq!(ranked[0].0, 1, "linear bound candidate should rank first");
    }

    #[test]
    fn test_proof_compactness_smaller_scores_higher() {
        let filter = NoveltyFilter::new();
        let params = ParamVec(vec![
            ParamValue::Choice(0),
            ParamValue::Nat(1),
            ParamValue::Nat(2),
            ParamValue::Nat(2),
        ]);
        let small_proof = make_candidate(
            0,
            TheoremFamily::CertSizeBound,
            params.clone(),
            Expr::prop(),
            Some(Expr::const_str("small")),
        );
        let large_proof = make_candidate(
            1,
            TheoremFamily::CertSizeBound,
            params,
            Expr::prop(),
            Some(Expr::apps(
                Expr::const_str("f"),
                [
                    Expr::app(Expr::const_str("g"), Expr::const_str("a")),
                    Expr::app(Expr::const_str("h"), Expr::const_str("b")),
                ],
            )),
        );
        let small_score = filter.score(&small_proof);
        let large_score = filter.score(&large_proof);
        assert!(
            small_score.proof_compactness > large_score.proof_compactness,
            "small ({}) > large ({})",
            small_score.proof_compactness,
            large_score.proof_compactness
        );
    }

    #[test]
    fn test_score_total_is_weighted_sum() {
        let filter = NoveltyFilter::new();
        let candidate = make_candidate(
            0,
            TheoremFamily::CertSizeBound,
            ParamVec(vec![
                ParamValue::Choice(0),
                ParamValue::Nat(1),
                ParamValue::Nat(2),
                ParamValue::Nat(2),
            ]),
            Expr::prop(),
            None,
        );
        let score = filter.score(&candidate);
        let expected = WEIGHT_BOUND_TIGHTNESS * score.bound_tightness
            + WEIGHT_PARAMETER_NOVELTY * score.parameter_novelty
            + WEIGHT_PROOF_COMPACTNESS * score.proof_compactness;
        assert!(
            (score.total - expected).abs() < 1e-10,
            "total ({}) == weighted sum ({})",
            score.total,
            expected
        );
    }

    #[test]
    fn test_filter_and_rank_empty() {
        let filter = NoveltyFilter::new();
        assert!(filter.filter_and_rank(&[]).is_empty());
    }

    #[test]
    fn test_non_cert_size_family_neutral_tightness() {
        let filter = NoveltyFilter::new();
        let candidate = make_candidate(
            0,
            TheoremFamily::DomainTightness,
            ParamVec::new(),
            Expr::prop(),
            None,
        );
        let score = filter.score(&candidate);
        assert!(
            (score.bound_tightness - 0.5).abs() < 1e-10,
            "non-CertSizeBound should get 0.5, got {}",
            score.bound_tightness
        );
    }
}
