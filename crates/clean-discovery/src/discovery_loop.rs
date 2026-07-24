// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Main AI-driven discovery loop: candidate generation -> kernel verification
//! -> feedback -> next generation.
//!
//! Ties together all discovery infrastructure (candidate generators, batch
//! verifier, feedback analyzer, lemma library, tactic recommender) into a
//! single iterative loop that searches for novel mathematical theorems about
//! neural network verification.
//!
//! # Architecture
//!
//! ```text
//! ┌──────────────────────────────────────────────────────┐
//! │                   DiscoveryLoop                       │
//! │                                                      │
//! │  ┌─────────────┐    ┌──────────────┐                │
//! │  │  Candidate   │───>│ BatchVerifier │                │
//! │  │  Generator   │    │  (kernel)     │                │
//! │  └──────▲──────┘    └──────┬───────┘                │
//! │         │                   │                         │
//! │  ┌──────┴──────┐    ┌──────▼───────┐                │
//! │  │  Feedback    │<───│  Classifier  │                │
//! │  │  Loop        │    │  (feedback)  │                │
//! │  └──────┬──────┘    └──────────────┘                │
//! │         │                                            │
//! │  ┌──────▼──────┐    ┌──────────────┐                │
//! │  │  Lemma       │    │  Stats       │                │
//! │  │  Library     │    │  Tracker     │                │
//! │  └─────────────┘    └──────────────┘                │
//! └──────────────────────────────────────────────────────┘
//! ```
//!
//! Part of #3258.

use crate::candidate::CandidateTheorem;
use crate::discovery_stats::DiscoveryStats;
use crate::error::DiscoveryError;
use crate::feedback_loop::FeedbackLoop;
use crate::search::ExhaustiveSearch;
use clean_kernel::Environment;

/// Configuration for the discovery loop.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct DiscoveryLoopConfig {
    /// Maximum number of discovery iterations to run.
    pub max_iterations: u32,
    /// Number of candidates to generate per iteration.
    pub batch_size: usize,
    /// Whether to enable feedback-driven candidate refinement.
    pub feedback_enabled: bool,
    /// Maximum neighbor candidates to generate from each acceptance.
    pub max_neighbors_per_acceptance: usize,
    /// Rolling window size for statistics tracking.
    pub stats_window_size: usize,
    /// Number of threads for batch verification (None = rayon default).
    pub num_threads: Option<usize>,
}

impl Default for DiscoveryLoopConfig {
    fn default() -> Self {
        Self {
            max_iterations: 100,
            batch_size: 1000,
            feedback_enabled: true,
            max_neighbors_per_acceptance: 10,
            stats_window_size: 100,
            num_threads: None,
        }
    }
}

/// Result of a complete discovery loop run.
#[derive(Debug)]
#[non_exhaustive]
pub struct DiscoveryLoopResult {
    /// Total iterations completed.
    pub iterations_completed: u32,
    /// Total candidates evaluated across all iterations.
    pub total_candidates: u64,
    /// Total accepted (verified) theorems.
    pub total_accepted: u64,
    /// Total rejected candidates.
    pub total_rejected: u64,
    /// Overall throughput in candidates per second.
    pub throughput_per_sec: f64,
    /// Acceptance rate (0.0 to 1.0).
    pub acceptance_rate: f64,
    /// All verified theorem candidates.
    pub accepted_theorems: Vec<CandidateTheorem>,
}

/// The main AI-driven discovery loop.
///
/// Orchestrates iterative candidate generation, kernel verification,
/// and feedback-driven refinement. Each iteration:
///
/// 1. Takes a batch of candidate theorems (from initial set + feedback neighbors)
/// 2. Batch-verifies them against the kernel type-checker
/// 3. Collects accepted theorems and rejection feedback
/// 4. Uses feedback to generate refined candidates for the next iteration
/// 5. Tracks throughput and acceptance metrics
pub struct DiscoveryLoop<'a> {
    env: &'a Environment,
    config: DiscoveryLoopConfig,
    feedback: FeedbackLoop,
    stats: DiscoveryStats,
}

impl<'a> DiscoveryLoop<'a> {
    /// Create a new discovery loop with the given environment and configuration.
    pub fn new(env: &'a Environment, config: DiscoveryLoopConfig) -> Self {
        let stats = DiscoveryStats::new(config.stats_window_size);
        Self {
            env,
            config,
            feedback: FeedbackLoop::new(),
            stats,
        }
    }

    /// Run the discovery loop on an initial batch of candidates.
    ///
    /// Iterates until `max_iterations` is reached or no more candidates
    /// remain. Returns all verified theorems and aggregate statistics.
    pub fn run(
        &mut self,
        initial_candidates: Vec<CandidateTheorem>,
    ) -> Result<DiscoveryLoopResult, DiscoveryError> {
        if initial_candidates.is_empty() {
            return Err(DiscoveryError::NoCandidates {
                family: "discovery_loop".to_owned(),
            });
        }

        let mut accepted_theorems: Vec<CandidateTheorem> = Vec::new();
        let mut pending = initial_candidates;

        for _iteration in 0..self.config.max_iterations {
            if pending.is_empty() {
                break;
            }

            // Truncate to batch_size.
            pending.truncate(self.config.batch_size);

            let iter_start = std::time::Instant::now();

            // Verify the batch (genuine proof-proves-statement checking).
            let search_result = ExhaustiveSearch::run(self.env, &pending);
            let iter_time_ns = iter_start.elapsed().as_nanos() as u64;

            let accepted_count = search_result.stats.total_verified;
            let total_count = search_result.stats.total_evaluated;
            self.stats
                .record_iteration(total_count, accepted_count, iter_time_ns);

            // Process results: separate accepted from rejected.
            let mut next_candidates: Vec<CandidateTheorem> = Vec::new();

            for (candidate, outcome) in pending.iter().zip(search_result.outcomes.iter()) {
                if outcome.verified {
                    // Record accepted theorem.
                    accepted_theorems.push(candidate.clone());

                    // Feedback: generate neighbor candidates from acceptance.
                    if self.config.feedback_enabled {
                        let neighbors = self.feedback.process_acceptance(candidate);
                        let limit = self.config.max_neighbors_per_acceptance;
                        next_candidates.extend(neighbors.into_iter().take(limit));
                    }
                } else if self.config.feedback_enabled {
                    // Analyze rejection for feedback.
                    let _adjustment = self.feedback.process_rejection(outcome);
                    // Adjustments inform the next generation strategy but
                    // do not directly produce candidates here. The caller
                    // can query adjustment_summary() to guide external
                    // candidate generators.
                }
            }

            pending = next_candidates;
        }

        let report = self.stats.report();
        Ok(DiscoveryLoopResult {
            iterations_completed: self.stats.total_iterations() as u32,
            total_candidates: self.stats.total_candidates(),
            total_accepted: self.stats.total_accepted(),
            total_rejected: self
                .stats
                .total_candidates()
                .saturating_sub(self.stats.total_accepted()),
            throughput_per_sec: report.throughput_per_sec,
            acceptance_rate: report.acceptance_rate,
            accepted_theorems,
        })
    }

    /// Access the running statistics.
    #[must_use]
    pub fn stats(&self) -> &DiscoveryStats {
        &self.stats
    }

    /// Access the feedback loop state.
    #[must_use]
    pub fn feedback(&self) -> &FeedbackLoop {
        &self.feedback
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::candidate::{CandidateId, ParamVec, VerificationOutcome};
    use crate::family::TheoremFamily;
    use clean_kernel::{BinderInfo, Expr, Level};

    /// An environment with the NN-verify proof-complexity declarations, which
    /// include `ibp_cert_polynomial_axiom`. Tests that need GENUINELY verifiable
    /// candidates use this env so the kernel can confirm a real proof.
    fn pc_env() -> Environment {
        let mut env = Environment::new();
        env.init_nn_verify_proof_complexity()
            .expect("init proof complexity");
        env
    }

    /// Classify outcomes into accepted indices and rejected references.
    fn partition_outcomes(
        outcomes: &[VerificationOutcome],
    ) -> (Vec<usize>, Vec<&VerificationOutcome>) {
        let mut accepted = Vec::new();
        let mut rejected = Vec::new();
        for (idx, outcome) in outcomes.iter().enumerate() {
            if outcome.verified {
                accepted.push(idx);
            } else {
                rejected.push(outcome);
            }
        }
        (accepted, rejected)
    }

    /// A GENUINELY verifiable candidate: its statement is exactly the type of
    /// `ibp_cert_polynomial_axiom` and its proof is that axiom. The kernel
    /// confirms `proof : statement` via `is_def_eq`, so this is honestly
    /// accepted (only in a `pc_env`).
    fn make_valid_candidate(id: u64) -> CandidateTheorem {
        let nat = Expr::const_str("Nat");
        let ibp_cert = Expr::const_str("NNVerify.ProofComplexity.IBPCertificate");
        let ibp_cert_size = Expr::const_str("NNVerify.ProofComplexity.ibp_cert_size");
        let le_le = Expr::const_str_levels("LE.le", vec![Level::zero()]);
        let inst_le_nat = Expr::const_str("instLENat");
        let nat_mul = Expr::const_str("Nat.mul");

        // forall (d w : Nat) (cert : IBPCertificate),
        //   ibp_cert_size cert <= d * (w * w)
        let cert_sz = Expr::app(ibp_cert_size, Expr::bvar(0));
        let w_sq = Expr::apps(nat_mul.clone(), [Expr::bvar(1), Expr::bvar(1)]);
        let bound = Expr::apps(nat_mul, [Expr::bvar(2), w_sq]);
        let le_expr = Expr::apps(le_le, [nat.clone(), inst_le_nat, cert_sz, bound]);
        let body = Expr::pi(BinderInfo::Default, ibp_cert, le_expr);
        let body = Expr::pi(BinderInfo::Default, nat.clone(), body);
        let statement = Expr::pi(BinderInfo::Default, nat, body);

        CandidateTheorem {
            id: CandidateId(id),
            family: TheoremFamily::CertSizeBound,
            params: ParamVec::new(),
            statement,
            proof: Some(Expr::const_str(
                "NNVerify.ProofComplexity.ibp_cert_polynomial_axiom",
            )),
        }
    }

    fn make_invalid_candidate(id: u64) -> CandidateTheorem {
        // Proof references a non-existent constant -> cannot prove anything.
        CandidateTheorem {
            id: CandidateId(id),
            family: TheoremFamily::CertSizeBound,
            params: ParamVec::new(),
            statement: Expr::prop(),
            proof: Some(Expr::const_str("NonExistent.Const")),
        }
    }

    #[test]
    fn test_discovery_loop_empty_candidates_error() {
        let env = Environment::new();
        let config = DiscoveryLoopConfig::default();
        let mut dl = DiscoveryLoop::new(&env, config);

        let result = dl.run(Vec::new());
        assert!(result.is_err(), "empty candidates should return error");
    }

    #[test]
    fn test_discovery_loop_valid_candidates() {
        let env = pc_env();
        let config = DiscoveryLoopConfig {
            max_iterations: 1,
            batch_size: 10,
            feedback_enabled: false,
            num_threads: Some(1),
            ..DiscoveryLoopConfig::default()
        };
        let mut dl = DiscoveryLoop::new(&env, config);

        let candidates = vec![make_valid_candidate(0), make_valid_candidate(1)];
        let result = dl.run(candidates).expect("should succeed");

        assert_eq!(result.total_candidates, 2);
        assert_eq!(result.total_accepted, 2);
        assert_eq!(result.total_rejected, 0);
        assert_eq!(result.accepted_theorems.len(), 2);
        assert!(result.throughput_per_sec > 0.0);
    }

    #[test]
    fn test_discovery_loop_mixed_candidates() {
        let env = pc_env();
        let config = DiscoveryLoopConfig {
            max_iterations: 1,
            batch_size: 10,
            feedback_enabled: false,
            num_threads: Some(1),
            ..DiscoveryLoopConfig::default()
        };
        let mut dl = DiscoveryLoop::new(&env, config);

        let candidates = vec![
            make_valid_candidate(0),
            make_invalid_candidate(1),
            make_valid_candidate(2),
        ];
        let result = dl.run(candidates).expect("should succeed");

        assert_eq!(result.total_candidates, 3);
        assert_eq!(result.total_accepted, 2);
        assert_eq!(result.total_rejected, 1);
        assert_eq!(result.accepted_theorems.len(), 2);
    }

    #[test]
    fn test_discovery_loop_with_feedback() {
        let env = pc_env();
        let config = DiscoveryLoopConfig {
            max_iterations: 3,
            batch_size: 100,
            feedback_enabled: true,
            max_neighbors_per_acceptance: 5,
            num_threads: Some(1),
            ..DiscoveryLoopConfig::default()
        };
        let mut dl = DiscoveryLoop::new(&env, config);

        // Start with one valid and one invalid candidate.
        let candidates = vec![make_valid_candidate(0), make_invalid_candidate(1)];
        let result = dl.run(candidates).expect("should succeed");

        // At least 1 accepted from the initial batch.
        assert!(
            result.total_accepted >= 1,
            "should accept at least one theorem"
        );
        assert!(
            result.iterations_completed >= 1,
            "should complete at least one iteration"
        );
    }

    #[test]
    fn test_discovery_loop_stats_tracking() {
        let env = pc_env();
        let config = DiscoveryLoopConfig {
            max_iterations: 1,
            batch_size: 10,
            feedback_enabled: false,
            stats_window_size: 50,
            num_threads: Some(1),
            ..DiscoveryLoopConfig::default()
        };
        let mut dl = DiscoveryLoop::new(&env, config);

        let candidates = vec![make_valid_candidate(0)];
        let _result = dl.run(candidates).expect("should succeed");

        let stats = dl.stats();
        assert_eq!(stats.total_iterations(), 1);
        assert_eq!(stats.total_candidates(), 1);
        assert_eq!(stats.total_accepted(), 1);
        assert!((stats.acceptance_rate() - 1.0).abs() < 1e-9);
    }

    #[test]
    fn test_partition_outcomes() {
        let outcomes = vec![
            VerificationOutcome {
                candidate_id: CandidateId(0),
                verified: true,
                inferred_type: None,
                error: None,
                time_ns: 50,
            },
            VerificationOutcome {
                candidate_id: CandidateId(1),
                verified: false,
                inferred_type: None,
                error: Some("error".to_owned()),
                time_ns: 100,
            },
            VerificationOutcome {
                candidate_id: CandidateId(2),
                verified: true,
                inferred_type: None,
                error: None,
                time_ns: 60,
            },
        ];

        let (accepted, rejected) = partition_outcomes(&outcomes);
        assert_eq!(accepted, vec![0, 2]);
        assert_eq!(rejected.len(), 1);
        assert_eq!(rejected[0].candidate_id, CandidateId(1));
    }

    #[test]
    fn test_discovery_loop_config_default() {
        let config = DiscoveryLoopConfig::default();
        assert_eq!(config.max_iterations, 100);
        assert_eq!(config.batch_size, 1000);
        assert!(config.feedback_enabled);
    }
}
