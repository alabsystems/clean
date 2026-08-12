// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Batch SMT-backed proof search loop.
//!
//! Provides [`AutomationEngine::batch_prove`] for proving multiple goals in a
//! single call, sharing the environment setup cost while creating a fresh
//! [`SmtBridge`](crate::bridge::SmtBridge) per goal (required by the
//! single-shot contract, #2836).
//!
//! # Design
//!
//! Each goal gets its own `SmtBridge` instance because the bridge accumulates
//! solver clauses, lossy atoms, and hypothesis state that is not isolated per
//! goal. The batch loop amortizes engine construction and environment setup
//! while respecting this invariant.
//!
//! # Example
//!
//! ```text
//! use clean_auto::{AutomationEngine, AutomationQuery};
//! use std::time::Duration;
//!
//! let engine = AutomationEngine::new();
//! let timeout = Duration::from_secs(5);
//! let queries: Vec<AutomationQuery> = goals.iter()
//!     .map(|g| AutomationQuery::new(g, timeout))
//!     .collect();
//! let results = engine.batch_prove(&env, &queries);
//! assert_eq!(results.outcomes.len(), goals.len());
//! ```

use crate::engine::AutomationEngine;
use crate::engine_api::{AutomationOutcome, AutomationQuery};
use clean_kernel::Environment;
use std::time::Instant;

/// Summary statistics from a batch proof search run.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BatchProveStats {
    /// Total number of goals submitted.
    pub total: usize,
    /// Number of goals that received `Verified` outcomes.
    pub verified: usize,
    /// Number of goals that received `Refuted` outcomes.
    pub refuted: usize,
    /// Number of goals that received `Unverified` outcomes.
    pub unverified: usize,
    /// Number of goals that received `Unknown` outcomes.
    pub unknown: usize,
    /// Total wall-clock time for the entire batch in milliseconds.
    pub total_time_ms: u64,
}

impl BatchProveStats {
    /// Compute stats from a slice of outcomes.
    pub(crate) fn from_outcomes(outcomes: &[AutomationOutcome], total_time_ms: u64) -> Self {
        let mut verified = 0;
        let mut refuted = 0;
        let mut unverified = 0;
        let mut unknown = 0;
        for outcome in outcomes {
            match outcome {
                AutomationOutcome::Verified(_) => verified += 1,
                AutomationOutcome::Refuted { .. } => refuted += 1,
                AutomationOutcome::Unverified { .. } => unverified += 1,
                AutomationOutcome::Unknown { .. } => unknown += 1,
            }
        }
        Self {
            total: outcomes.len(),
            verified,
            refuted,
            unverified,
            unknown,
            total_time_ms,
        }
    }
}

/// Result of a batch proof search.
#[derive(Debug)]
pub struct BatchProveResult {
    /// Per-goal outcomes, in the same order as the input queries.
    pub outcomes: Vec<AutomationOutcome>,
    /// Aggregate statistics.
    pub stats: BatchProveStats,
}

impl AutomationEngine {
    /// Prove multiple goals in batch, sharing the engine across all queries.
    ///
    /// Each goal is proved independently with a fresh `SmtBridge` (per the
    /// single-shot contract). Goals are processed sequentially; future versions
    /// may parallelize across goals since `AutomationEngine` is `Send + Sync`.
    ///
    /// # Arguments
    ///
    /// * `env` - Shared kernel environment for all goals
    /// * `queries` - Slice of automation queries, one per goal
    ///
    /// # Returns
    ///
    /// A [`BatchProveResult`] containing per-goal outcomes and aggregate stats.
    ///
    /// # Example
    ///
    /// ```text
    /// let engine = AutomationEngine::new();
    /// let queries = vec![
    ///     AutomationQuery::new(&goal1, timeout),
    ///     AutomationQuery::new(&goal2, timeout).with_hypotheses(&hyps),
    /// ];
    /// let result = engine.batch_prove(&env, &queries);
    /// assert_eq!(result.outcomes.len(), 2);
    /// ```
    pub fn batch_prove<'a>(
        &self,
        env: &Environment,
        queries: &[AutomationQuery<'a>],
    ) -> BatchProveResult {
        let batch_start = Instant::now();
        let mut outcomes = Vec::with_capacity(queries.len());

        for query in queries {
            // Each query gets its own auto_prove_with_query call, which
            // internally creates a fresh SmtBridge (single-shot contract).
            let outcome = self.auto_prove_with_query(env, Self::reborrow_query(query));
            outcomes.push(outcome);
        }

        let total_time_ms = batch_start.elapsed().as_millis() as u64;
        let stats = BatchProveStats::from_outcomes(&outcomes, total_time_ms);

        BatchProveResult { outcomes, stats }
    }

    /// Reborrow a query reference into an owned `AutomationQuery` suitable for
    /// passing to `auto_prove_with_query`.
    ///
    /// This avoids requiring `AutomationQuery: Clone` (which would require
    /// `dyn ProofOracle: Clone`). Instead we reconstruct from the accessor
    /// methods on the borrowed query.
    fn reborrow_query<'a>(query: &'a AutomationQuery<'a>) -> AutomationQuery<'a> {
        let mut q = AutomationQuery::new(query.goal(), query.timeout());
        if let Some(ctx) = query.local_ctx() {
            q = q.with_local_ctx(ctx);
        }
        let hyps = query.hypotheses();
        if !hyps.is_empty() {
            q = q.with_hypotheses(hyps);
        }
        if let Some(db) = query.premise_db() {
            q = q.with_premise_db(db);
        }
        // Oracle fields are not exposed via public accessors on AutomationQuery,
        // so batch_prove does not forward oracle configuration. This is acceptable
        // because oracle calls are typically per-goal interactive requests, not
        // batch workloads. The SMT and superposition strategies are fully forwarded.
        q
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::engine_api::AutomationSource;
    use clean_kernel::env::Declaration;
    use clean_kernel::{Expr, Level, Name};
    use std::time::Duration;

    fn setup_env() -> Environment {
        let mut env = Environment::new();
        env.init_eq().expect("init_eq");
        env.init_nat().expect("init_nat");
        env.init_true_false().expect("init_true_false");
        env.init_classical().expect("init_classical");

        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        for name in ["a", "b", "c"] {
            env.add_decl(Declaration::Axiom {
                name: Name::from_string(name),
                level_params: vec![],
                type_: nat.clone(),
            })
            .unwrap_or_else(|_| panic!("add {name}"));
        }
        env
    }

    fn make_nat_eq(lhs: &Expr, rhs: &Expr) -> Expr {
        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                    nat,
                ),
                lhs.clone(),
            ),
            rhs.clone(),
        )
    }

    #[test]
    fn test_batch_prove_empty() {
        let env = setup_env();
        let engine = AutomationEngine::new();
        let result = engine.batch_prove(&env, &[]);
        assert_eq!(result.outcomes.len(), 0);
        assert_eq!(result.stats.total, 0);
        assert_eq!(result.stats.verified, 0);
    }

    #[test]
    fn test_batch_prove_single_reflexive() {
        let env = setup_env();
        let engine = AutomationEngine::new();
        let a = Expr::const_(Name::from_string("a"), vec![]);
        let goal = make_nat_eq(&a, &a);
        let timeout = Duration::from_secs(5);

        let queries = vec![AutomationQuery::new(&goal, timeout)];
        let result = engine.batch_prove(&env, &queries);

        assert_eq!(result.outcomes.len(), 1);
        assert!(
            matches!(result.outcomes[0], AutomationOutcome::Verified(_)),
            "reflexive equality should be verified, got: {:?}",
            result.outcomes[0]
        );
        assert_eq!(result.stats.total, 1);
        assert_eq!(result.stats.verified, 1);
    }

    #[test]
    fn test_batch_prove_multiple_goals() {
        let env = setup_env();
        let engine = AutomationEngine::new();
        let a = Expr::const_(Name::from_string("a"), vec![]);
        let b = Expr::const_(Name::from_string("b"), vec![]);
        let _c = Expr::const_(Name::from_string("c"), vec![]);
        let timeout = Duration::from_secs(5);

        // Goal 0: a = a (provable by reflexivity)
        let goal0 = make_nat_eq(&a, &a);
        // Goal 1: b = b (provable by reflexivity)
        let goal1 = make_nat_eq(&b, &b);
        // Goal 2: a = b (not provable without hypotheses — should be refuted)
        let goal2 = make_nat_eq(&a, &b);

        let queries = vec![
            AutomationQuery::new(&goal0, timeout),
            AutomationQuery::new(&goal1, timeout),
            AutomationQuery::new(&goal2, timeout),
        ];
        let result = engine.batch_prove(&env, &queries);

        assert_eq!(result.outcomes.len(), 3);
        assert!(
            matches!(result.outcomes[0], AutomationOutcome::Verified(_)),
            "a = a should be verified"
        );
        assert!(
            matches!(result.outcomes[1], AutomationOutcome::Verified(_)),
            "b = b should be verified"
        );
        // a = b without hypotheses: SMT should refute (find counterexample)
        assert!(
            matches!(
                result.outcomes[2],
                AutomationOutcome::Refuted { .. } | AutomationOutcome::Unknown { .. }
            ),
            "a = b without hypotheses should be refuted or unknown, got: {:?}",
            result.outcomes[2]
        );
        assert_eq!(result.stats.total, 3);
        assert_eq!(result.stats.verified, 2);
    }

    #[test]
    fn test_batch_prove_with_hypotheses() {
        let env = setup_env();
        let engine = AutomationEngine::new();
        let a = Expr::const_(Name::from_string("a"), vec![]);
        let b = Expr::const_(Name::from_string("b"), vec![]);
        let timeout = Duration::from_secs(5);

        // Goal: a = b, with hypothesis a = b
        let goal = make_nat_eq(&a, &b);
        let hypotheses = vec![(goal.clone(), None)];

        let queries = vec![AutomationQuery::new(&goal, timeout).with_hypotheses(&hypotheses)];
        let result = engine.batch_prove(&env, &queries);

        assert_eq!(result.outcomes.len(), 1);
        assert!(
            matches!(result.outcomes[0], AutomationOutcome::Verified(_)),
            "a = b with hypothesis a = b should be verified, got: {:?}",
            result.outcomes[0]
        );
        assert_eq!(result.stats.verified, 1);
    }

    #[test]
    fn test_batch_prove_stats_accuracy() {
        let outcomes = vec![
            AutomationOutcome::Verified(Box::new(crate::ProofResult::new(
                Expr::prop(),
                "test",
                0,
                None,
            ))),
            AutomationOutcome::Refuted {
                source: AutomationSource::Smt,
                time_ms: 1,
            },
            AutomationOutcome::Unknown {
                reason: "test".to_string(),
                source: AutomationSource::Smt,
                time_ms: 2,
            },
        ];
        let stats = BatchProveStats::from_outcomes(&outcomes, 100);
        assert_eq!(stats.total, 3);
        assert_eq!(stats.verified, 1);
        assert_eq!(stats.refuted, 1);
        assert_eq!(stats.unverified, 0);
        assert_eq!(stats.unknown, 1);
        assert_eq!(stats.total_time_ms, 100);
    }
}
