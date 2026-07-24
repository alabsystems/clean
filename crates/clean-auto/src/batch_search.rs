// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Batched SMT proof search with in-process ay refinement.

use crate::engine::AutomationEngine;
use crate::engine_api::{AutomationOutcome, AutomationQuery};
use crate::proof_result::build_hypothesis_proof_context;
use crate::ProofResult;
use clean_kernel::Environment;
use std::cmp::Reverse;
use std::time::Instant;

/// Goal entry inside a batch query.
pub struct BatchGoal<'a> {
    /// Goal and context to prove.
    pub query: AutomationQuery<'a>,
    /// Higher values are scheduled earlier by [`SearchStrategy::Priority`].
    pub priority: u32,
}

impl<'a> BatchGoal<'a> {
    /// Create a batch goal with default priority.
    pub fn new(query: AutomationQuery<'a>) -> Self {
        Self { query, priority: 0 }
    }

    /// Override the goal priority.
    pub fn with_priority(mut self, priority: u32) -> Self {
        self.priority = priority;
        self
    }
}

/// Batch request for multiple SMT-backed goals.
pub struct BatchQuery<'a> {
    /// Goals to prove.
    pub goals: Vec<BatchGoal<'a>>,
    /// Goal scheduling policy inside each iteration.
    pub strategy: SearchStrategy,
    /// Maximum solve attempts per goal.
    pub max_iterations: usize,
    /// Initial SMT instantiation-round budget per goal.
    pub initial_smt_rounds: u32,
    /// Increment applied to unresolved goals after each iteration.
    pub refinement_step: u32,
    /// Per-goal cap on SMT instantiation rounds.
    pub max_smt_rounds: u32,
}

impl<'a> BatchQuery<'a> {
    /// Create a batch query with conservative defaults.
    pub fn new(goals: Vec<BatchGoal<'a>>) -> Self {
        Self {
            goals,
            strategy: SearchStrategy::BreadthFirst,
            max_iterations: 3,
            initial_smt_rounds: 8,
            refinement_step: 8,
            max_smt_rounds: 64,
        }
    }

    pub fn with_strategy(mut self, strategy: SearchStrategy) -> Self {
        self.strategy = strategy;
        self
    }

    pub fn with_max_iterations(mut self, max_iterations: usize) -> Self {
        self.max_iterations = max_iterations.max(1);
        self
    }

    pub fn with_initial_smt_rounds(mut self, rounds: u32) -> Self {
        self.initial_smt_rounds = rounds.max(1);
        self
    }

    pub fn with_refinement_step(mut self, step: u32) -> Self {
        self.refinement_step = step;
        self
    }

    pub fn with_max_smt_rounds(mut self, rounds: u32) -> Self {
        self.max_smt_rounds = rounds.max(1);
        self
    }
}

/// Goal ordering policy for the batch loop.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SearchStrategy {
    BreadthFirst,
    DepthFirst,
    Priority,
}

/// Final per-goal status from batch search.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BatchGoalStatus {
    Proved,
    Disproved,
    Unknown,
    Timeout,
}

/// Final outcome for one goal in the batch.
#[derive(Debug)]
pub struct BatchGoalResult {
    pub status: BatchGoalStatus,
    pub proof: Option<ProofResult>,
    pub reason: Option<String>,
    pub attempts: usize,
}

/// Result of a full batch search run.
#[derive(Debug)]
pub struct BatchResult {
    pub goals: Vec<BatchGoalResult>,
    pub iterations: usize,
}

/// Stateful batch SMT loop.
pub struct BatchSearchLoop<'a> {
    batch: BatchQuery<'a>,
}

impl<'a> BatchSearchLoop<'a> {
    pub fn new(batch: BatchQuery<'a>) -> Self {
        Self { batch }
    }

    /// Run the real SMT-backed loop using `AutomationEngine::try_smt_detailed`.
    pub fn run(self, engine: &AutomationEngine, env: &Environment) -> BatchResult {
        let max_smt_rounds = self.batch.max_smt_rounds.min(engine.max_smt_rounds).max(1);
        self.run_with(max_smt_rounds, |goal| solve_pending_goal(engine, env, goal))
    }

    fn run_with<F>(self, max_smt_rounds: u32, mut submit: F) -> BatchResult
    where
        F: FnMut(&PendingGoal<'a>) -> RoundOutcome,
    {
        let strategy = self.batch.strategy;
        let max_iterations = self.batch.max_iterations.max(1);
        let refinement_step = self.batch.refinement_step;
        let initial_smt_rounds = self.batch.initial_smt_rounds.min(max_smt_rounds).max(1);
        let goal_count = self.batch.goals.len();
        let mut goals = (0..goal_count).map(|_| None).collect::<Vec<_>>();
        let mut pending = self
            .batch
            .goals
            .into_iter()
            .enumerate()
            .map(|(index, goal)| PendingGoal {
                index,
                goal,
                attempts: 0,
                smt_rounds: initial_smt_rounds,
            })
            .collect::<Vec<_>>();
        let mut iterations = 0;

        while !pending.is_empty() {
            iterations += 1;
            order_pending(&mut pending, strategy);
            let mut next_pending = Vec::new();

            for mut goal in pending.into_iter() {
                let index = goal.index;
                let outcome = submit(&goal);
                goal.attempts += 1;
                goals[index] = match outcome {
                    RoundOutcome::Proved(proof) => Some(BatchGoalResult {
                        status: BatchGoalStatus::Proved,
                        proof: Some(proof),
                        reason: None,
                        attempts: goal.attempts,
                    }),
                    RoundOutcome::Disproved => Some(BatchGoalResult {
                        status: BatchGoalStatus::Disproved,
                        proof: None,
                        reason: None,
                        attempts: goal.attempts,
                    }),
                    RoundOutcome::Timeout(reason) => Some(BatchGoalResult {
                        status: BatchGoalStatus::Timeout,
                        proof: None,
                        reason: Some(reason),
                        attempts: goal.attempts,
                    }),
                    RoundOutcome::Unknown { reason, terminal } => {
                        if terminal {
                            Some(BatchGoalResult {
                                status: BatchGoalStatus::Unknown,
                                proof: None,
                                reason: Some(reason),
                                attempts: goal.attempts,
                            })
                        } else if goal.attempts >= max_iterations {
                            Some(timeout_result(goal.attempts, goal.smt_rounds, reason))
                        } else if let Some(next_rounds) =
                            next_smt_rounds(goal.smt_rounds, refinement_step, max_smt_rounds)
                        {
                            goal.smt_rounds = next_rounds;
                            goal.goal.priority = goal.goal.priority.saturating_add(1);
                            next_pending.push(goal);
                            None
                        } else {
                            Some(timeout_result(goal.attempts, goal.smt_rounds, reason))
                        }
                    }
                };
            }

            pending = next_pending;
        }

        BatchResult {
            goals: goals
                .into_iter()
                .map(|goal| {
                    goal.unwrap_or(BatchGoalResult {
                        status: BatchGoalStatus::Unknown,
                        proof: None,
                        reason: Some("batch goal was not processed".to_string()),
                        attempts: 0,
                    })
                })
                .collect(),
            iterations,
        }
    }
}

/// Orchestrate the batch SMT search loop.
pub fn batch_prove<'a>(
    engine: &AutomationEngine,
    env: &Environment,
    batch: BatchQuery<'a>,
) -> BatchResult {
    BatchSearchLoop::new(batch).run(engine, env)
}

struct PendingGoal<'a> {
    index: usize,
    goal: BatchGoal<'a>,
    attempts: usize,
    smt_rounds: u32,
}

#[derive(Debug)]
enum RoundOutcome {
    Proved(ProofResult),
    Disproved,
    Unknown { reason: String, terminal: bool },
    Timeout(String),
}

fn solve_pending_goal(
    engine: &AutomationEngine,
    env: &Environment,
    goal: &PendingGoal<'_>,
) -> RoundOutcome {
    if goal.goal.query.timeout().is_zero() {
        return RoundOutcome::Timeout("goal timeout exhausted before SMT submission".to_string());
    }

    let smt_engine = AutomationEngine::with_config(goal.smt_rounds.min(engine.max_smt_rounds));
    let (hypotheses, proof_context) =
        build_hypothesis_proof_context(goal.goal.query.hypotheses, goal.goal.query.local_ctx);
    // Phase-0 solver-cache obligation key (goal-type digest); only computed when
    // the telemetry sink is enabled, so the default path pays nothing.
    let obligation = if crate::solver_cache::telemetry::is_enabled() {
        crate::solver_cache::obligation_digest(goal.goal.query.goal).ok()
    } else {
        None
    };
    let start = Instant::now();
    match smt_engine.try_smt_detailed(
        env,
        goal.goal.query.goal,
        &hypotheses,
        goal.goal.query.premise_db,
        proof_context.as_ref(),
        start,
        obligation.as_deref(),
        start,
    ) {
        AutomationOutcome::Verified(proof) => RoundOutcome::Proved(*proof),
        AutomationOutcome::Refuted { .. } => RoundOutcome::Disproved,
        AutomationOutcome::Unverified { reason, .. } => RoundOutcome::Unknown {
            reason,
            terminal: true,
        },
        AutomationOutcome::Unknown { reason, .. } if is_timeout_reason(&reason) => {
            RoundOutcome::Timeout(reason)
        }
        AutomationOutcome::Unknown { reason, .. } => RoundOutcome::Unknown {
            reason,
            terminal: false,
        },
    }
}

fn order_pending(pending: &mut [PendingGoal<'_>], strategy: SearchStrategy) {
    match strategy {
        SearchStrategy::BreadthFirst => {
            pending.sort_by_key(|goal| (goal.attempts, Reverse(goal.goal.priority), goal.index))
        }
        SearchStrategy::DepthFirst => pending.sort_by_key(|goal| {
            (
                Reverse(goal.attempts),
                Reverse(goal.goal.priority),
                goal.index,
            )
        }),
        SearchStrategy::Priority => {
            pending.sort_by_key(|goal| (Reverse(goal.goal.priority), goal.attempts, goal.index))
        }
    }
}

fn next_smt_rounds(current: u32, step: u32, max_smt_rounds: u32) -> Option<u32> {
    let next = current.saturating_add(step).min(max_smt_rounds);
    (next > current).then_some(next)
}

fn timeout_result(attempts: usize, smt_rounds: u32, reason: String) -> BatchGoalResult {
    BatchGoalResult {
        status: BatchGoalStatus::Timeout,
        proof: None,
        reason: Some(format!(
            "batch SMT search exhausted after {attempts} attempt(s) at {smt_rounds} round(s): {reason}"
        )),
        attempts,
    }
}

fn is_timeout_reason(reason: &str) -> bool {
    reason.to_ascii_lowercase().contains("timeout")
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::{Environment, Expr, Name};
    use std::time::Duration;

    fn mock_goal<'a>(goal: &'a Expr, priority: u32) -> BatchGoal<'a> {
        BatchGoal::new(AutomationQuery::new(goal, Duration::from_secs(1))).with_priority(priority)
    }

    fn fake_proof(text: &str) -> ProofResult {
        ProofResult::new(Expr::prop(), text, 0, None)
    }

    #[test]
    fn test_refines_unsolved_goal_until_proved() {
        let goal = Expr::prop();
        let batch = BatchQuery::new(vec![mock_goal(&goal, 0)])
            .with_max_iterations(3)
            .with_initial_smt_rounds(1)
            .with_refinement_step(2)
            .with_max_smt_rounds(5);
        let mut seen_rounds = Vec::new();

        let result = BatchSearchLoop::new(batch).run_with(5, |pending| {
            seen_rounds.push(pending.smt_rounds);
            if pending.smt_rounds < 3 {
                RoundOutcome::Unknown {
                    reason: "keep refining".to_string(),
                    terminal: false,
                }
            } else {
                RoundOutcome::Proved(fake_proof("ay"))
            }
        });

        assert_eq!(seen_rounds, vec![1, 3]);
        assert_eq!(result.iterations, 2);
        assert_eq!(result.goals[0].status, BatchGoalStatus::Proved);
        assert_eq!(result.goals[0].attempts, 2);
        assert_eq!(
            result.goals[0]
                .proof
                .as_ref()
                .expect("proof should exist")
                .proof_text(),
            "ay"
        );
    }

    #[test]
    fn test_marks_timeout_when_refinement_budget_exhausted() {
        let goal = Expr::prop();
        let batch = BatchQuery::new(vec![mock_goal(&goal, 0)])
            .with_max_iterations(2)
            .with_initial_smt_rounds(1)
            .with_refinement_step(1)
            .with_max_smt_rounds(2);

        let result = BatchSearchLoop::new(batch).run_with(2, |_| RoundOutcome::Unknown {
            reason: "still unknown".to_string(),
            terminal: false,
        });

        assert_eq!(result.goals[0].status, BatchGoalStatus::Timeout);
        assert_eq!(result.goals[0].attempts, 2);
    }

    #[test]
    fn test_terminal_unknown_skips_refinement() {
        let goal = Expr::prop();
        let batch = BatchQuery::new(vec![mock_goal(&goal, 0)]);

        let result = BatchSearchLoop::new(batch).run_with(64, |_| RoundOutcome::Unknown {
            reason: "reconstruction unavailable".to_string(),
            terminal: true,
        });

        assert_eq!(result.iterations, 1);
        assert_eq!(result.goals[0].status, BatchGoalStatus::Unknown);
        assert_eq!(result.goals[0].attempts, 1);
    }

    #[test]
    fn test_order_pending_respects_strategy() {
        let goal = Expr::prop();
        let mk_pending = |index, attempts, priority| PendingGoal {
            index,
            goal: mock_goal(&goal, priority),
            attempts,
            smt_rounds: 1,
        };

        let mut breadth = vec![
            mk_pending(0, 2, 0),
            mk_pending(1, 0, 1),
            mk_pending(2, 1, 0),
        ];
        order_pending(&mut breadth, SearchStrategy::BreadthFirst);
        assert_eq!(
            breadth.iter().map(|goal| goal.index).collect::<Vec<_>>(),
            vec![1, 2, 0]
        );

        let mut depth = vec![
            mk_pending(0, 2, 0),
            mk_pending(1, 0, 1),
            mk_pending(2, 1, 0),
        ];
        order_pending(&mut depth, SearchStrategy::DepthFirst);
        assert_eq!(
            depth.iter().map(|goal| goal.index).collect::<Vec<_>>(),
            vec![0, 2, 1]
        );

        let mut priority = vec![
            mk_pending(0, 0, 1),
            mk_pending(1, 2, 3),
            mk_pending(2, 1, 2),
        ];
        order_pending(&mut priority, SearchStrategy::Priority);
        assert_eq!(
            priority.iter().map(|goal| goal.index).collect::<Vec<_>>(),
            vec![1, 2, 0]
        );
    }
    #[test]
    fn test_batch_prove_empty_batch() {
        let env = Environment::new();
        let result = batch_prove(&AutomationEngine::new(), &env, BatchQuery::new(vec![]));
        assert!(result.goals.is_empty());
        assert_eq!(result.iterations, 0);
    }
    #[test]
    fn test_batch_prove_single_query() {
        let env = Environment::new();
        let goal = Expr::const_(Name::from_string("False"), vec![]);
        let result = batch_prove(
            &AutomationEngine::new(),
            &env,
            BatchQuery::new(vec![BatchGoal::new(AutomationQuery::new(
                &goal,
                Duration::from_secs(1),
            ))]),
        );
        assert_eq!(result.goals[0].status, BatchGoalStatus::Disproved);
        assert_eq!(result.goals[0].attempts, 1);
    }

    #[test]
    fn test_batch_prove_timeout_handling() {
        let env = Environment::new();
        let goal = Expr::const_(Name::from_string("False"), vec![]);
        let result = batch_prove(
            &AutomationEngine::new(),
            &env,
            BatchQuery::new(vec![BatchGoal::new(AutomationQuery::new(
                &goal,
                Duration::ZERO,
            ))]),
        );
        assert_eq!(result.goals[0].status, BatchGoalStatus::Timeout);
        assert_eq!(result.goals[0].attempts, 1);
        assert!(result.goals[0]
            .reason
            .as_ref()
            .is_some_and(|r| r.contains("timeout")));
    }
}
