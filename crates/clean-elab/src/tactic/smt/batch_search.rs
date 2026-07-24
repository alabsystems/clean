// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
#![allow(dead_code)]

//! Batched SMT proof search infrastructure.
//!
//! Each goal in the batch gets its own fresh Ay solver instance so solver
//! state does not leak across goals. Goals are processed in chunks bounded by
//! `batch_size`, which limits how many solver workers run concurrently.

use super::ay_solver::{create_smt_backend, SmtProveOutcome};
use super::ay_types::AyConfig;
use crate::tactic::LocalDecl;
use crate::unify::MetaState;
use clean_auto::bridge::ay_contract::{AyError, AyLogic};
use clean_kernel::Expr;
use std::any::Any;

/// Instantiated SMT batch goal input: `(goal_expr, local_context)`.
pub(crate) type BatchSmtGoal = (Expr, Vec<LocalDecl>);

/// SMT proof result returned by batch search.
pub(crate) type SmtProof = SmtProveOutcome;

/// SMT error returned by batch search.
pub(crate) type SmtError = AyError;

/// Run SMT proof search over a batch of goals.
///
/// The search reuses the existing single-goal `SmtSolver` integration by
/// creating one solver per goal, registering the local context, asserting
/// supported hypotheses, and proving the target expression.
#[derive(Debug, Clone)]
pub(crate) struct BatchSmtSearch {
    config: AyConfig,
    logic: AyLogic,
    batch_size: usize,
}

impl BatchSmtSearch {
    /// Default maximum number of concurrently active solver workers.
    pub(crate) const DEFAULT_BATCH_SIZE: usize = 16;

    #[must_use]
    pub(crate) fn new(config: AyConfig, logic: AyLogic) -> Self {
        Self {
            config,
            logic,
            batch_size: Self::DEFAULT_BATCH_SIZE,
        }
    }

    #[must_use]
    pub(crate) fn batch_size(&self) -> usize {
        self.batch_size
    }

    #[must_use]
    pub(crate) fn with_batch_size(mut self, batch_size: usize) -> Self {
        self.batch_size = batch_size.max(1);
        self
    }

    /// Search a batch of already-instantiated goals.
    ///
    /// REQUIRES: `goals` and each declaration type/value have already had
    /// metavariables instantiated for the current proof state.
    /// ENSURES: Returns one result per input goal, preserving input order.
    /// ENSURES: Each goal is solved with a fresh solver instance.
    pub(crate) fn search(&self, goals: Vec<BatchSmtGoal>) -> Vec<Result<SmtProof, SmtError>> {
        self.run_batch(goals)
    }

    /// Search a batch of goals after instantiating each goal/local context
    /// with the provided metavariable assignments.
    ///
    /// ENSURES: Preserves input order.
    /// ENSURES: Equivalent to instantiating each batch goal and calling
    /// `search` on the resulting list.
    pub(crate) fn search_with_metas(
        &self,
        goals: Vec<BatchSmtGoal>,
        metas: &MetaState,
    ) -> Vec<Result<SmtProof, SmtError>> {
        let instantiated_goals = goals
            .into_iter()
            .map(|(goal_expr, local_ctx)| {
                let goal_expr = metas.instantiate(&goal_expr);
                let local_ctx = local_ctx
                    .into_iter()
                    .map(|decl| {
                        let ty = metas.instantiate(&decl.ty);
                        let value = decl.value.as_ref().map(|value| metas.instantiate(value));
                        LocalDecl { ty, value, ..decl }
                    })
                    .collect();
                (goal_expr, local_ctx)
            })
            .collect();
        self.run_batch(instantiated_goals)
    }

    fn run_batch(&self, goals: Vec<BatchSmtGoal>) -> Vec<Result<SmtProof, SmtError>> {
        let mut results = Vec::with_capacity(goals.len());
        let mut pending_goals = goals.into_iter();

        loop {
            let chunk: Vec<_> = pending_goals.by_ref().take(self.batch_size).collect();
            if chunk.is_empty() {
                break;
            }

            let start_index = results.len();
            let mut chunk_results = std::thread::scope(|scope| {
                let mut handles = Vec::with_capacity(chunk.len());
                for (offset, (goal_expr, local_ctx)) in chunk.into_iter().enumerate() {
                    let config = self.config.clone();
                    let logic = self.logic;
                    let goal_index = start_index + offset;
                    handles.push(scope.spawn(move || {
                        solve_goal(config, logic, goal_index, goal_expr, local_ctx)
                    }));
                }

                handles
                    .into_iter()
                    .map(|handle| match handle.join() {
                        Ok(result) => result,
                        Err(panic) => Err(AyError::SolverPanic(panic_payload_to_string(&panic))),
                    })
                    .collect::<Vec<_>>()
            });
            results.append(&mut chunk_results);
        }

        results
    }
}

fn solve_goal(
    config: AyConfig,
    logic: AyLogic,
    goal_index: usize,
    goal_expr: Expr,
    local_ctx: Vec<LocalDecl>,
) -> Result<SmtProof, SmtError> {
    let mut solver = create_smt_backend(&config, logic);
    let metas = MetaState::new();
    solver.register_fvars_from_context(&local_ctx, &metas)?;

    let mut dropped_hypotheses = 0u32;
    for decl in &local_ctx {
        if !decl.ty.is_sort()
            && solver
                .translate_and_assert_hypothesis(decl.fvar, &decl.ty)
                .is_err()
        {
            dropped_hypotheses += 1;
        }
    }
    if dropped_hypotheses > 0 {
        tracing::debug!(
            goal_index,
            dropped = dropped_hypotheses,
            "batch SMT search dropped unsupported hypothesis(es)"
        );
    }

    solver.prove(&goal_expr)
}

fn panic_payload_to_string(payload: &Box<dyn Any + Send + 'static>) -> String {
    if let Some(message) = payload.downcast_ref::<&str>() {
        (*message).to_string()
    } else if let Some(message) = payload.downcast_ref::<String>() {
        message.clone()
    } else {
        "unknown panic payload".to_string()
    }
}
