// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! AutomationEngine: the main entry point for clean native automation.

use crate::bridge::superposition_reconstruction::SymbolMap;
use crate::bridge::QuantifierOrigin;
use crate::engine_api::AutomationRequest;
use crate::premise::{MePoSelector, PremiseDatabase, PremiseId};
use crate::proof_result::ProofResult;
use clean_kernel::{Environment, Expr, FVarId, LocalContext};
use std::collections::HashMap;
use std::time::{Duration, Instant};

/// Native automation engine
///
/// Provides automatic theorem proving using multiple strategies:
/// 1. SMT solving via the SMT-Kernel bridge (handles equality, propositional logic)
/// 2. Superposition calculus (for first-order logic)
/// 3. Premise selection (for selecting relevant hypotheses)
///
/// # Thread Safety
///
/// This type is `Send + Sync` and can be safely shared across threads.
/// All fields are read-only after construction, so concurrent calls to
/// `auto_prove` are safe. For async contexts, use `auto_prove_async()` or
/// wrap sync methods in `tokio::task::spawn_blocking()`.
#[derive(Debug)]
pub struct AutomationEngine {
    /// Maximum SMT instantiation rounds
    pub(crate) max_smt_rounds: u32,
}

impl AutomationEngine {
    /// Create a new automation engine with default settings
    pub fn new() -> Self {
        Self {
            max_smt_rounds: 100,
        }
    }

    /// Create with custom SMT round limit
    pub fn with_config(max_smt_rounds: u32) -> Self {
        Self { max_smt_rounds }
    }

    fn prepare_superposition_reconstruction_env(
        env: &Environment,
        symbol_map: &SymbolMap,
        lane: &'static str,
    ) -> Option<Environment> {
        let mut recon_env = env.clone();
        symbol_map.declare_skolems(&mut recon_env);
        if let Err(error) = recon_env.init_classical() {
            tracing::warn!(
                lane,
                error = ?error,
                "superposition reconstruction classical bootstrap failed"
            );
            return None;
        }
        Some(recon_env)
    }

    /// Attempt to automatically prove a goal.
    ///
    /// This is the compatibility wrapper over
    /// [`Self::auto_prove_detailed`] / [`AutomationRequest`]. New call sites
    /// should prefer the detailed API so `Unverified`, `Refuted`, and
    /// `Unknown` outcomes remain visible to the caller.
    ///
    /// Returns `Some(ProofResult)` if a proof is found within the timeout,
    /// `None` if the goal cannot be proved or timeout is exceeded.
    pub fn auto_prove(
        &self,
        env: &Environment,
        goal: &Expr,
        timeout: Duration,
        local_ctx: Option<&LocalContext>,
    ) -> Option<ProofResult> {
        let hypotheses = local_ctx
            .map(|ctx| {
                ctx.iter()
                    .map(|decl| (decl.type_.clone(), None))
                    .collect::<Vec<_>>()
            })
            .unwrap_or_default();
        let mut request = AutomationRequest::new(goal, timeout);
        if !hypotheses.is_empty() {
            request = request.with_hypotheses(hypotheses.as_slice());
        }
        if let Some(ctx) = local_ctx {
            request = request.with_local_ctx(ctx);
        }
        self.auto_prove_with_request(env, request).verified()
    }

    /// Async compatibility wrapper over [`Self::auto_prove`].
    pub async fn auto_prove_async(
        &self,
        env: &Environment,
        goal: &Expr,
        timeout: Duration,
        local_ctx: Option<&LocalContext>,
    ) -> Option<ProofResult> {
        self.auto_prove(env, goal, timeout, local_ctx)
    }

    /// Try superposition-based proving with proof reconstruction.
    ///
    /// Pipeline:
    /// 1. Clausify the negated goal into CNF via [`GoalClausifier`]
    /// 2. Feed clauses to [`SuperpositionProver`]
    /// 3. Run saturation-based proving
    /// 4. If refutation found, reconstruct kernel proof via [`SuperpositionReconstructor`]
    ///
    /// Returns `ProofResult` on success (with `time_ms = 0`; caller may
    /// replace via [`ProofResult::with_time_ms`]).
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn try_superposition_prove(
        &self,
        env: &Environment,
        goal: &Expr,
    ) -> Option<ProofResult> {
        use crate::bridge::superposition_clausify::GoalClausifier;
        use crate::bridge::superposition_reconstruction::SuperpositionReconstructor;
        use crate::superposition::{ProverResult, SuperpositionProver};

        // Step 1: Clausify the negated goal (with env for accurate type inference)
        let mut clausifier = GoalClausifier::new_with_env(env);
        let (clause_sets, _symbol_map) = clausifier.clausify_goal(goal);

        if clause_sets.is_empty() {
            return None;
        }

        // Step 2: Feed clauses to the superposition prover
        let mut prover = SuperpositionProver::new();
        for literals in &clause_sets {
            prover.add_clause(literals.clone());
        }

        // Step 3: Run the prover with a bounded iteration count
        let result = prover.prove(10_000);

        // Step 4: If refutation found, reconstruct and wrap with byContradiction
        match result {
            ProverResult::Unsatisfiable(trace) => {
                let symbol_map = clausifier.into_symbol_map();
                let recon_env = Self::prepare_superposition_reconstruction_env(
                    env,
                    &symbol_map,
                    "superposition",
                )?;
                let mut reconstructor =
                    SuperpositionReconstructor::with_env(&trace, &symbol_map, &recon_env);
                match reconstructor.reconstruct_goal() {
                    Ok((proof, description)) => Some(ProofResult::new(proof, description, 0, None)),
                    Err(e) => {
                        tracing::warn!(
                            error = %e,
                            "superposition goal reconstruction failed"
                        );
                        None
                    }
                }
            }
            ProverResult::Saturated | ProverResult::ResourceLimit => None,
        }
    }

    /// Try superposition proving with hypotheses from the local context.
    ///
    /// Like `try_superposition_prove`, but also clausifies and feeds hypotheses
    /// to the prover. This enables refutation of goals that depend on context
    /// (e.g., proving `False` from contradictory hypotheses).
    ///
    /// Returns `ProofResult` on success (with `time_ms = 0`; caller may
    /// replace via [`ProofResult::with_time_ms`]).
    pub fn try_superposition_prove_with_hypotheses(
        &self,
        env: &Environment,
        goal: &Expr,
        hypotheses: &[(Expr, Option<QuantifierOrigin>)],
    ) -> Option<ProofResult> {
        use crate::bridge::superposition_clausify::GoalClausifier;
        use crate::bridge::superposition_reconstruction::SuperpositionReconstructor;
        use crate::superposition::{ProverResult, SuperpositionProver};

        let mut clausifier = GoalClausifier::new_with_env(env);
        let (goal_clauses, _) = clausifier.clausify_goal(goal);

        // Clausify hypotheses with sequential clause IDs matching prover assignment.
        // The prover assigns IDs 0..n-1 to goal clauses, then n, n+1, ... to
        // hypothesis clauses. SymbolMap IDs must match for proof reconstruction.
        let mut hyp_clauses: Vec<Vec<crate::superposition::Literal>> = Vec::new();
        let mut next_clause_id = goal_clauses.len() as u64;
        for (hyp, _origin) in hypotheses.iter() {
            let fvar = FVarId::new(next_clause_id);
            let clauses = clausifier.clausify_hypothesis_sequential(hyp, next_clause_id, fvar);
            next_clause_id += clauses.len() as u64;
            for c in clauses {
                hyp_clauses.push(c);
            }
        }

        if goal_clauses.is_empty() && hyp_clauses.is_empty() {
            return None;
        }

        let mut prover = SuperpositionProver::new();
        for literals in &goal_clauses {
            prover.add_clause(literals.clone());
        }
        for literals in &hyp_clauses {
            prover.add_clause(literals.clone());
        }

        let result = prover.prove(10_000);
        match result {
            ProverResult::Unsatisfiable(trace) => {
                let symbol_map = clausifier.into_symbol_map();
                let recon_env = Self::prepare_superposition_reconstruction_env(
                    env,
                    &symbol_map,
                    "superposition+hyps",
                )?;
                let mut reconstructor =
                    SuperpositionReconstructor::with_env(&trace, &symbol_map, &recon_env);
                match reconstructor.reconstruct_goal() {
                    Ok((proof, description)) => Some(ProofResult::new(proof, description, 0, None)),
                    Err(e) => {
                        tracing::warn!(
                            error = %e,
                            "superposition+hyps goal reconstruction failed"
                        );
                        None
                    }
                }
            }
            ProverResult::Saturated | ProverResult::ResourceLimit => None,
        }
    }

    /// Try superposition proving with hypotheses that preserve caller-provided FVarIds.
    ///
    /// Like `try_superposition_prove_with_hypotheses`, but each hypothesis carries
    /// the FVarId from the tactic's local context. This ensures the reconstructed
    /// proof term references the correct hypothesis variables for type-checking.
    ///
    /// Part of #1164: wiring superposition into the tactic framework.
    pub fn try_superposition_prove_with_fvars(
        &self,
        env: &Environment,
        goal: &Expr,
        hypotheses: &[(Expr, FVarId)],
    ) -> Option<ProofResult> {
        self.try_superposition_prove_with_fvars_until(env, goal, hypotheses, None)
    }

    /// [`Self::try_superposition_prove_with_fvars`] with a wall-clock `deadline`.
    ///
    /// The saturation loop polls `deadline` and bails (no proof) the moment it is
    /// reached, so a pipeline caller that threads its remaining budget cannot be
    /// trapped in a runaway saturation. `None` is the unbounded (iteration-only)
    /// behavior. Soundness is unchanged — a deadline only forgoes a proof, never
    /// fabricates one (the reconstructed term is still kernel-re-checked
    /// downstream).
    pub(crate) fn try_superposition_prove_with_fvars_until(
        &self,
        env: &Environment,
        goal: &Expr,
        hypotheses: &[(Expr, FVarId)],
        deadline: Option<Instant>,
    ) -> Option<ProofResult> {
        use crate::bridge::superposition_clausify::GoalClausifier;
        use crate::bridge::superposition_reconstruction::SuperpositionReconstructor;
        use crate::superposition::{ProverResult, SuperpositionProver};

        let mut clausifier = GoalClausifier::new_with_env(env);
        // Use a high sentinel FVarId base for goal clauses to avoid collision
        // with tactic-scope hypothesis FVarIds (which are small sequential IDs).
        // The sentinel must not collide with u64::MAX used by build_multi_clause_body
        // for the h_fvar sentinel.
        const GOAL_FVAR_SENTINEL: u64 = u64::MAX / 2;
        clausifier.set_goal_fvar_base(GOAL_FVAR_SENTINEL);
        let (goal_clauses, _) = clausifier.clausify_goal(goal);

        let mut hyp_clauses: Vec<Vec<crate::superposition::Literal>> = Vec::new();
        let mut next_clause_id = goal_clauses.len() as u64;
        for (hyp, fvar) in hypotheses.iter() {
            let clauses = clausifier.clausify_hypothesis_sequential(hyp, next_clause_id, *fvar);
            next_clause_id += clauses.len() as u64;
            for c in clauses {
                hyp_clauses.push(c);
            }
        }

        if goal_clauses.is_empty() && hyp_clauses.is_empty() {
            return None;
        }

        let mut prover = SuperpositionProver::new();
        for literals in &goal_clauses {
            prover.add_clause(literals.clone());
        }
        for literals in &hyp_clauses {
            prover.add_clause(literals.clone());
        }

        let result = prover.prove_until(10_000, deadline);
        match result {
            ProverResult::Unsatisfiable(trace) => {
                let symbol_map = clausifier.into_symbol_map();
                let recon_env = Self::prepare_superposition_reconstruction_env(
                    env,
                    &symbol_map,
                    "superposition+fvars",
                )?;
                let mut reconstructor =
                    SuperpositionReconstructor::with_env(&trace, &symbol_map, &recon_env);
                match reconstructor.reconstruct_goal() {
                    Ok((proof, description)) => Some(ProofResult::new(proof, description, 0, None)),
                    Err(e) => {
                        tracing::warn!(
                            error = %e,
                            "superposition+fvars goal reconstruction failed"
                        );
                        None
                    }
                }
            }
            ProverResult::Saturated | ProverResult::ResourceLimit => None,
        }
    }

    /// Attempt to prove a goal with premise-guided E-matching instantiation.
    ///
    /// This variant uses premise selection (MePo) to score hypotheses by their
    /// relevance to the goal, biasing E-matching instantiation toward more
    /// relevant quantifiers. This remains a compatibility wrapper over the
    /// detailed request/result API.
    ///
    /// # Arguments
    /// * `env` - The kernel environment
    /// * `goal` - The proposition to prove
    /// * `hypotheses` - Hypotheses with optional quantifier origin for scoring
    /// * `premise_db` - Database of known premises for relevance scoring
    /// * `timeout` - Maximum time to spend proving
    ///
    /// # Example
    ///
    /// ```text
    /// let engine = AutomationEngine::new();
    /// let mut premise_db = PremiseDatabase::new();
    /// // ... populate premise_db with known theorems ...
    ///
    /// let hypotheses = vec![
    ///     (forall_hyp, Some(QuantifierOrigin::new(name, premise_id))),
    /// ];
    /// let result = engine.auto_prove_with_premises(
    ///     &env, &goal, hypotheses, &premise_db, timeout, None
    /// );
    /// ```
    pub fn auto_prove_with_premises(
        &self,
        env: &Environment,
        goal: &Expr,
        hypotheses: Vec<(Expr, Option<QuantifierOrigin>)>,
        premise_db: &PremiseDatabase,
        timeout: Duration,
        local_ctx: Option<&LocalContext>,
    ) -> Option<ProofResult> {
        let mut request = AutomationRequest::new(goal, timeout)
            .with_hypotheses(hypotheses.as_slice())
            .with_premise_db(premise_db);
        if let Some(ctx) = local_ctx {
            request = request.with_local_ctx(ctx);
        }
        self.auto_prove_with_request(env, request).verified()
    }

    /// Compute premise relevance scores for a goal.
    ///
    /// This can be used to pre-compute scores before calling
    /// `auto_prove_with_premises` or for analysis/debugging.
    pub fn compute_premise_scores(
        premise_db: &PremiseDatabase,
        goal: &Expr,
    ) -> HashMap<PremiseId, f64> {
        let selector = MePoSelector::new(premise_db).with_threshold(0.0);
        selector
            .select_with_scores(goal)
            .iter()
            .map(|(p, score)| (p.id, *score))
            .collect()
    }
}

impl Default for AutomationEngine {
    fn default() -> Self {
        Self::new()
    }
}
