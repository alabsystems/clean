// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Detailed automation entrypoints layered on top of [`crate::engine`].

use crate::bridge::SmtBridge;
use crate::bridge::SmtVerificationResult;
use crate::engine::AutomationEngine;
use crate::engine_api::{AutomationOutcome, AutomationQuery, AutomationRequest, AutomationSource};
use crate::engine_induction_rewrite::REWRITE_DEPTH;
use crate::engine_router::{route_goal, RoutedEngine};
use crate::oracle::{
    sort_oracle_candidates, sort_proof_term_candidates, OracleRequest as ProofOracleRequest,
};
use crate::premise::{MePoSelector, PremiseDatabase, PremiseId};
use crate::proof_result::{build_hypothesis_proof_context, HypothesisWithProofFVar};
use crate::solver_cache::obligation_digest;
use crate::solver_cache::record::{AttemptResult, SmtStatsSnapshot, SolverEngine};
use crate::solver_cache::store;
use crate::solver_cache::telemetry::{self, AttemptTelemetry};
use crate::ProofResult;
use clean_kernel::{
    BinderInfo, Environment, Expr, ExprKind, FVarId, Level, LocalContext, Name, TypeChecker,
};
use std::collections::{HashMap, HashSet};
use std::time::Instant;

/// Maximum number of premises the [`AutomationEngine::try_premise_injection`]
/// lane feeds to the engines. Caps the injected hypothesis set so the SMT/
/// superposition search stays bounded while still surfacing the lemmas a goal
/// needs (the improved selector ranks the most relevant first).
const MAX_INJECTED_PREMISES: usize = 8;

/// Maximum number of candidate universe instantiations tried per
/// *universe-polymorphic* injected premise (see [`premise_injection_candidates`]).
/// Bounds the injected-hypothesis blow-up: each poly premise contributes at most
/// this many hypotheses (one per candidate level), each independently
/// kernel-re-checked when its proof is closed.
const MAX_LEVEL_CANDIDATES: usize = 3;

impl AutomationEngine {
    /// Canonical detailed entrypoint using the forward-compatible query type.
    ///
    /// New call sites should prefer this over [`Self::auto_prove_with_request`]
    /// because [`AutomationQuery`] can accept future options without breaking
    /// existing callers.
    pub fn auto_prove_with_query(
        &self,
        env: &Environment,
        query: AutomationQuery<'_>,
    ) -> AutomationOutcome {
        let start = Instant::now();
        // Phase-0 solver-cache obligation key: computed once, only when the
        // telemetry sink *or* the proof cache is enabled (zero overhead by
        // default). The goal-type digest is the Phase-0 key (design §2.1);
        // context/env extend it later.
        let obligation = if telemetry::is_enabled() || store::is_enabled() {
            obligation_digest(query.goal).ok()
        } else {
            None
        };

        // ── Cache-hit-before-solve (design §4.1) ───────────────────────────
        // If the proof cache holds a proof term for this obligation key, return
        // it as the proof result *without* re-running the solver search. The
        // returned term is NOT trusted here: it flows through the exact same
        // downstream kernel re-check (`recheck_and_classify`) the caller already
        // performs for a freshly-found proof, so a stale/colliding/corrupt entry
        // is caught by the kernel, never silently honored. We only short-circuit
        // when no premise database is in play, because cached closed proof terms
        // do not carry the caller's premise context.
        if store::is_enabled() && query.premise_db.is_none() {
            if let Some(digest) = obligation.as_deref() {
                let lookup_start = Instant::now();
                if let Some(cached) = store::get(digest) {
                    let proof_term = cached.proof_term;
                    let proof_term_digest = obligation_digest(&proof_term).ok();
                    telemetry::emit_cache_hit(
                        digest,
                        SolverEngine::CleanSmt,
                        elapsed_ms(lookup_start),
                        proof_term_digest,
                    );
                    return AutomationOutcome::Verified(Box::new(ProofResult::new(
                        proof_term,
                        format!(
                            "solver-cache hit ({} / {})",
                            cached.meta.solver, cached.meta.strategy
                        ),
                        elapsed_ms(start),
                        None,
                    )));
                }
            }
        }

        let outcome = self.run_pipeline(env, query, start, obligation.as_deref());

        // On a freshly-found proof, populate the cache so a later identical
        // obligation is a hit. Insert failures are non-fatal (logged, swallowed):
        // they only forgo a future hit, never affect this proof.
        if let (AutomationOutcome::Verified(result), Some(digest)) =
            (&outcome, obligation.as_deref())
        {
            // Only cache closed proof terms (no caller premise context); a term
            // referencing synthetic hypothesis fvars is not self-contained.
            if result.proof_context().is_none() {
                let meta = store::CacheMeta::new(
                    SolverEngine::CleanSmt.solver_name(),
                    telemetry::STRATEGY_ID,
                );
                if let Err(error) = store::put(digest, result.proof_term(), meta) {
                    tracing::warn!(%error, "solver-cache insert failed (ignored)");
                }
            }
        }

        outcome
    }

    /// The router-driven `{smt, induction, superposition, oracle}` search.
    ///
    /// Extracted from [`Self::auto_prove_with_query`] so the cache hook (lookup
    /// before, insert after) wraps the search. The engine *order* is chosen
    /// per-goal by [`crate::engine_router`] (best-first for the goal's
    /// theory/structure) instead of a fixed sequence; every plan is a
    /// permutation of all four engines, so the search still falls back to trying
    /// every engine on a misclassification. When a premise database is supplied
    /// and the routed engines fail, a final premise-injection lane feeds the most
    /// relevant lemmas to the engines.
    ///
    /// Soundness is unchanged: each engine still emits a proof term the kernel
    /// re-checks downstream; reordering attempts cannot accept an unsound proof.
    /// A `Verified` from any engine short-circuits; otherwise the strongest
    /// non-proof outcome (Refuted > Unverified > Unknown, first-seen on a tie) is
    /// returned. The induction lane intentionally runs even after an SMT
    /// `Refuted`, so a lossy EUF refutation can still be overridden by a genuine
    /// (kernel-checked) `Nat.rec` proof.
    fn run_pipeline(
        &self,
        env: &Environment,
        query: AutomationQuery<'_>,
        start: Instant,
        obligation: Option<&str>,
    ) -> AutomationOutcome {
        // Robustness rail: decline a pathologically deep goal before any engine
        // runs. Goal translation (SMT/superposition) and the induction lane's
        // kernel re-checks are recursive in the goal structure; on a goal nested
        // past `MAX_GOAL_DEPTH` a single such call can run for minutes (observed)
        // or overflow the stack — costs the per-engine deadline poll cannot
        // interrupt once inside a kernel call. Real goals are far shallower, so
        // this returns `Unknown` (→ `None` to `auto_prove`) without a search,
        // never a crash or runaway. Soundness-neutral: declining only forgoes a
        // proof attempt.
        if crate::engine_induction::goal_depth_exceeds(
            query.goal,
            crate::engine_induction::MAX_GOAL_DEPTH,
        ) {
            return AutomationOutcome::Unknown {
                reason: format!(
                    "goal nesting depth exceeds the search bound ({})",
                    crate::engine_induction::MAX_GOAL_DEPTH
                ),
                source: AutomationSource::Smt,
                time_ms: elapsed_ms(start),
            };
        }

        let (hypotheses_with_fvars, proof_context) =
            build_hypothesis_proof_context(query.hypotheses, query.local_ctx);

        let mut best: Option<AutomationOutcome> = None;
        let mut refuted = false;
        for engine in route_goal(query.goal) {
            if start.elapsed() >= query.timeout {
                break;
            }
            // A counter-model (`Refuted`) is terminal for the engines that cannot
            // legitimately override it. The induction lane is the sole exception:
            // a `∀(n:Nat)` EUF refutation is lossy (the uninterpreted translation
            // drops `Nat.rec`), so a genuine, kernel-checked `Nat.rec` proof may
            // still follow. SMT itself only runs once. This mirrors the historical
            // pipeline, where `Refuted` short-circuited before superposition/oracle.
            if refuted && matches!(engine, RoutedEngine::Superposition | RoutedEngine::Oracle) {
                continue;
            }
            let outcome = self.run_routed_engine(
                engine,
                env,
                &query,
                &hypotheses_with_fvars,
                proof_context.as_ref(),
                start,
                obligation,
            );
            if let Some(outcome) = outcome {
                if matches!(outcome, AutomationOutcome::Verified(_)) {
                    return outcome;
                }
                if matches!(outcome, AutomationOutcome::Refuted { .. }) {
                    refuted = true;
                }
                best = Some(merge_outcome(best, outcome));
            }
        }

        // Instance-projection-as-premise lane: when the goal is stated under a
        // local typeclass instance `[inst : C α]`, the class's *laws* (its
        // Prop-typed fields) are invisible to the routed engines, which only see
        // `inst` as an opaque structure. This lane projects those laws with the
        // kernel `Proj` primitive and offers them as premises (a direct
        // `is_def_eq` closer for the single-lemma leaf, plus injected hypotheses
        // for SMT/superposition). Gated on a local context being present. See
        // `try_instance_projection_premises`.
        if query.local_ctx.is_some() && start.elapsed() < query.timeout {
            if let Some(verified) =
                self.try_instance_projection_premises(env, &query, proof_context.as_ref(), start)
            {
                return verified;
            }
        }

        // Premise-injection last-resort lane: when a premise DB is supplied and
        // the routed engines did not prove the goal, select the most relevant
        // lemmas and feed them to the engines as injected hypotheses (closed by
        // their declaring constants, kernel-re-checked). See `try_premise_injection`.
        if query.premise_db.is_some() && start.elapsed() < query.timeout {
            if let Some(verified) =
                self.try_premise_injection(env, &query, proof_context.as_ref(), start)
            {
                return verified;
            }
        }

        best.unwrap_or_else(|| AutomationOutcome::Unknown {
            reason: "no engine produced a verdict".to_string(),
            source: AutomationSource::Smt,
            time_ms: elapsed_ms(start),
        })
    }

    /// Run one routed engine, returning its [`AutomationOutcome`].
    ///
    /// `None` means the engine was not applicable (oracle with no oracle hook, or
    /// the induction lane declined the goal) and should not contribute to the
    /// merged non-proof outcome. Each engine keeps its own telemetry emission so
    /// the per-engine attempt records are unchanged by the reordering.
    #[allow(clippy::too_many_arguments)]
    fn run_routed_engine(
        &self,
        engine: RoutedEngine,
        env: &Environment,
        query: &AutomationQuery<'_>,
        hypotheses_with_fvars: &[HypothesisWithProofFVar],
        proof_context: Option<&LocalContext>,
        start: Instant,
        obligation: Option<&str>,
    ) -> Option<AutomationOutcome> {
        match engine {
            RoutedEngine::Smt => {
                let smt_start = Instant::now();
                Some(self.try_smt_detailed(
                    env,
                    query.goal,
                    hypotheses_with_fvars,
                    query.premise_db,
                    proof_context,
                    start,
                    obligation,
                    smt_start,
                ))
            }
            RoutedEngine::Induction => {
                let base_ctx = proof_context.cloned().unwrap_or_default();
                let term = self.try_induction_lane(
                    env,
                    query.goal,
                    &base_ctx,
                    start + query.timeout,
                    crate::engine_induction::INDUCTION_FUEL,
                )?;
                let induction_ctx = if base_ctx.is_empty() {
                    None
                } else {
                    Some(base_ctx)
                };
                Some(AutomationOutcome::Verified(Box::new(ProofResult::new(
                    term,
                    "proved by structural induction (recursor)",
                    elapsed_ms(start),
                    induction_ctx,
                ))))
            }
            RoutedEngine::Superposition => {
                let superposition_hypotheses: Vec<(Expr, FVarId)> = hypotheses_with_fvars
                    .iter()
                    .map(|(hyp, fvar, _origin)| (hyp.clone(), *fvar))
                    .collect();
                let superpos_start = Instant::now();
                let superpos_result = self.try_superposition_prove_with_fvars_until(
                    env,
                    query.goal,
                    &superposition_hypotheses,
                    Some(start + query.timeout),
                );
                emit_attempt_telemetry(
                    obligation,
                    SolverEngine::CleanSuperposition,
                    superpos_start,
                    superpos_result
                        .as_ref()
                        .map(|r| (AttemptResult::Proved, Some(r.proof_term())))
                        .unwrap_or((AttemptResult::Noproof, None)),
                    None,
                );
                let mut result = superpos_result?;
                result.proof_context = proof_context.cloned();
                Some(AutomationOutcome::Verified(Box::new(
                    result.with_time_ms(elapsed_ms(start)),
                )))
            }
            RoutedEngine::Oracle => {
                query.oracle?;
                let oracle_start = Instant::now();
                let oracle_outcome = self.try_oracle_detailed(env, query, proof_context, start);
                emit_outcome_telemetry(
                    obligation,
                    SolverEngine::Oracle,
                    oracle_start,
                    &oracle_outcome,
                    None,
                );
                Some(oracle_outcome)
            }
        }
    }

    /// Detailed request/result API that preserves non-proof outcomes.
    ///
    /// Delegates to [`Self::auto_prove_with_query`] via [`AutomationQuery`]
    /// conversion. New call sites should prefer `auto_prove_with_query` directly.
    pub fn auto_prove_with_request(
        &self,
        env: &Environment,
        request: AutomationRequest<'_>,
    ) -> AutomationOutcome {
        self.auto_prove_with_query(env, AutomationQuery::from(request))
    }

    /// Alias retained for discoverability while the request/result API settles.
    pub fn auto_prove_detailed(
        &self,
        env: &Environment,
        request: AutomationRequest<'_>,
    ) -> AutomationOutcome {
        self.auto_prove_with_query(env, AutomationQuery::from(request))
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn try_smt_detailed(
        &self,
        env: &Environment,
        goal: &Expr,
        hypotheses: &[HypothesisWithProofFVar],
        premise_db: Option<&PremiseDatabase>,
        proof_context: Option<&LocalContext>,
        start: Instant,
        obligation: Option<&str>,
        attempt_start: Instant,
    ) -> AutomationOutcome {
        let mut bridge = SmtBridge::new(env);
        bridge.set_max_instantiation_rounds(self.max_smt_rounds);
        if let Some(ctx) = proof_context {
            bridge.set_local_ctx(ctx.clone());
        }

        if let Some(premise_db) = premise_db {
            let selector = MePoSelector::new(premise_db).with_threshold(0.0);
            let scored = selector.select_with_scores(goal);
            let premise_scores: HashMap<PremiseId, f64> = scored
                .iter()
                .map(|(premise, score)| (premise.id, *score))
                .collect();
            bridge.set_premise_scores(premise_scores);
        }

        let mut dropped_hypotheses = 0u32;
        for (hyp, fvar, origin) in hypotheses {
            if bridge
                .add_hypothesis_with_premise(hyp, Some(*fvar), origin.clone())
                .is_err()
            {
                dropped_hypotheses += 1;
            }
        }
        if dropped_hypotheses > 0 {
            tracing::warn!(
                dropped = dropped_hypotheses,
                "hypothesis(es) dropped in detailed automation path (unsupported by SMT bridge)"
            );
        }

        let proved = bridge.prove(goal);
        // Capture SMT statistics for telemetry only when the sink is enabled
        // (the default disabled path does not touch the bridge stats).
        let smt_stats = if telemetry::is_enabled() {
            Some(telemetry::snapshot_smt_stats(&bridge.stats()))
        } else {
            None
        };

        let outcome = match proved {
            Ok(SmtVerificationResult::Verified(proof)) => {
                AutomationOutcome::Verified(Box::new(ProofResult::new(
                    proof.proof_term().clone(),
                    proof.proof_sketch(),
                    elapsed_ms(start),
                    proof_context.cloned(),
                )))
            }
            Ok(SmtVerificationResult::Unverified { reason, .. }) => AutomationOutcome::Unverified {
                reason: reason.to_string(),
                source: AutomationSource::Smt,
                time_ms: elapsed_ms(start),
            },
            Ok(SmtVerificationResult::Refuted(_model)) => AutomationOutcome::Refuted {
                source: AutomationSource::Smt,
                time_ms: elapsed_ms(start),
            },
            Ok(SmtVerificationResult::Unknown(reason)) => AutomationOutcome::Unknown {
                reason,
                source: AutomationSource::Smt,
                time_ms: elapsed_ms(start),
            },
            Err(error) => AutomationOutcome::Unknown {
                reason: error.to_string(),
                source: AutomationSource::Smt,
                time_ms: elapsed_ms(start),
            },
        };

        emit_outcome_telemetry(
            obligation,
            SolverEngine::CleanSmt,
            attempt_start,
            &outcome,
            smt_stats,
        );
        outcome
    }

    pub(crate) fn try_oracle_detailed(
        &self,
        env: &Environment,
        query: &AutomationQuery<'_>,
        proof_context: Option<&LocalContext>,
        start: Instant,
    ) -> AutomationOutcome {
        let oracle = match query.oracle {
            Some(oracle) => oracle,
            None => {
                return AutomationOutcome::Unknown {
                    reason: "oracle hooks were not provided".to_string(),
                    source: AutomationSource::Oracle,
                    time_ms: elapsed_ms(start),
                };
            }
        };

        if !oracle.is_available() {
            return AutomationOutcome::Unknown {
                reason: "oracle is not available".to_string(),
                source: AutomationSource::Oracle,
                time_ms: elapsed_ms(start),
            };
        }

        let oracle_request = ProofOracleRequest::from_goal_and_context(query.goal, proof_context);

        // --- Phase 1: Try direct proof-term candidates (kernel-validated) ---
        //
        // These bypass the OracleCandidateRunner entirely. The engine validates
        // each candidate via `TypeChecker::infer_type` + `is_def_eq` against the
        // goal. This is the cheapest validation path and runs first.
        if let Ok(mut proof_terms) = oracle.suggest_proof_term(&oracle_request) {
            sort_proof_term_candidates(&mut proof_terms);
            for pt_candidate in &proof_terms {
                if query.timeout.saturating_sub(start.elapsed()).is_zero() {
                    return AutomationOutcome::Unknown {
                        reason: "oracle proof-term validation timed out".to_string(),
                        source: AutomationSource::Oracle,
                        time_ms: elapsed_ms(start),
                    };
                }

                if let Some(outcome) = validate_proof_term_candidate(
                    env,
                    query.goal,
                    proof_context,
                    pt_candidate,
                    start,
                ) {
                    return outcome;
                }
            }
        }

        // --- Phase 2: Try tactic candidates via OracleCandidateRunner ---
        let runner = match query.oracle_runner {
            Some(runner) => runner,
            None => {
                // No runner and no proof terms succeeded; report exhaustion.
                return AutomationOutcome::Unknown {
                    reason: "oracle returned no usable proof-term candidates \
                             and no OracleCandidateRunner was provided"
                        .to_string(),
                    source: AutomationSource::Oracle,
                    time_ms: elapsed_ms(start),
                };
            }
        };

        let mut candidates = match oracle.suggest_proof(&oracle_request) {
            Ok(candidates) => candidates,
            Err(error) => {
                return AutomationOutcome::Unknown {
                    reason: format!("oracle failed: {error}"),
                    source: AutomationSource::Oracle,
                    time_ms: elapsed_ms(start),
                };
            }
        };
        sort_oracle_candidates(&mut candidates);
        if candidates.is_empty() {
            return AutomationOutcome::Unknown {
                reason: "oracle returned no candidates".to_string(),
                source: AutomationSource::Oracle,
                time_ms: elapsed_ms(start),
            };
        }

        for candidate in &candidates {
            let remaining = query.timeout.saturating_sub(start.elapsed());
            if remaining.is_zero() {
                return AutomationOutcome::Unknown {
                    reason: "oracle candidate execution timed out".to_string(),
                    source: AutomationSource::Oracle,
                    time_ms: elapsed_ms(start),
                };
            }

            match runner.try_candidate(env, proof_context, query.goal, candidate, remaining) {
                Ok(Some(proof)) => {
                    return AutomationOutcome::Verified(Box::new(
                        proof.with_time_ms(elapsed_ms(start)),
                    ));
                }
                Ok(None) => {}
                Err(error) => {
                    return AutomationOutcome::Unknown {
                        reason: error.to_string(),
                        source: AutomationSource::Oracle,
                        time_ms: elapsed_ms(start),
                    };
                }
            }
        }

        AutomationOutcome::Unknown {
            reason: format!(
                "oracle exhausted {} candidate(s) without a verified proof",
                candidates.len()
            ),
            source: AutomationSource::Oracle,
            time_ms: elapsed_ms(start),
        }
    }

    /// Premise-injection lane: prove `query.goal` by feeding the most relevant
    /// lemmas from the premise database to the SMT and superposition engines.
    ///
    /// This is the "better premise selection" payoff: the routed engines run
    /// with only the caller's explicit hypotheses, so an equational/arithmetic
    /// goal that needs a *specific* library lemma is left unproved. This lane
    /// selects the top relevant premises (improved conclusion-weighted MePo with
    /// dependency propagation, [`MePoSelector::select_relevant`]), layers each as
    /// a fresh hypothesis `fvar : C.type` on top of the proof context, and runs
    /// the engines. The returned proof term references those hypothesis `fvar`s;
    /// each is then closed by substituting its declaring constant `C`, yielding a
    /// closed term that the kernel re-checks against the goal.
    ///
    /// # Soundness
    ///
    /// A premise is injected only when it is a real constant in `env` (so `C` has
    /// the declared type the hypothesis assumed). Universe-monomorphic premises
    /// inject `@C` directly; **universe-polymorphic** premises inject `@C.{ℓ…}`
    /// for each candidate level instantiation from a small, bounded menu
    /// ([`premise_injection_candidates`]) — the level instantiation is *guessed*,
    /// never trusted: each injected hypothesis carries the type `C.{ℓ…}` actually
    /// produced by that instantiation, and the closing constant is the matching
    /// `@C.{ℓ…}`. The final term is re-checked (`infer_type` + `is_def_eq` against
    /// the goal) before it is returned, so a wrong level instantiation (or a
    /// stale/mismatched premise, or a bad substitution) is rejected by the kernel,
    /// never emitted as success. Returns `Some(Verified)` only on a kernel-checked
    /// closed proof.
    fn try_premise_injection(
        &self,
        env: &Environment,
        query: &AutomationQuery<'_>,
        proof_context: Option<&LocalContext>,
        start: Instant,
    ) -> Option<AutomationOutcome> {
        let db = query.premise_db?;
        let selector = MePoSelector::new(db);
        let relevant = selector.select_relevant(query.goal, MAX_INJECTED_PREMISES);
        if relevant.is_empty() {
            return None;
        }

        // Candidate universe levels for instantiating universe-polymorphic
        // premises (the monomorphic ones ignore this).
        let candidates = goal_candidate_levels(query.goal);

        // Layer each injectable premise onto the proof context as a fresh
        // hypothesis (a universe-poly premise contributes one hypothesis per
        // candidate level instantiation), recording the constant that closes its
        // fvar.
        let mut ctx = proof_context.cloned().unwrap_or_default();
        let mut hypotheses: Vec<HypothesisWithProofFVar> = Vec::new();
        let mut closing: Vec<(FVarId, Expr)> = Vec::new();
        for premise in &relevant {
            for (hyp_type, closing_const) in
                premise_injection_candidates(env, &premise.name, &candidates)
            {
                let fvar = ctx.push(premise.name.clone(), hyp_type.clone(), BinderInfo::Default);
                hypotheses.push((hyp_type, fvar, None));
                closing.push((fvar, closing_const));
            }
        }
        if closing.is_empty() {
            return None;
        }

        // SMT first (EUF/arithmetic close most lemma-backed goals), then
        // superposition (equational rewriting with the lemmas as rules). Both are
        // gated on the remaining wall-clock budget so the injection lane cannot
        // run away past the caller's timeout.
        let deadline = start + query.timeout;
        if start.elapsed() < query.timeout {
            let smt_start = Instant::now();
            let smt = self.try_smt_detailed(
                env,
                query.goal,
                &hypotheses,
                Some(db),
                Some(&ctx),
                start,
                None,
                smt_start,
            );
            if let AutomationOutcome::Verified(result) = smt {
                if let Some(verified) = self.close_injected_proof(
                    env,
                    query.goal,
                    proof_context,
                    result.proof_term(),
                    &closing,
                    start,
                ) {
                    return Some(verified);
                }
            }
        }

        if start.elapsed() < query.timeout {
            let superposition_hyps: Vec<(Expr, FVarId)> = hypotheses
                .iter()
                .map(|(hyp, fvar, _)| (hyp.clone(), *fvar))
                .collect();
            if let Some(result) = self.try_superposition_prove_with_fvars_until(
                env,
                query.goal,
                &superposition_hyps,
                Some(deadline),
            ) {
                if let Some(verified) = self.close_injected_proof(
                    env,
                    query.goal,
                    proof_context,
                    result.proof_term(),
                    &closing,
                    start,
                ) {
                    return Some(verified);
                }
            }
        }

        None
    }

    /// Close an injected-premise proof term and kernel-re-check it.
    ///
    /// Substitutes each injected hypothesis `fvar` with its declaring constant,
    /// then verifies the resulting (closed-over-`proof_context`) term against
    /// `goal`. Returns `Some(Verified)` only when the kernel accepts it.
    fn close_injected_proof(
        &self,
        env: &Environment,
        goal: &Expr,
        proof_context: Option<&LocalContext>,
        open_term: &Expr,
        closing: &[(FVarId, Expr)],
        start: Instant,
    ) -> Option<AutomationOutcome> {
        let mut term = open_term.clone();
        for (fvar, const_term) in closing {
            term = term.abstract_fvar(*fvar).instantiate(const_term);
        }
        let tc = match proof_context {
            Some(ctx) if !ctx.is_empty() => TypeChecker::with_context(env, ctx.clone()),
            _ => TypeChecker::new(env),
        };
        let inferred = tc.infer_type(&term).ok()?;
        if !tc.is_def_eq(&inferred, goal) {
            return None;
        }
        Some(AutomationOutcome::Verified(Box::new(ProofResult::new(
            term,
            "proved via injected premises (kernel-checked)",
            elapsed_ms(start),
            proof_context.cloned(),
        ))))
    }

    /// Instance-projection-as-premise lane: when the goal is stated under a
    /// local typeclass instance `[inst : C α]`, the class's *laws* (its
    /// Prop-typed fields — `mul_one`, `mul_assoc`, …) are not visible to the
    /// routed engines, which only ever see `inst` as an opaque structure. This
    /// lane makes them available. For every instance local in the proof context
    /// it projects each Prop-typed field with the kernel projection primitive
    /// `Proj(C, i, inst)` (the exact field access Lean itself compiles a class
    /// method to), yielding a law term whose *type is the class axiom*. Those
    /// laws are offered two ways:
    ///
    /// 1. a **direct** `is_def_eq` closer that specialises one projected law to
    ///    the goal's arguments (first-order matches the law's conclusion against
    ///    the goal, applies the law, and re-checks) — this closes the common
    ///    single-lemma leaf that SMT's syntactic matcher cannot bridge; and
    /// 2. as **injected hypotheses** fed to SMT + superposition (each closed by
    ///    substituting its hypothesis fvar with the projection term, then
    ///    re-checked by [`Self::close_injected_proof`]).
    ///
    /// # Soundness
    ///
    /// This is a *search* lane, never TCB. Every projection term is built with
    /// the kernel `Proj` primitive and *type-inferred by the kernel*
    /// (`infer_type`) — a wrong field index or a non-projectable local is
    /// rejected there, never emitted. Only Prop-typed projections (the axioms)
    /// are kept; data fields (`mul`, `one`) are skipped. The final term — the
    /// specialised law, or the closed injected proof — is re-checked
    /// (`infer_type` + `is_def_eq` against the goal) before it is returned, so a
    /// wrong specialisation / level / substitution is caught by the kernel and
    /// never returned as success. Returns `Some(Verified)` only on a
    /// kernel-checked term.
    fn try_instance_projection_premises(
        &self,
        env: &Environment,
        query: &AutomationQuery<'_>,
        proof_context: Option<&LocalContext>,
        start: Instant,
    ) -> Option<AutomationOutcome> {
        let ctx = proof_context?;
        if ctx.is_empty() {
            return None;
        }
        let laws = collect_instance_projection_laws(env, ctx);
        if laws.is_empty() {
            return None;
        }

        // (1) Direct is_def_eq closer — specialise a single projected law to the
        // goal. Handles the single-lemma leaf case SMT's syntactic matcher can't
        // bridge.
        if let Some(verified) = self.try_project_law_defeq(env, query.goal, ctx, &laws, start) {
            return Some(verified);
        }

        // (1b) Rewrite-search closer — apply the projected laws as directed
        // rewrites (into sub-terms, and multiple laws chained), for the goals the
        // whole-goal direct closer cannot align: one law under a congruence
        // (`(a*1)*b = a*b`) and two laws chained (`(a*1)*(1*b) = a*b`). See
        // `try_project_law_rewrite`.
        if start.elapsed() < query.timeout {
            if let Some(verified) = self.try_project_law_rewrite(
                env,
                query.goal,
                ctx,
                &laws,
                start,
                start + query.timeout,
            ) {
                return Some(verified);
            }
        }

        // (2) Injected-hypothesis lane: layer each projected law onto the context
        // as a fresh hypothesis and feed SMT + superposition; close the returned
        // term by substituting each hypothesis fvar with its projection term.
        //
        // The engines see the whnf-normalized goal (`goal_norm`), so a goal
        // written with operator notation reduces to the same class-op form the
        // projected law hypotheses carry — the multi-step extension of the direct
        // closer's single-lemma whnf bridge. Each returned term is still
        // re-checked against the *original* `query.goal` by `close_injected_proof`
        // (`goal_norm` is def-eq to it), so this only widens the engines' reach.
        let mut ctx2 = ctx.clone();
        let mut hypotheses: Vec<HypothesisWithProofFVar> = Vec::new();
        let mut closing: Vec<(FVarId, Expr)> = Vec::new();
        for (law_ty, law_term) in &laws {
            let fvar = ctx2.push(
                Name::from_string("inst_law"),
                law_ty.clone(),
                BinderInfo::Default,
            );
            hypotheses.push((law_ty.clone(), fvar, None));
            closing.push((fvar, law_term.clone()));
        }
        let tc_norm = TypeChecker::with_context(env, ctx2.clone());
        let goal_norm = whnf_normalize(&tc_norm, query.goal, WHNF_NORM_FUEL);

        let deadline = start + query.timeout;
        if start.elapsed() < query.timeout {
            let smt_start = Instant::now();
            let smt = self.try_smt_detailed(
                env,
                &goal_norm,
                &hypotheses,
                None,
                Some(&ctx2),
                start,
                None,
                smt_start,
            );
            if let AutomationOutcome::Verified(result) = smt {
                if let Some(verified) = self.close_injected_proof(
                    env,
                    query.goal,
                    Some(ctx),
                    result.proof_term(),
                    &closing,
                    start,
                ) {
                    return Some(verified);
                }
            }
        }

        if start.elapsed() < query.timeout {
            let superposition_hyps: Vec<(Expr, FVarId)> = hypotheses
                .iter()
                .map(|(hyp, fvar, _)| (hyp.clone(), *fvar))
                .collect();
            if let Some(result) = self.try_superposition_prove_with_fvars_until(
                env,
                &goal_norm,
                &superposition_hyps,
                Some(deadline),
            ) {
                if let Some(verified) = self.close_injected_proof(
                    env,
                    query.goal,
                    Some(ctx),
                    result.proof_term(),
                    &closing,
                    start,
                ) {
                    return Some(verified);
                }
            }
        }

        None
    }

    /// Close `goal` by specialising one projected class law to it.
    ///
    /// For each `(law_ty, law_term)`: first try the bare law (its type may
    /// already be def-eq to the goal — a 0-ary law); otherwise first-order-match
    /// the law's conclusion (its Pi telescope stripped) against the goal to
    /// recover the argument for each universally-quantified variable, apply
    /// `law_term` to those arguments, and re-check. [`Self::close_injected_proof`]
    /// (with no substitution) performs the `infer_type` + `is_def_eq` gate — the
    /// sole soundness arbiter, so a wrong match simply fails it and the loop
    /// moves on.
    fn try_project_law_defeq(
        &self,
        env: &Environment,
        goal: &Expr,
        ctx: &LocalContext,
        laws: &[(Expr, Expr)],
        start: Instant,
    ) -> Option<AutomationOutcome> {
        // whnf pre-pass: normalize the goal's operator notation to class-op form
        // once, so the syntactic matcher can align a goal written with
        // heterogeneous operators (`a * 1` = `@HMul.hMul … instMul a …`) against
        // a projected law stated in `C.op inst …` form. The recovered arguments
        // feed a term that is *always re-checked against the original `goal`*
        // (via `close_injected_proof`), so normalization only widens what
        // matches — never what the kernel accepts.
        let tc = TypeChecker::with_context(env, ctx.clone());
        let goal_norm = whnf_normalize(&tc, goal, WHNF_NORM_FUEL);
        let goal_changed = goal_norm != *goal;

        for (law_ty, law_term) in laws {
            // (a) 0-ary law: its type may already be the goal.
            if let Some(verified) =
                self.close_injected_proof(env, goal, Some(ctx), law_term, &[], start)
            {
                return Some(verified);
            }
            // (b) specialise the law's telescope to the goal's arguments —
            // matching first against the raw goal, then (if it differs) against
            // the whnf-normalized goal.
            if let Some(applied) = specialize_law_to_goal(law_ty, law_term, goal) {
                if let Some(verified) =
                    self.close_injected_proof(env, goal, Some(ctx), &applied, &[], start)
                {
                    return Some(verified);
                }
            }
            if goal_changed {
                if let Some(applied) = specialize_law_to_goal(law_ty, law_term, &goal_norm) {
                    if let Some(verified) =
                        self.close_injected_proof(env, goal, Some(ctx), &applied, &[], start)
                    {
                        return Some(verified);
                    }
                }
            }
        }
        None
    }

    /// Close an equality `goal` by applying the projected class laws as *directed
    /// rewrites* — the multi-step / multi-lemma extension of the direct closer.
    ///
    /// The direct closer ([`Self::try_project_law_defeq`]) first-order matches ONE
    /// projected law's conclusion against the WHOLE goal, so it closes only a
    /// single-lemma whole-goal instance (`inst.mul a inst.one = a`). It cannot
    /// rewrite a law into a proper SUBTERM (`(a*1)*b = a*b`, `mul_one` under a
    /// congruence) nor CHAIN two distinct laws (`(a*1)*(1*b) = a*b`, `mul_one` on
    /// the left operand and `one_mul` on the right). Those need an equational
    /// rewrite search over the projected laws.
    ///
    /// This lane reuses the induction lane's kernel-checked rewrite engine
    /// ([`Self::prove_eq_rewrite`]): each projected law `∀ x…, l = r` becomes a
    /// directed rewrite fact `(law_term, law_ty)`, and `prove_eq_rewrite` applies
    /// them at sub-positions — lifting each rewrite through the surrounding
    /// application spine with `congrArg`/`congr` and stitching the residual with
    /// `Eq.trans` — recursing until the goal reduces to reflexivity. It is bounded
    /// by [`REWRITE_DEPTH`] and the caller's wall-clock `deadline`. The search is
    /// run at sub-positions of BOTH the RAW goal and (as a fallback) its
    /// whnf-normalized form (the same operator-notation pre-pass the direct closer
    /// uses), mirroring [`Self::try_project_law_defeq`]. The raw attempt is what
    /// aligns a real-Mathlib goal in surface `HMul`/`OfNat` notation with the
    /// equally-surface projected law (`mul_one`) at a sub-position; the normalized
    /// attempt aligns a surface goal against a law already in class-op form.
    ///
    /// # Soundness
    ///
    /// This is a *search* lane, never TCB. `prove_eq_rewrite` kernel-checks
    /// (`infer_type` + `is_def_eq`) every term it builds, and the returned term is
    /// re-checked against the ORIGINAL `goal` by [`Self::close_injected_proof`]
    /// (the whnf normal form is def-eq to it). A wrong or over-eager rewrite
    /// simply fails that gate and is never returned as success; the lane never
    /// emits `sorry`/axiom. Returns `Some(Verified)` only on a kernel-checked term.
    fn try_project_law_rewrite(
        &self,
        env: &Environment,
        goal: &Expr,
        ctx: &LocalContext,
        laws: &[(Expr, Expr)],
        start: Instant,
        deadline: Instant,
    ) -> Option<AutomationOutcome> {
        // whnf pre-pass: collapse the goal's operator notation to class-op form so
        // the rewriter aligns a goal written with heterogeneous operators against a
        // projected law's `C.op inst …` conclusion (see `try_project_law_defeq`).
        let tc = TypeChecker::with_context(env, ctx.clone());
        let goal_norm = whnf_normalize(&tc, goal, WHNF_NORM_FUEL);
        let goal_changed = goal_norm != *goal;

        // Each projected law `∀ x…, l = r` is a directed rewrite fact
        // `(witness, equation_type)`; the engine's sub-term rewriter peels the `∀`
        // telescope and first-order matches at a sub-position.
        let facts: Vec<(Expr, Expr)> = laws
            .iter()
            .map(|(law_ty, law_term)| (law_term.clone(), law_ty.clone()))
            .collect();

        // Sub-position search against the RAW goal FIRST. The projected-law patterns
        // in `facts` are themselves un-normalized — a real-Mathlib class law
        // (`mul_one`) is stated in surface `@HMul.hMul …`/`@OfNat.ofNat …` notation,
        // and only the *goal* is normalized here, not the facts. So the raw goal's
        // sub-terms — carrying that same surface notation — align head-to-head with
        // the fact patterns, letting `mul_one` match the `(a*1)` sub-position of
        // `(a*1)*b`; the normalized goal's collapsed class-op/`Proj` heads would NOT
        // (that head desync is exactly why the norm-only search missed G2). This
        // mirrors `try_project_law_defeq`, which specialises each law against the raw
        // goal (…@926) *before* the normalized one (…@934). Kernel-gated as ever:
        // `prove_eq_rewrite` checks every term against the raw goal, and the result
        // is re-checked by `close_injected_proof` below.
        if let Some(term) = self.prove_eq_rewrite(env, ctx, goal, &facts, deadline, REWRITE_DEPTH) {
            if let Some(verified) =
                self.close_injected_proof(env, goal, Some(ctx), &term, &[], start)
            {
                return Some(verified);
            }
        }

        // Fall back to the whnf-normalized goal (class-op / `Proj`-head form) — the
        // synthetic whnf-pre-pass path: a goal in surface notation whose matching
        // *law* is already in class-op form matches only after the goal's heads are
        // collapsed down to the law's. Only attempted when normalization actually
        // changed the goal. Re-checked against the ORIGINAL goal (`goal_norm` is
        // def-eq to it), the sole soundness gate for this lane.
        if goal_changed {
            if let Some(term) =
                self.prove_eq_rewrite(env, ctx, &goal_norm, &facts, deadline, REWRITE_DEPTH)
            {
                return self.close_injected_proof(env, goal, Some(ctx), &term, &[], start);
            }
        }
        None
    }
}

/// Upper bound on the number of projected class laws collected from the local
/// context in one call — keeps the injected-hypothesis set (and the direct
/// closer's per-law work) bounded on a context carrying many instances.
const MAX_PROJECTED_LAWS: usize = 32;

/// Maximum `extends`-chain depth the transitive parent-projection follows.
/// `Monoid extends Semigroup extends Mul` needs depth 2 to reach `Mul` from a
/// `Monoid` instance; the shallow finite class hierarchies Lean compiles never
/// nest anywhere near this, so it caps the (already `seen`-deduplicated) worklist
/// against a pathological or cyclic reflected structure without truncating any
/// real hierarchy.
const MAX_PARENT_DEPTH: usize = 4;

/// Upper bound on the number of instances the transitive projection worklist
/// expands in one call — a belt-and-braces termination bound alongside
/// [`MAX_PARENT_DEPTH`] and the `seen` set, so a wide-and-deep reflected DAG
/// cannot blow up the projection scan.
const MAX_PROJECTION_STEPS: usize = 64;

/// Fuel for the structural whnf normalizer ([`whnf_normalize`]). Bounds the
/// depth to which the goal's operator notation is unfolded before the syntactic
/// matcher runs. Typeclass operator chains (`HMul.hMul → instMul → C.op`) are a
/// handful of nodes deep, so this comfortably covers them while staying a hard
/// termination bound (whnf itself is heartbeat-bounded).
const WHNF_NORM_FUEL: u32 = 8;

/// Fresh-fvar base for the first-order matcher's telescope holes. Chosen far
/// above realistic context ids (below the reserved sentinel range) so a hole id
/// never collides with a genuine local; the holes appear only in the *pattern*
/// (they are replaced by matched goal subterms before the term is built), so
/// this range never leaks into an emitted proof.
const LAW_HOLE_FVAR_BASE: u64 = u64::MAX / 2;

/// The name of the head constant of `e`'s application spine, if any (mdata
/// transparent). Used to read the class name off an instance local's type.
fn head_const_name_of(e: &Expr) -> Option<Name> {
    match e.strip_mdata().get_app_fn().kind() {
        ExprKind::Const(name, _) => Some(name.clone()),
        _ => None,
    }
}

/// `true` iff `ty` is a proposition — its own type whnf-reduces to `Sort 0`.
/// Distinguishes a projected class *law* (`∀ x, …` : Prop) from a projected
/// *data* field (`α → α`, `α`, … : Type).
fn expr_type_is_prop(tc: &TypeChecker<'_>, ty: &Expr) -> bool {
    match tc.infer_type(ty) {
        Ok(sort) => matches!(tc.whnf(&sort).kind(), ExprKind::Sort(l) if l.is_zero()),
        Err(_) => false,
    }
}

/// Project the Prop-typed fields (class axioms) of every instance local in
/// `ctx`, returning `(law_type, law_term)` pairs where `law_term = Proj(C, i,
/// inst)` and `law_type` is its kernel-inferred type.
///
/// An instance local is any decl whose type's head constant is a registered
/// class ([`Environment::is_class`]); its fields come from
/// [`Environment::inductive_info`]. Each projection is type-inferred by the
/// kernel — a non-projectable local (e.g. a class with no registered structure
/// fields) yields nothing, and only Prop-typed projections are kept, so data
/// fields (`mul`, `one`) are skipped.
fn collect_instance_projection_laws(env: &Environment, ctx: &LocalContext) -> Vec<(Expr, Expr)> {
    let tc = TypeChecker::with_context(env, ctx.clone());
    let mut laws: Vec<(Expr, Expr)> = Vec::new();

    // Worklist of `(instance_term, class_name, depth)`. Seeded with the instance
    // locals in the context (depth 0); the transitive step pushes parent
    // instances reached through a data-valued projection whose type head is
    // itself a class (an `extends` field like `Monoid.toSemigroup`).
    let mut worklist: Vec<(Expr, Name, usize)> = Vec::new();
    let mut seen: HashSet<Expr> = HashSet::new();
    for decl in ctx.iter() {
        let Some(class_name) = head_const_name_of(&decl.type_) else {
            continue;
        };
        if !env.is_class(&class_name) {
            continue;
        }
        let inst = Expr::fvar(decl.id);
        if seen.insert(inst.clone()) {
            worklist.push((inst, class_name, 0));
        }
    }

    let mut steps = 0usize;
    while let Some((inst, class_name, depth)) = worklist.pop() {
        steps += 1;
        if steps > MAX_PROJECTION_STEPS {
            break;
        }
        let Some(info) = env.inductive_info(&class_name) else {
            continue;
        };
        let Some(fields) = info.field_names.as_ref() else {
            continue;
        };
        for i in 0..fields.len() {
            let Ok(idx) = u32::try_from(i) else {
                break;
            };
            let proj = Expr::proj(class_name.clone(), idx, inst.clone());
            let Ok(proj_ty) = tc.infer_type(&proj) else {
                continue;
            };
            if expr_type_is_prop(&tc, &proj_ty) {
                // A Prop-typed projection is a class axiom (`mul_one`,
                // `mul_assoc`, …) — surface it as a law.
                laws.push((proj_ty, proj));
                if laws.len() >= MAX_PROJECTED_LAWS {
                    return laws;
                }
            } else if depth < MAX_PARENT_DEPTH {
                // A data-valued projection whose type head is itself a class is
                // an `extends` parent-instance field (`Monoid.toSemigroup :
                // Semigroup α`). Recurse into it so the parent class's laws
                // (`Semigroup.mul_assoc`, reachable only through this projection)
                // are surfaced too. Bounded by `MAX_PARENT_DEPTH` and the `seen`
                // set (finite shallow hierarchy; never loops). All other data
                // fields (`mul`, `one`) are skipped.
                let parent = head_const_name_of(tc.whnf(&proj_ty).strip_mdata());
                if let Some(parent) = parent {
                    if env.is_class(&parent) && seen.insert(proj.clone()) {
                        worklist.push((proj, parent, depth + 1));
                    }
                }
            }
        }
    }
    laws
}

/// Structural weak-head normalization: whnf the head of `e`, then recurse into
/// the arguments of the resulting application spine (fuel-bounded), reassembling
/// the term from the normalized parts.
///
/// A plain [`TypeChecker::whnf`] only reduces the *head* of an equality goal
/// (`Eq`, an axiom — stuck), leaving its operands (`a * 1` written as
/// `@HMul.hMul M M M instMul a (@OfNat.ofNat …)`) untouched. This pass drives
/// whnf into those operands, collapsing the instance-notation chain
/// (`HMul.hMul → instMul → C.op`) down to the underlying class-op form
/// (`C.op inst a …`) that the syntactic first-order matcher can align with a
/// projected law's conclusion.
///
/// Meaning-preserving: `whnf` preserves definitional equality and reassembly
/// only substitutes def-eq subterms, so the result is def-eq to `e`. This is a
/// *matching* aid only — the caller's kernel re-check (`infer_type` + `is_def_eq`
/// against the original goal) remains the sole soundness gate, so a wrong or
/// over-eager normalization cannot yield an accepted unsound proof.
fn whnf_normalize(tc: &TypeChecker<'_>, e: &Expr, fuel: u32) -> Expr {
    if fuel == 0 {
        return e.clone();
    }
    let reduced = tc.whnf(e);
    let reduced = reduced.strip_mdata();
    match reduced.kind() {
        ExprKind::App(_, _) => {
            let f = whnf_normalize(tc, reduced.get_app_fn(), fuel - 1);
            let args: Vec<Expr> = reduced
                .get_app_args()
                .iter()
                .map(|a| whnf_normalize(tc, a, fuel - 1))
                .collect();
            Expr::apps(f, args)
        }
        _ => reduced.clone(),
    }
}

/// Specialise a projected class law `law_term : law_ty` so it proves `goal`.
///
/// Peels `law_ty`'s Pi telescope, instantiating each binder with a fresh
/// sentinel fvar (a "hole") so the conclusion is closed, then first-order
/// matches the conclusion against `goal` to recover each binder's argument, and
/// returns `law_term` applied to those arguments. Returns `None` when the law is
/// not a Pi (nothing to specialise), when the match fails, or when some binder's
/// argument could not be recovered from the goal. This is a *heuristic* to find
/// arguments; the caller's kernel re-check (`infer_type` + `is_def_eq`) is the
/// soundness gate, so a wrong guess is rejected there, never returned.
fn specialize_law_to_goal(law_ty: &Expr, law_term: &Expr, goal: &Expr) -> Option<Expr> {
    const MAX_BINDERS: usize = 8;
    let mut holes: Vec<FVarId> = Vec::new();
    let mut body = law_ty.clone();
    while let ExprKind::Pi(_, _dom, cod) = body.strip_mdata().kind() {
        if holes.len() >= MAX_BINDERS {
            break;
        }
        let id = FVarId::new(LAW_HOLE_FVAR_BASE + holes.len() as u64);
        holes.push(id);
        body = cod.instantiate(&Expr::fvar(id));
    }
    if holes.is_empty() {
        return None;
    }
    let hole_set: HashSet<FVarId> = holes.iter().copied().collect();
    let mut assign: HashMap<FVarId, Expr> = HashMap::new();
    if !first_order_match(&body, goal, &hole_set, &mut assign, 0) {
        return None;
    }
    let mut args: Vec<Expr> = Vec::with_capacity(holes.len());
    for hole in &holes {
        args.push(assign.get(hole)?.clone());
    }
    Some(Expr::apps(law_term.clone(), args))
}

/// First-order match `pattern` against `term`, treating the fvars in `holes` as
/// pattern variables. A hole matches any subterm (recording the assignment,
/// checking consistency on a repeated hole); every other node must match
/// head-to-head structurally. Universe levels are ignored at `Const`/`Sort`
/// leaves — a level mismatch (if any) is caught by the caller's kernel re-check,
/// not here. Returns `true` iff a consistent assignment was found.
fn first_order_match(
    pattern: &Expr,
    term: &Expr,
    holes: &HashSet<FVarId>,
    assign: &mut HashMap<FVarId, Expr>,
    depth: u32,
) -> bool {
    const MAX_DEPTH: u32 = 64;
    if depth > MAX_DEPTH {
        return false;
    }
    let pattern = pattern.strip_mdata();
    let term = term.strip_mdata();
    if let ExprKind::FVar(id) = pattern.kind() {
        if holes.contains(id) {
            return match assign.get(id) {
                Some(prev) => prev == term,
                None => {
                    assign.insert(*id, term.clone());
                    true
                }
            };
        }
    }
    match (pattern.kind(), term.kind()) {
        (ExprKind::App(pf, pa), ExprKind::App(tf, ta)) => {
            first_order_match(pf, tf, holes, assign, depth + 1)
                && first_order_match(pa, ta, holes, assign, depth + 1)
        }
        (ExprKind::Const(n1, _), ExprKind::Const(n2, _)) => n1 == n2,
        (ExprKind::FVar(a), ExprKind::FVar(b)) => a == b,
        (ExprKind::BVar(a), ExprKind::BVar(b)) => a == b,
        (ExprKind::Sort(_), ExprKind::Sort(_)) => true,
        (ExprKind::Lit(a), ExprKind::Lit(b)) => a == b,
        (ExprKind::Proj(n1, i1, e1), ExprKind::Proj(n2, i2, e2)) => {
            n1 == n2 && i1 == i2 && first_order_match(e1, e2, holes, assign, depth + 1)
        }
        (ExprKind::Pi(_, d1, c1), ExprKind::Pi(_, d2, c2))
        | (ExprKind::Lam(_, d1, c1), ExprKind::Lam(_, d2, c2)) => {
            first_order_match(d1, d2, holes, assign, depth + 1)
                && first_order_match(c1, c2, holes, assign, depth + 1)
        }
        _ => false,
    }
}

/// The injectable hypotheses for one premise `name`: `(hyp_type, closing_const)`
/// pairs.
///
/// * **Monomorphic** premise (no level params): one pair `(C.type, @C)` — the
///   bare constant inhabits its declared type.
/// * **Universe-polymorphic** premise: one pair *per* candidate level, each a
///   uniform instantiation `pᵢ := ℓ` of all level params (capped at
///   [`MAX_LEVEL_CANDIDATES`]). Each pair is `(C.type[p… := ℓ], @C.{ℓ…})`, so the
///   hypothesis type and the closing constant agree by construction; a wrong
///   guess simply fails the caller's kernel re-check (it is never trusted). The
///   uniform-level heuristic (all params to the same level) is not a unifier, but
///   it resolves the common case — e.g. `List.append_nil.{u}` over `List Nat`
///   instantiates `u := 0` from the goal's `List.{0}` level.
fn premise_injection_candidates(
    env: &Environment,
    name: &Name,
    candidates: &[Level],
) -> Vec<(Expr, Expr)> {
    let Some(info) = env.get_const(name) else {
        return Vec::new();
    };
    if info.level_params.is_empty() {
        return vec![(info.type_.clone(), Expr::const_(name.clone(), Vec::new()))];
    }
    let arity = info.level_params.len();
    let mut out = Vec::new();
    for cand in candidates {
        let levels = vec![cand.clone(); arity];
        let hyp_type = info
            .type_
            .instantiate_level_params_direct(&info.level_params, &levels);
        out.push((hyp_type, Expr::const_(name.clone(), levels)));
        if out.len() >= MAX_LEVEL_CANDIDATES {
            break;
        }
    }
    out
}

/// A small, bounded menu of candidate universe levels for instantiating
/// universe-polymorphic injected premises: `Sort 0` plus the distinct
/// (normalised) levels that actually appear in the goal's `Sort`/`Const` nodes.
///
/// Full universe unification is out of scope here; this menu plus the caller's
/// kernel re-check is sufficient to close the common monomorphic-application
/// goals (where the right level is one the goal already mentions) without ever
/// admitting an ill-leveled term.
fn goal_candidate_levels(goal: &Expr) -> Vec<Level> {
    let mut levels = vec![Level::zero()];
    collect_levels(goal, &mut levels, 0);
    levels.truncate(MAX_LEVEL_CANDIDATES);
    levels
}

/// Push the normalised `level` into `out` if not already present.
fn push_unique_level(out: &mut Vec<Level>, level: &Level) {
    let normalized = level.normalize();
    if !out.contains(&normalized) {
        out.push(normalized);
    }
}

/// Collect the (normalised) universe levels appearing in `e`, to a bounded depth.
fn collect_levels(e: &Expr, out: &mut Vec<Level>, depth: u32) {
    const MAX_DEPTH: u32 = 24;
    if depth > MAX_DEPTH {
        return;
    }
    match e.kind() {
        ExprKind::Sort(level) => push_unique_level(out, level),
        ExprKind::Const(_, levels) => {
            for level in levels.iter() {
                push_unique_level(out, level);
            }
        }
        ExprKind::App(f, a) => {
            collect_levels(f, out, depth + 1);
            collect_levels(a, out, depth + 1);
        }
        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
            collect_levels(ty, out, depth + 1);
            collect_levels(body, out, depth + 1);
        }
        ExprKind::MData(_, inner) => collect_levels(inner, out, depth),
        _ => {}
    }
}

/// Validate an oracle-suggested proof term through the kernel type checker.
///
/// Returns `Some(AutomationOutcome::Verified(_))` if the proof term's inferred
/// type is definitionally equal to the goal, `None` otherwise (the candidate
/// is silently discarded and the engine tries the next one).
fn validate_proof_term_candidate(
    env: &Environment,
    goal: &Expr,
    proof_context: Option<&LocalContext>,
    candidate: &crate::oracle::ProofTermCandidate,
    start: Instant,
) -> Option<AutomationOutcome> {
    let tc = match proof_context {
        Some(ctx) => TypeChecker::with_context(env, ctx.clone()),
        None => TypeChecker::new(env),
    };

    let inferred = match tc.infer_type(&candidate.proof_term) {
        Ok(ty) => ty,
        Err(_) => return None,
    };

    if !tc.is_def_eq(&inferred, goal) {
        return None;
    }

    let description = candidate
        .description
        .clone()
        .unwrap_or_else(|| "oracle proof term".to_string());

    Some(AutomationOutcome::Verified(Box::new(ProofResult::new(
        candidate.proof_term.clone(),
        description,
        elapsed_ms(start),
        proof_context.cloned(),
    ))))
}

fn elapsed_ms(start: Instant) -> u64 {
    start.elapsed().as_millis() as u64
}

/// Strength rank of a non-`Verified` outcome (`Verified` short-circuits and is
/// never merged). Refuted (a counter-model) is the most informative, then a
/// strategy that established information (`Unverified`), then bare `Unknown`.
fn outcome_rank(outcome: &AutomationOutcome) -> u8 {
    match outcome {
        AutomationOutcome::Verified(_) => 3,
        AutomationOutcome::Refuted { .. } => 2,
        AutomationOutcome::Unverified { .. } => 1,
        AutomationOutcome::Unknown { .. } => 0,
    }
}

/// Keep the stronger of two non-proof outcomes (higher [`outcome_rank`]); on a
/// tie keep the first-seen (`prev`) so the reported source stays stable.
fn merge_outcome(
    prev: Option<AutomationOutcome>,
    candidate: AutomationOutcome,
) -> AutomationOutcome {
    match prev {
        None => candidate,
        Some(prev) => {
            if outcome_rank(&candidate) > outcome_rank(&prev) {
                candidate
            } else {
                prev
            }
        }
    }
}

/// Emit a `solver-attempt-record-v1` for one engine outcome.
///
/// No-op unless telemetry is enabled *and* the obligation key was computed.
/// `Verified` records carry the proof-term digest so a future cache layer can
/// return a re-checkable proof; non-proof outcomes are advisory (design §2.4).
fn emit_outcome_telemetry(
    obligation: Option<&str>,
    engine: SolverEngine,
    attempt_start: Instant,
    outcome: &AutomationOutcome,
    smt_stats: Option<SmtStatsSnapshot>,
) {
    let proof_term = match outcome {
        AutomationOutcome::Verified(result) => Some(result.proof_term()),
        AutomationOutcome::Unverified { .. }
        | AutomationOutcome::Refuted { .. }
        | AutomationOutcome::Unknown { .. } => None,
    };
    let result = outcome_to_result(outcome);
    emit_attempt_telemetry(
        obligation,
        engine,
        attempt_start,
        (result, proof_term),
        smt_stats,
    );
}

/// Map a fixed-pipeline [`AutomationOutcome`] to a record [`AttemptResult`].
fn outcome_to_result(outcome: &AutomationOutcome) -> AttemptResult {
    match outcome {
        AutomationOutcome::Verified(_) => AttemptResult::Proved,
        AutomationOutcome::Refuted { .. } => AttemptResult::Sat,
        // No verdict bit was established and no proof term was produced. We
        // record `Unknown` rather than `Noproof`/`Timeout` because the
        // fixed-pipeline outcome does not distinguish budget exhaustion from
        // genuine indeterminacy; this stays an advisory hint either way.
        AutomationOutcome::Unverified { .. } | AutomationOutcome::Unknown { .. } => {
            AttemptResult::Unknown
        }
    }
}

/// Lowest-level emission shim: assemble [`AttemptTelemetry`] and write it.
///
/// The proof-term digest is computed here, only on the proof-bearing path and
/// only when telemetry is live (the obligation key is `Some`).
fn emit_attempt_telemetry(
    obligation: Option<&str>,
    engine: SolverEngine,
    attempt_start: Instant,
    result: (AttemptResult, Option<&Expr>),
    smt_stats: Option<SmtStatsSnapshot>,
) {
    let Some(obligation) = obligation else {
        return;
    };
    let (result, proof_term) = result;
    let proof_term_digest = proof_term.and_then(|term| obligation_digest(term).ok());
    telemetry::emit(AttemptTelemetry {
        obligation_digest: obligation.to_string(),
        engine,
        result,
        wall_ms: elapsed_ms(attempt_start),
        proof_term_digest,
        smt_stats,
        cache_outcome: crate::solver_cache::record::CacheOutcome::Miss,
    });
}
