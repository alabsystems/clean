// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The first autoprove swarm worker: loop the in-repo `clean-auto` hammer over
//! a stream of obligations and graduate every solved goal through the C1
//! kernel-recheck trust gate.
//!
//! # Trust contract
//!
//! A goal is counted `proved` **only** when the kernel itself re-checks the
//! hammer's proof term WITH its value via
//! [`crate::graduate::recheck::recheck_and_classify`] and returns a
//! foundational-only verdict ([`RecheckVerdict::is_foundational`]). The hammer
//! producing a `ProofResult` is necessary but never sufficient: the proof term
//! is reconstructed, wrapped as a [`Declaration::Theorem`], and replayed into a
//! FRESH recheck environment. The kernel's `add_decl` is the only road to the
//! verdict — the worker never stamps a verdict of its own.
//!
//! # Pipeline (per obligation)
//!
//! 1. [`ObligationSource`] yields a `(name, goal)` pair.
//! 2. Classify the goal:
//!    * **Tier-1** ([`tier1_classify`]): a closed proposition with no top-level
//!      `∀`/`Π` (Prop-typed, shallow, no universe-polymorphism). The hammer is
//!      run on the goal directly.
//!    * **Tier-2** ([`tier2_classify`]): a goal tier-1 rejected with
//!      `HasTopLevelPi` — a `∀ (xs), Body` telescope — whose `Body`, once the
//!      leading binders are peeled into fresh free variables, is itself
//!      tier-1-shaped. This is ~92% of real corpus lemmas. The hammer is run on
//!      the OPENED body in the peeled [`clean_kernel::LocalContext`], then the
//!      proof term is re-abstracted ([`reabstract_over_binders`]) back over the
//!      binders to recover a closed proof of the original `∀` type.
//!
//!    Any other tier-1 rejection is a hard `skip`.
//! 3. The PREMISE-GUIDED hammer
//!    ([`clean_auto::AutomationEngine::auto_prove_with_premises`]) is run with a
//!    short timeout. A [`premises::PremisePool`] seeded from the search
//!    environment's lemmas (prelude/native theorems + any already-proved decls)
//!    supplies MePo-selected premises so superposition/SMT can discharge goals
//!    that FOLLOW FROM other lemmas, not only goals that close from nothing.
//!    `None` ⇒ `miss`. The proof term references each used premise as a
//!    synthetic free variable; [`premises::closeover_premise_fvars`] substitutes
//!    each back over the actual environment CONSTANT it stands for, recovering a
//!    closed value. Premises guide the SEARCH only — the kernel re-checks the
//!    closed term, so soundness is identical (a premise-misled wrong proof is
//!    `KernelRejected`; a domain-axiom premise surfaces as `AxiomDependent`).
//! 4. The (re-abstracted, for tier-2) proof term is wrapped as a
//!    [`Declaration::Theorem`] of the ORIGINAL goal type and run through the C1
//!    gate against a fresh overlay environment. The kernel type-checks the value
//!    against the `∀` type itself, so a wrong tier-2 re-abstraction is
//!    `KernelRejected` (fail-closed) — the gate, not the worker, certifies. A
//!    foundational verdict ⇒ `proved`; an axiom-dependent or kernel-rejected
//!    verdict ⇒ `miss`.

mod obligation;
mod premises;
mod tier1;
mod tier2;
mod timeout;

pub use obligation::{DemoSource, ObligationSource, ShardObligations};
pub use tier1::{tier1_classify, Tier1Outcome};
pub use tier2::{reabstract_over_binders, tier2_classify, Tier2Outcome, Tier2Plan};

use premises::{closeover_premise_fvars, prove_with_premises, PremisePool};

use std::sync::Arc;
use std::time::Duration;

use clean_kernel::{Declaration, Environment, Expr, Name};

use crate::graduate::recheck::recheck_and_classify;

/// One obligation handed to the worker: a name to register the proved theorem
/// under, plus the goal proposition to discharge.
#[derive(Clone, Debug)]
pub struct Obligation {
    /// Name the proved theorem is registered under in the recheck environment.
    pub name: String,
    /// The goal proposition (a kernel [`Expr`]).
    pub goal: Expr,
}

impl Obligation {
    /// Construct an obligation.
    #[must_use]
    pub fn new(name: impl Into<String>, goal: Expr) -> Self {
        Self {
            name: name.into(),
            goal,
        }
    }
}

/// Why one obligation did not graduate (everything except `Proved`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Miss {
    /// The classifier rejected the goal before the hammer ran (a tier-1
    /// rejection, or a `∀` goal tier-2 could not peel to a tier-1 body).
    Skipped(Tier1Outcome),
    /// The hammer returned no proof within the timeout.
    HammerNoProof,
    /// The hammer produced a term but the C1 gate rejected it (kernel error).
    GateRejected(String),
    /// The C1 gate accepted the term but its closure is not foundational-only:
    /// the proof leans on a domain axiom, so it is NOT counted proved.
    AxiomDependent(Vec<String>),
}

/// Which classifier admitted a proved goal — the tier whose path produced the
/// kernel-verified proof. Carried on [`Attempt::Proved`] so a run can report the
/// tier-2 lift (the ∀-quantified yield) distinctly from the tier-1 baseline.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Tier {
    /// A closed, quantifier-free goal proved directly (tier-1).
    Tier1,
    /// A `∀`-quantified goal peeled, proved opened, and re-abstracted (tier-2).
    Tier2,
}

/// The outcome of attempting one obligation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Attempt {
    /// The kernel re-checked the proof term WITH its value and the transitive
    /// axiom closure is foundational-only. This is the only `proved` verdict,
    /// and it is the kernel's, not the worker's. Carries the [`Tier`] whose path
    /// produced the proof.
    Proved(Tier),
    /// Anything else; see [`Miss`].
    Missed(Miss),
}

/// Running tally across a worker run.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Tally {
    /// Goals offered by the source.
    pub attempted: u64,
    /// Goals accepted by the classifier (tier-1 or tier-2; the hammer ran).
    pub kept: u64,
    /// Goals the classifier rejected before the hammer ran.
    pub skipped: u64,
    /// Goals the kernel re-checked to a foundational-only verdict.
    pub proved: u64,
    /// Of [`Tally::proved`], the count whose proof came through the tier-2
    /// (∀-quantified) path — the tier-2 yield lift over the tier-1 baseline.
    pub proved_tier2: u64,
    /// Kept goals that did not graduate (no proof, gate rejection, or
    /// axiom-dependent closure).
    pub missed: u64,
}

impl Tally {
    /// Fold one attempt into the tally.
    pub(crate) fn record(&mut self, attempt: &Attempt) {
        self.attempted += 1;
        match attempt {
            Attempt::Proved(tier) => {
                self.kept += 1;
                self.proved += 1;
                if *tier == Tier::Tier2 {
                    self.proved_tier2 += 1;
                }
            }
            Attempt::Missed(Miss::Skipped(_)) => {
                self.skipped += 1;
            }
            Attempt::Missed(_) => {
                self.kept += 1;
                self.missed += 1;
            }
        }
    }
}

/// Which prover channel the worker drives a goal through. The control knob for
/// the premise-lift A/B: both modes run the IDENTICAL classifier, environment,
/// timeout, and C1 gate — only the premise channel differs, so a count
/// difference between two runs is attributable to premises alone.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum ProverMode {
    /// Premise-guided ATP: MePo selects a relevant premise subset from the
    /// pool and hands them to superposition/SMT as hypothesis clauses. The
    /// default — the lifted path.
    #[default]
    PremiseGuided,
    /// The bare hammer: no premises offered (empty hypotheses, empty database).
    /// This is the BASELINE control — `auto_prove`-equivalent reachability, so
    /// it only discharges goals that close from nothing.
    Bare,
}

/// Which prelude the worker's search + recheck environments are built from —
/// the structural fix for WALL 1 (missing hierarchy).
///
/// The bare import prelude ([`Environment::try_with_prelude_for_import`]) lacks
/// the algebra hierarchy (`Monoid`, `Group`, `Semiring`, …), so a real Mathlib
/// algebra goal cannot even be TYPED by the recheck environment — it is skipped
/// upstream of the prover regardless of the universe-polymorphism fix. The
/// [`Hierarchy::Algebra`] mode instead seeds the in-repo algebra structures (the
/// kernel's `Monoid`/`Group`/`Ring` hierarchy, the local stand-in for a loaded
/// `.olean` module dep-closure), so a `∀ {M} [Monoid M] (a : M), …` goal types,
/// peels, proves, and graduates against an environment that knows `Monoid`.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum Hierarchy {
    /// Bare import prelude only — the historical default. No algebra hierarchy.
    #[default]
    Bare,
    /// Import prelude PLUS the in-repo algebra structure hierarchy (`Monoid`,
    /// `Group`, `Ring`, …). The environment a universe-polymorphic algebra goal
    /// needs to type and graduate.
    Algebra,
}

/// Configuration for one worker run.
#[derive(Clone, Copy, Debug)]
pub struct WorkerConfig {
    /// Per-goal hammer timeout.
    pub timeout: Duration,
    /// Stop after offering at most this many obligations (`None` = no cap).
    pub limit: Option<u64>,
    /// Seed the native lemma batches into the base environment so the hammer
    /// has overlay lemmas to draw on.
    pub seed_native: bool,
    /// Which prover channel to drive each goal through (the premise-lift A/B
    /// control). [`ProverMode::PremiseGuided`] by default.
    pub mode: ProverMode,
    /// Which prelude the search + recheck environments carry (WALL 1). The
    /// algebra hierarchy is required for real universe-polymorphic Mathlib goals
    /// to type. [`Hierarchy::Bare`] by default (the historical behaviour).
    pub hierarchy: Hierarchy,
}

impl Default for WorkerConfig {
    fn default() -> Self {
        Self {
            timeout: Duration::from_secs(5),
            limit: None,
            seed_native: false,
            mode: ProverMode::PremiseGuided,
            hierarchy: Hierarchy::Bare,
        }
    }
}

/// Errors raised while setting up or running the worker.
#[derive(Debug, thiserror::Error)]
pub enum WorkerError {
    /// The base / recheck environment could not be built from the prelude.
    #[error("environment setup failed: {0}")]
    Env(#[from] clean_kernel::EnvError),
    /// The obligation source failed to produce obligations.
    #[error("obligation source failed: {0}")]
    Source(String),
}

/// The autoprove worker: a base environment for the hammer plus a fresh
/// recheck environment that every proved theorem is graduated into.
pub struct SwarmWorker {
    /// Lemma-rich environment the hammer searches against. Held behind an `Arc`
    /// so it can be SHARED into the prover's per-goal timeout worker thread by
    /// refcount bump rather than deep-cloned (the corpus environment is large).
    /// Test-only mutators use [`Arc::make_mut`].
    base: Arc<Environment>,
    /// Fresh environment proved theorems are graduated into (the C1 gate's
    /// `add_decl` target). Distinct from `base`: a graduation that mutated the
    /// search environment would let one proof's side effects leak into the
    /// next goal's search.
    recheck: Environment,
    /// Premise pool seeded from `base`: the proof-carrying lemmas the hammer can
    /// follow a goal FROM, plus the MePo database that scores them per goal.
    /// Built once — `base` is immutable across a run, so the pool is stable.
    premises: PremisePool,
    config: WorkerConfig,
}

impl SwarmWorker {
    /// Build a worker: a prelude-seeded base environment (optionally with the
    /// native lemma batches) and a matching fresh recheck environment.
    ///
    /// # Errors
    ///
    /// Returns [`WorkerError::Env`] if the prelude cannot be built.
    pub fn new(config: WorkerConfig) -> Result<Self, WorkerError> {
        let base = build_environment(config.seed_native, config.hierarchy)?;
        let recheck = build_environment(config.seed_native, config.hierarchy)?;
        let premises = PremisePool::from_env(&base);
        Ok(Self {
            base: Arc::new(base),
            recheck,
            premises,
            config,
        })
    }

    /// Number of pooled premises (proof-carrying lemmas) the premise-guided
    /// hammer can draw on — exposed for tests and run diagnostics.
    #[must_use]
    pub fn premise_count(&self) -> usize {
        self.premises.len()
    }

    /// Register a kernel-checked premise theorem into BOTH the search and
    /// recheck environments and rebuild the premise pool, so a goal can follow
    /// from it. Test-only: it kernel-checks `value : type_` via the same
    /// `add_decl` the C1 gate uses, so the seeded premise is a genuine
    /// foundational lemma (no `add_decl_structural` shortcut).
    #[cfg(test)]
    fn seed_checked_premise(
        &mut self,
        name: &str,
        type_: Expr,
        value: Expr,
    ) -> Result<(), clean_kernel::EnvError> {
        let decl = Declaration::Theorem {
            name: Name::from_string(name),
            level_params: Vec::new(),
            type_,
            value,
        };
        // `Arc::make_mut` clones the shared environment only if another handle
        // (a still-running prover thread) is alive; at test-seed time none is,
        // so this mutates in place.
        Arc::make_mut(&mut self.base).add_decl(decl.clone())?;
        self.recheck.add_decl(decl)?;
        self.premises = PremisePool::from_env(self.base.as_ref());
        Ok(())
    }

    /// The current base (search) environment — exposed so a caller can seed
    /// extra obligation-specific declarations before a run.
    #[must_use]
    pub fn base_env(&self) -> &Environment {
        self.base.as_ref()
    }

    /// Attempt a single obligation end-to-end: classify (tier-1 OR tier-2),
    /// hammer, re-abstract if tier-2, then the C1 kernel-recheck gate.
    ///
    /// The `proved` verdict is the kernel's: it is returned only when
    /// [`recheck_and_classify`] reports a foundational-only closure for the
    /// wrapped theorem. Whatever value the worker constructs — a closed tier-1
    /// proof term or a re-abstracted tier-2 `λ`-telescope — the kernel
    /// type-checks it against the ORIGINAL goal type; a wrong re-abstraction is
    /// `KernelRejected` (fail-closed), so the gate, not the worker, certifies.
    pub fn attempt(&mut self, obligation: &Obligation) -> Attempt {
        // Tier-1: closed, quantifier-free goals go straight to the hammer.
        match tier1_classify(self.base.as_ref(), &obligation.goal) {
            Tier1Outcome::Accept => return self.attempt_tier1(obligation),
            // A leading `∀` is the tier-2 frontier — try peeling it. Every other
            // tier-1 rejection is a hard skip (not-a-Prop, too deep, …).
            Tier1Outcome::HasTopLevelPi => {}
            other => return Attempt::Missed(Miss::Skipped(other)),
        }
        self.attempt_tier2(obligation)
    }

    /// Tier-1 path: prove the closed goal with the premise-guided hammer, close
    /// any premise-introduced free variables back over their environment
    /// constants, wrap, gate.
    fn attempt_tier1(&mut self, obligation: &Obligation) -> Attempt {
        let Some(proof) = prove_with_premises(
            &self.base,
            &self.premises,
            &obligation.goal,
            self.config.timeout,
            None,
            self.config.mode == ProverMode::PremiseGuided,
            &[],
        ) else {
            return Attempt::Missed(Miss::HammerNoProof);
        };

        // The premise-guided hammer references each used premise as a synthetic
        // free variable in `proof_context`. Close those back over the actual
        // environment constant they stand for to recover a CLOSED theorem value.
        // No proof context ⇒ the goal closed from nothing (the proof term is
        // already closed). A tier-1 goal is monomorphic, so no goal levels.
        let value = match proof.proof_context() {
            None => proof.proof_term().clone(),
            Some(ctx) => {
                // Tier-1 has no peeled binders, so EVERY context decl must be a
                // premise; an unmappable decl means an open term we cannot
                // honestly wrap — fail closed.
                let Some(value) =
                    closeover_premise_fvars(&self.premises, proof.proof_term(), ctx, &[], &[])
                else {
                    return Attempt::Missed(Miss::HammerNoProof);
                };
                value
            }
        };

        self.gate(
            &obligation.name,
            &obligation.goal,
            value,
            Vec::new(),
            Tier::Tier1,
        )
    }

    /// Tier-2 path: peel the `∀` telescope into fresh free variables, prove the
    /// opened body in that local context, re-abstract the proof term back over
    /// the binders, and gate the re-abstracted `λ`-telescope against the
    /// ORIGINAL `∀` type.
    fn attempt_tier2(&mut self, obligation: &Obligation) -> Attempt {
        let plan = match tier2_classify(self.base.as_ref(), &obligation.goal) {
            Tier2Outcome::Accept(plan) => plan,
            // Tier-2 declined the `∀`: not peelable to a tier-1 body. Skip with
            // the tier-1 verdict that surfaced it (it really did lead with a Π).
            _ => return Attempt::Missed(Miss::Skipped(Tier1Outcome::HasTopLevelPi)),
        };

        // The goal's universe params, as concrete levels, instantiate any
        // universe-polymorphic premise (e.g. the algebra `mul_one` lemmas) at the
        // goal's universes — and pin the levels the close-over applies to the
        // chosen premise const.
        let goal_levels: Vec<clean_kernel::Level> = plan
            .level_params
            .iter()
            .cloned()
            .map(clean_kernel::Level::param)
            .collect();

        // Prove the OPENED body against the peeled local context, premise-guided.
        let Some(proof) = prove_with_premises(
            &self.base,
            &self.premises,
            &plan.body,
            self.config.timeout,
            Some(&plan.local_ctx),
            self.config.mode == ProverMode::PremiseGuided,
            &goal_levels,
        ) else {
            return Attempt::Missed(Miss::HammerNoProof);
        };

        // The opened-body proof may reference BOTH the peeled `∀` binders (their
        // fvars, handled by re-abstraction below) and any premises the hammer
        // used (synthetic context fvars). Close the premise fvars back over their
        // environment constants first — leaving the peeled binders' fvars in
        // `plan.fvars` untouched for re-abstraction.
        let closed_body = match proof.proof_context() {
            None => proof.proof_term().clone(),
            Some(ctx) => {
                let Some(closed) = closeover_premise_fvars(
                    &self.premises,
                    proof.proof_term(),
                    ctx,
                    &plan.fvars,
                    &goal_levels,
                ) else {
                    return Attempt::Missed(Miss::HammerNoProof);
                };
                closed
            }
        };

        // Re-abstract over the peeled binders to recover a term of the original
        // `∀` type. If the body proof leaned on free variables BEYOND the peeled
        // binders and the premises we closed, the re-abstracted term still
        // mentions them; the kernel rejects an open declaration value, so we
        // fail closed at the gate rather than guess.
        let value = reabstract_over_binders(&plan, &closed_body);
        // The peeled telescope may include TYPE binders, so the re-abstracted
        // term is universe-polymorphic over the goal's params. Stamp them on the
        // theorem: the kernel re-checks the polymorphic `λ` against the original
        // `∀`-type with exactly these params in scope — a mismatch is
        // KernelRejected (sound by construction).
        self.gate(
            &obligation.name,
            &obligation.goal,
            value,
            plan.level_params.clone(),
            Tier::Tier2,
        )
    }

    /// Wrap `(name, type_, value)` as a theorem and run it through the C1
    /// kernel-recheck gate. `Proved(tier)` is returned ONLY on a
    /// foundational-only verdict — the kernel type-checks `value` against
    /// `type_` itself, with `level_params` in scope. `tier` records which
    /// classifier produced the proof.
    fn gate(
        &mut self,
        name: &str,
        type_: &Expr,
        value: Expr,
        level_params: Vec<Name>,
        tier: Tier,
    ) -> Attempt {
        let decl = Declaration::Theorem {
            name: Name::from_string(name),
            level_params,
            type_: type_.clone(),
            value,
        };

        match recheck_and_classify(&mut self.recheck, decl) {
            Ok(verdict) if verdict.is_foundational() => Attempt::Proved(tier),
            Ok(verdict) => Attempt::Missed(Miss::AxiomDependent(verdict.domain_axioms)),
            Err(err) => Attempt::Missed(Miss::GateRejected(err.to_string())),
        }
    }

    /// Drive a whole obligation source to exhaustion (or the configured
    /// limit), returning the final [`Tally`]. `on_attempt` is invoked after
    /// each obligation with the running tally so callers can print progress.
    ///
    /// # Errors
    ///
    /// Propagates [`WorkerError::Source`] if the source yields an error.
    pub fn run<S, F>(&mut self, mut source: S, mut on_attempt: F) -> Result<Tally, WorkerError>
    where
        S: ObligationSource,
        F: FnMut(&Obligation, &Attempt, &Tally),
    {
        let mut tally = Tally::default();
        while let Some(result) = source.next_obligation() {
            if let Some(limit) = self.config.limit {
                if tally.attempted >= limit {
                    break;
                }
            }
            let obligation = result.map_err(WorkerError::Source)?;
            let attempt = self.attempt(&obligation);
            tally.record(&attempt);
            on_attempt(&obligation, &attempt, &tally);
        }
        Ok(tally)
    }
}

/// Build the worker's search / recheck environment, optionally seeding the
/// native lemma batches so the hammer has overlay lemmas to draw on.
///
/// The `hierarchy` selects the prelude (WALL 1):
///
/// * [`Hierarchy::Bare`] — [`Environment::try_with_prelude_for_import`], the
///   bare import prelude. No algebra hierarchy; a `∀ {M} [Monoid M], …` goal
///   cannot be typed by this environment.
/// * [`Hierarchy::Algebra`] — [`Environment::try_with_prelude`], which seeds the
///   in-repo `Semigroup`/`Monoid`/`Group`/`Ring` structure hierarchy (the local
///   stand-in for a loaded `.olean` module dep-closure). A universe-polymorphic
///   algebra goal types, peels, proves, and graduates against it.
fn build_environment(
    seed_native: bool,
    hierarchy: Hierarchy,
) -> Result<Environment, clean_kernel::EnvError> {
    let mut env = match hierarchy {
        Hierarchy::Bare => Environment::try_with_prelude_for_import()?,
        Hierarchy::Algebra => Environment::try_with_prelude()?,
    };
    if seed_native {
        crate::build_library_native::seed_native_environment(&mut env);
    }
    Ok(env)
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::Expr;

    /// A constructed tier-1 goal the hammer discharges: the reflexive equality
    /// `@Eq.{1} Nat 0 0`. It is a closed proposition with no top-level `∀`, so
    /// the tier-1 filter accepts it; the SMT bridge's reflexivity lane proves
    /// it with `Eq.refl`.
    fn refl_goal() -> Expr {
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_str_levels("Eq", vec![Level::succ(Level::zero())]),
                    Expr::const_str("Nat"),
                ),
                Expr::nat_lit(0),
            ),
            Expr::nat_lit(0),
        )
    }

    #[test]
    fn test_worker_constructed_tier1_goal_proves_and_kernel_accepts() {
        let mut worker =
            SwarmWorker::new(WorkerConfig::default()).expect("prelude environment must build");
        let goal = refl_goal();

        // Tier-1 must ACCEPT the constructed goal (closed Prop, no top-level Pi).
        assert_eq!(
            tier1_classify(worker.base_env(), &goal),
            Tier1Outcome::Accept,
            "constructed reflexive equality must pass the tier-1 filter"
        );

        let obligation = Obligation::new("SwarmWorker.smoke_refl", goal);
        let attempt = worker.attempt(&obligation);

        // The ONLY accepted verdict is the kernel's: `Attempt::Proved` is
        // returned exclusively on a foundational `recheck_and_classify`. A
        // closed goal is proved via the tier-1 path.
        assert_eq!(
            attempt,
            Attempt::Proved(Tier::Tier1),
            "the hammer must prove the goal AND the C1 kernel recheck must accept it; got {attempt:?}"
        );
    }

    /// A tier-2 goal the hammer discharges after intro: `∀ (n : Nat),
    /// @Eq.{1} Nat n n`. Tier-1 rejects it (`HasTopLevelPi`); tier-2 peels the
    /// `n` binder, the reflexivity lane proves the opened `n = n`, and the
    /// re-abstracted `fun n => Eq.refl n` kernel-typechecks against the ∀ type.
    fn forall_refl_goal() -> Expr {
        let eq_body = Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_str_levels("Eq", vec![Level::succ(Level::zero())]),
                    Expr::const_str("Nat"),
                ),
                Expr::bvar(0),
            ),
            Expr::bvar(0),
        );
        Expr::pi(
            clean_kernel::BinderInfo::Default,
            Expr::const_str("Nat"),
            eq_body,
        )
    }

    #[test]
    fn test_worker_tier2_forall_goal_proves_and_kernel_accepts() {
        let mut worker =
            SwarmWorker::new(WorkerConfig::default()).expect("prelude environment must build");
        let goal = forall_refl_goal();

        // Tier-1 MUST reject the ∀ goal — this is precisely the 92% frontier.
        assert_eq!(
            tier1_classify(worker.base_env(), &goal),
            Tier1Outcome::HasTopLevelPi,
            "a leading ∀ is tier-1 out of scope by construction"
        );
        // Tier-2 MUST accept it (closed telescope over a Prop body).
        assert!(
            matches!(
                tier2_classify(worker.base_env(), &goal),
                Tier2Outcome::Accept(_)
            ),
            "∀ (n:Nat), n = n must pass the tier-2 filter"
        );

        let obligation = Obligation::new("SwarmWorker.tier2_forall_refl", goal);
        let attempt = worker.attempt(&obligation);

        // The ONLY accepted verdict is the kernel's: the re-abstracted ∀-proof
        // must type-check against the ∀ type AND be foundational-only, via the
        // tier-2 path.
        assert_eq!(
            attempt,
            Attempt::Proved(Tier::Tier2),
            "tier-2 must prove the ∀ goal AND the C1 kernel recheck must accept the re-abstracted proof; got {attempt:?}"
        );
    }

    /// Soundness guard: the gate still DISCRIMINATES under tier-2. A `∀` goal
    /// that is a TRUE Prop but UNPROVABLE-as-reflexivity must NOT come back
    /// `Proved` — it must be a miss, never a false graduation.
    #[test]
    fn test_worker_tier2_false_goal_is_not_proved() {
        let mut worker =
            SwarmWorker::new(WorkerConfig::default()).expect("prelude environment must build");
        // `∀ (n : Nat), @Eq.{1} Nat n (Nat.succ n)` — well-typed Prop, FALSE,
        // so no proof term exists; the gate must never stamp it Proved.
        let eq_body = Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_str_levels("Eq", vec![Level::succ(Level::zero())]),
                    Expr::const_str("Nat"),
                ),
                Expr::bvar(0),
            ),
            Expr::app(Expr::const_str("Nat.succ"), Expr::bvar(0)),
        );
        let goal = Expr::pi(
            clean_kernel::BinderInfo::Default,
            Expr::const_str("Nat"),
            eq_body,
        );
        let obligation = Obligation::new("SwarmWorker.tier2_false_goal", goal);
        let attempt = worker.attempt(&obligation);
        assert!(
            !matches!(attempt, Attempt::Proved(_)),
            "a false ∀ goal must never graduate; got {attempt:?}"
        );
    }

    /// The lifted ceiling (was: pinned dead-end). A real Mathlib algebra lemma is
    /// universe-POLYMORPHIC and typeclass-parameterised: it leads with a
    /// `∀ {G : Type u}, …` binder. The premise-guided swarm on the
    /// `Mathlib.Algebra.Group.Basic` shard (471 Axiomatized goals: `mul_one`,
    /// `inv_inv`, `zpow_add`, …) previously skipped EVERY one of them at this
    /// exact wall — `tier2_classify` rejected the leading `Type u` binder as
    /// `BadBinderType(UniversePolymorphic)` before the prover ever saw it.
    ///
    /// WALL 2 lifts that: the tier-3 peel admits leading TYPE binders and
    /// extracts their universe params. The same `∀ {G : Type u} (a : G), a = a`
    /// goal that used to be the wall is now tier-2 ACCEPTED with `level_params =
    /// [u]`. (The earlier-than-prover binding constraint is gone; whether the ATP
    /// then closes a given body is the prover's separate concern.)
    #[test]
    fn test_worker_universe_polymorphic_algebra_goal_is_now_accepted() {
        let worker =
            SwarmWorker::new(WorkerConfig::default()).expect("prelude environment must build");
        // `∀ {G : Type u} (a : G), @Eq.{u+1} G a a` — the leading `Type u` binder
        // that used to be the universe-polymorphic wall. (G : Type u = Sort(u+1),
        // so equality on G is at level u+1.)
        let u = || Level::param(Name::from_string("u"));
        let eq_body = Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_str_levels("Eq", vec![Level::succ(u())]),
                    Expr::bvar(1),
                ),
                Expr::bvar(0),
            ),
            Expr::bvar(0),
        );
        let goal = Expr::pi(
            clean_kernel::BinderInfo::Implicit,
            Expr::sort(Level::succ(u())),
            Expr::pi(clean_kernel::BinderInfo::Default, Expr::bvar(0), eq_body),
        );
        // The wall is GONE: the universe-polymorphic goal is tier-2 accepted and
        // its universe param u is extracted.
        let outcome = tier2_classify(worker.base_env(), &goal);
        let Tier2Outcome::Accept(plan) = outcome else {
            panic!("a Type-u-led goal must now be tier-2 accepted, not walled; got {outcome:?}");
        };
        assert_eq!(
            plan.level_params,
            vec![Name::from_string("u")],
            "the leading Type u binder's universe param must be extracted"
        );
        assert_eq!(
            plan.fvars.len(),
            2,
            "both the Type binder and the value binder are peeled"
        );
    }

    #[test]
    fn test_worker_demo_run_tally_has_at_least_one_proof() {
        let mut worker =
            SwarmWorker::new(WorkerConfig::default()).expect("prelude environment must build");
        let tally = worker
            .run(DemoSource::default(), |_, _, _| {})
            .expect("demo run must not error");
        assert!(tally.attempted >= 1, "demo source must offer obligations");
        assert!(
            tally.proved >= 1,
            "at least one demo obligation must graduate through the kernel: {tally:?}"
        );
        // Conservation: every attempt is exactly one of proved / missed /
        // skipped (kept = proved + missed).
        assert_eq!(tally.kept, tally.proved + tally.missed);
        assert_eq!(tally.attempted, tally.kept + tally.skipped);
    }

    // ---- hard per-goal timeout: the loop never hangs on one goal -------------

    /// A deliberately hard tier-1 goal: the FALSE equality `@Eq.{1} Nat 0 1`.
    /// No proof exists, so the premise-guided prover has nothing to close and
    /// spends its whole search budget grinding before giving up — the kind of
    /// goal that, without a hard wall in the WORKER loop, can run past the
    /// prover's between-iteration deadline and stall the batch.
    fn hard_false_goal() -> Expr {
        nat_eq(Expr::nat_lit(0), Expr::nat_lit(1))
    }

    /// End-to-end progress guarantee: a hard goal that consumes its whole
    /// timeout budget must NOT graduate AND must NOT stop the run — the loop
    /// continues and proves a subsequent EASY goal. This is the batch-level
    /// statement of the hard-timeout contract proved deterministically at the
    /// mechanism level in [`super::timeout`]'s tests.
    #[test]
    fn test_worker_hard_goal_times_out_and_loop_proves_next_easy_goal() {
        // A short per-goal wall: long enough for the trivial refl goal to close,
        // short enough that the run finishes promptly even though the hard goal
        // burns its full budget. The hard wall in the worker loop guarantees the
        // loop regains control regardless.
        let mut worker = SwarmWorker::new(WorkerConfig {
            timeout: Duration::from_millis(500),
            ..WorkerConfig::default()
        })
        .expect("prelude environment must build");

        // Goal order: the HARD (false, time-burning) goal FIRST, then an EASY
        // reflexive goal the worker must still reach and graduate.
        let easy = Obligation::new("SwarmWorker.timeout_easy_refl", refl_goal());
        let hard = Obligation::new("SwarmWorker.timeout_hard_false", hard_false_goal());
        let source = DemoSource::new(vec![hard, easy]);

        let run_start = std::time::Instant::now();
        let tally = worker
            .run(source, |_, _, _| {})
            .expect("the run must complete — never hang on the hard goal");
        let elapsed = run_start.elapsed();

        // The loop reached BOTH goals: it did not abort or hang on the first.
        assert_eq!(
            tally.attempted, 2,
            "the loop must continue past the hard goal to the easy one: {tally:?}"
        );
        // The trailing easy goal graduated through the kernel — progress was
        // genuinely made after the hard goal.
        assert!(
            tally.proved >= 1,
            "the subsequent easy goal must graduate after the hard goal: {tally:?}"
        );
        // The hard false goal did NOT graduate (soundness: a timeout/miss is
        // never a proof).
        assert!(
            tally.missed >= 1,
            "the hard false goal must be a miss, never a graduation: {tally:?}"
        );
        // The whole two-goal run is bounded by roughly the per-goal walls, not
        // by an unbounded grind — a generous ceiling that still catches a hang.
        assert!(
            elapsed < Duration::from_secs(30),
            "the run must be bounded by the per-goal walls, not hang: {elapsed:?}"
        );
    }

    // ---- premise-guided ATP contrast ----------------------------------------

    use clean_auto::AutomationEngine;
    use clean_kernel::{Declaration, Level, Name};
    use std::time::Duration;

    fn nat_eq(a: Expr, b: Expr) -> Expr {
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_str_levels("Eq", vec![Level::succ(Level::zero())]),
                    Expr::const_str("Nat"),
                ),
                a,
            ),
            b,
        )
    }

    /// Add the SAME declaration to both the worker's search (`base`) and
    /// recheck environments (so a goal can both be searched against it and
    /// graduate through the gate that sees it). Test-only.
    fn add_to_both_envs(worker: &mut SwarmWorker, decl: Declaration) {
        Arc::make_mut(&mut worker.base)
            .add_decl(decl.clone())
            .expect("add decl to base");
        worker.recheck.add_decl(decl).expect("add decl to recheck");
    }

    /// The headline lift: a goal that is NOT trivially closed but FOLLOWS FROM
    /// premises the database contains — discharged by SUPERPOSITION chaining
    /// (equality transitivity), with a FOUNDATIONAL verdict.
    ///
    /// Setup: three non-reducible `def`s `cA, cB, cC : Nat := 0`. Because they
    /// are non-reducible the bare hammer's reflexivity/SMT lanes do NOT unfold
    /// them, so the goal `cA = cC` is a genuine miss for the bare path (see the
    /// BARE-MISS assertion). But each is a `def` with a value, so the equalities
    /// `cA = cB` and `cB = cC` are FOUNDATIONAL theorems: `Eq.refl` type-checks
    /// because the KERNEL unfolds the defs to `0`. Those two theorems are seeded
    /// as premises.
    ///
    /// The premise-guided worker hands superposition both equality clauses,
    /// derives `cA = cC` by transitivity, and `closeover_premise_fvars` rewrites
    /// the two premise free variables to `@TProbe.prem_ab` / `@TProbe.prem_bc`.
    /// The resulting CLOSED term re-checks through the UNCHANGED C1 gate; its
    /// transitive axiom closure is foundational-only (the premises are
    /// `Eq.refl`-proved theorems, not axioms), so the verdict is `Proved`.
    /// Premises guided the SEARCH; the kernel certified the result.
    #[test]
    fn test_worker_premise_guided_proves_what_bare_misses() {
        let mut worker = SwarmWorker::new(WorkerConfig::default()).expect("prelude env");
        let engine = AutomationEngine::new();

        // Three non-reducible defs, all = Nat.zero. Non-reducible so the bare
        // hammer cannot relate them by def-eq; foundational because they have
        // values (no axiom).
        for nm in ["TProbe.cA", "TProbe.cB", "TProbe.cC"] {
            add_to_both_envs(
                &mut worker,
                Declaration::Definition {
                    name: Name::from_string(nm),
                    level_params: vec![],
                    type_: Expr::const_str("Nat"),
                    value: Expr::nat_lit(0),
                    is_reducible: false,
                },
            );
        }
        let ca = || Expr::const_str("TProbe.cA");
        let cb = || Expr::const_str("TProbe.cB");
        let cc = || Expr::const_str("TProbe.cC");
        let eq_refl_nat = |t: Expr| {
            Expr::app(
                Expr::app(
                    Expr::const_str_levels("Eq.refl", vec![Level::succ(Level::zero())]),
                    Expr::const_str("Nat"),
                ),
                t,
            )
        };

        // Two FOUNDATIONAL premise theorems: cA = cB and cB = cC, each proved by
        // Eq.refl (the kernel unfolds the defs to 0 to accept them).
        worker
            .seed_checked_premise("TProbe.prem_ab", nat_eq(ca(), cb()), eq_refl_nat(ca()))
            .expect("seed foundational premise cA = cB");
        add_to_both_envs(
            &mut worker,
            Declaration::Theorem {
                name: Name::from_string("TProbe.prem_bc"),
                level_params: vec![],
                type_: nat_eq(cb(), cc()),
                value: eq_refl_nat(cb()),
            },
        );
        // Rebuild the pool so BOTH premises are present (seed_checked_premise
        // rebuilt it after prem_ab; the direct add_to_both_envs for prem_bc did
        // not, so refresh).
        worker.premises = PremisePool::from_env(worker.base.as_ref());

        // Goal: cA = cC. A closed tier-1 Prop.
        let goal = nat_eq(ca(), cc());
        assert_eq!(
            tier1_classify(worker.base_env(), &goal),
            Tier1Outcome::Accept,
            "cA = cC must be a tier-1 goal"
        );

        // CONTRAST: the bare hammer misses it — it never sees the premise
        // equalities as clauses and will not unfold the non-reducible defs.
        let bare = engine.auto_prove(worker.base_env(), &goal, Duration::from_secs(3), None);
        assert!(
            bare.is_none(),
            "the bare hammer must MISS cA = cC (the contrast): got {bare:?}"
        );

        // PREMISE-GUIDED: prove via auto_prove_with_premises AND the C1 kernel
        // recheck accepts it to a FOUNDATIONAL verdict.
        let obligation = Obligation::new("TProbe.goal_cA_eq_cC", goal);
        let attempt = worker.attempt(&obligation);
        assert_eq!(
            attempt,
            Attempt::Proved(Tier::Tier1),
            "premise-guided worker must prove the goal the bare hammer missed AND the C1 gate must accept it foundationally: {attempt:?}"
        );
    }

    /// The A/B control through the WORKER's own [`ProverMode`] switch (not the
    /// raw engine): the same constructed goal, env, timeout, and C1 gate, with
    /// only the premise channel toggled. `ProverMode::Bare` MISSES the goal that
    /// `ProverMode::PremiseGuided` proves — so a count delta between a bare and a
    /// premise-guided corpus run is attributable to premises alone, and the bare
    /// mode never falsely graduates.
    fn build_premise_probe_worker(mode: ProverMode) -> (SwarmWorker, Obligation) {
        let mut worker = SwarmWorker::new(WorkerConfig {
            mode,
            ..WorkerConfig::default()
        })
        .expect("prelude env");
        for nm in ["AbProbe.cA", "AbProbe.cB", "AbProbe.cC"] {
            add_to_both_envs(
                &mut worker,
                Declaration::Definition {
                    name: Name::from_string(nm),
                    level_params: vec![],
                    type_: Expr::const_str("Nat"),
                    value: Expr::nat_lit(0),
                    is_reducible: false,
                },
            );
        }
        let eq_refl_nat = |t: Expr| {
            Expr::app(
                Expr::app(
                    Expr::const_str_levels("Eq.refl", vec![Level::succ(Level::zero())]),
                    Expr::const_str("Nat"),
                ),
                t,
            )
        };
        let ca = Expr::const_str("AbProbe.cA");
        let cb = Expr::const_str("AbProbe.cB");
        let cc = Expr::const_str("AbProbe.cC");
        add_to_both_envs(
            &mut worker,
            Declaration::Theorem {
                name: Name::from_string("AbProbe.prem_ab"),
                level_params: vec![],
                type_: nat_eq(ca.clone(), cb.clone()),
                value: eq_refl_nat(ca.clone()),
            },
        );
        add_to_both_envs(
            &mut worker,
            Declaration::Theorem {
                name: Name::from_string("AbProbe.prem_bc"),
                level_params: vec![],
                type_: nat_eq(cb, cc.clone()),
                value: eq_refl_nat(ca.clone()),
            },
        );
        worker.premises = PremisePool::from_env(worker.base.as_ref());
        let obligation = Obligation::new("AbProbe.goal", nat_eq(ca, cc));
        (worker, obligation)
    }

    #[test]
    fn test_worker_bare_mode_misses_what_premise_guided_proves() {
        // PREMISE-GUIDED worker mode: proves the transitivity goal.
        let (mut guided, obligation) = build_premise_probe_worker(ProverMode::PremiseGuided);
        assert_eq!(
            guided.attempt(&obligation),
            Attempt::Proved(Tier::Tier1),
            "premise-guided worker mode must prove the transitivity goal"
        );

        // BARE worker mode: identical pipeline, premise channel disabled — must
        // MISS (the lift is real), and must NEVER falsely graduate.
        let (mut bare, obligation) = build_premise_probe_worker(ProverMode::Bare);
        let attempt = bare.attempt(&obligation);
        assert!(
            !matches!(attempt, Attempt::Proved(_)),
            "bare worker mode must MISS the premise-only goal (A/B control); got {attempt:?}"
        );
    }

    // ---- tier-3: universe-polymorphic algebra goals -------------------------

    /// Build `∀ {M : Type u} [inst : Monoid M] (a : M), <body(M, inst, a)>` —
    /// the universe-polymorphic, typeclass-parameterised algebra shape every real
    /// Mathlib group/monoid lemma leads with. `body` is built over the three
    /// de Bruijn binders M=2, inst=1, a=0.
    fn monoid_forall(body: Expr) -> Expr {
        let u = Level::param(Name::from_string("u"));
        let monoid_m = Expr::app(
            Expr::const_str_levels("Monoid", vec![u.clone()]),
            Expr::bvar(0),
        );
        Expr::pi(
            clean_kernel::BinderInfo::Implicit,
            Expr::sort(Level::succ(u)), // M : Type u
            Expr::pi(
                clean_kernel::BinderInfo::InstImplicit,
                monoid_m, // [inst : Monoid M]
                Expr::pi(clean_kernel::BinderInfo::Default, Expr::bvar(1), body), // (a : M)
            ),
        )
    }

    /// THE TIER-3 HEADLINE (breaks BOTH walls). A universe-polymorphic Monoid
    /// lemma — `∀ {M : Type u} [Monoid M] (a : M), a = a` — that the bare import
    /// prelude could neither TYPE (no `Monoid` — WALL 1) nor CLASSIFY (the
    /// leading `Type u` binder was rejected as `UniversePolymorphic` — WALL 2),
    /// so every such goal was skipped before the prover.
    ///
    /// With [`Hierarchy::Algebra`] (the `Monoid` hierarchy in the recheck env)
    /// and the universe-polymorphic peel (the `Type u` and `[Monoid M]` binders
    /// peeled into the local context, `u` extracted into `level_params`), the
    /// worker:
    ///   1. tier-2-ACCEPTS the goal (no longer the `BadBinderType` wall);
    ///   2. proves the opened body `a = a` (reflexivity lane);
    ///   3. re-abstracts `λ {M} [inst] (a), Eq.refl a` and graduates a
    ///      universe-POLYMORPHIC `Declaration::Theorem` with `level_params = [u]`;
    ///   4. the C1 kernel gate RE-CHECKS that polymorphic term against the
    ///      original `∀`-type and returns a foundational verdict.
    ///
    /// The kernel, with the original `∀`-type and `level_params = [u]`, is the
    /// arbiter — a wrong re-abstraction or a mismatched `level_params` would be
    /// `KernelRejected`. `Proved(Tier2)` is the kernel's verdict, not the
    /// worker's.
    #[test]
    fn test_worker_universe_polymorphic_monoid_lemma_proves_and_kernel_accepts() {
        let u = Level::param(Name::from_string("u"));
        // body: @Eq.{u+1} M a a  (M : Type u = Sort (u+1), so equality is at u+1)
        let body = Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_str_levels("Eq", vec![Level::succ(u.clone())]),
                    Expr::bvar(2), // M
                ),
                Expr::bvar(0), // a
            ),
            Expr::bvar(0), // a
        );
        let goal = monoid_forall(body);

        let mut worker = SwarmWorker::new(WorkerConfig {
            hierarchy: Hierarchy::Algebra,
            ..WorkerConfig::default()
        })
        .expect("algebra-hierarchy environment must build");

        // WALL 1+2 broken: tier-2 now ACCEPTS the universe-polymorphic goal (it
        // was `BadBinderType(UniversePolymorphic)` before) and extracts `u`.
        let plan = match tier2_classify(worker.base_env(), &goal) {
            Tier2Outcome::Accept(plan) => plan,
            other => panic!("universe-poly Monoid goal must be tier-2 accepted; got {other:?}"),
        };
        assert_eq!(
            plan.level_params,
            vec![Name::from_string("u")],
            "the goal's universe param u must be extracted into level_params"
        );
        assert_eq!(plan.fvars.len(), 3, "M, inst, and a are all peeled");

        // End to end: the worker proves it AND the C1 kernel recheck accepts the
        // POLYMORPHIC Declaration::Theorem (correct level_params), foundationally.
        let attempt = worker.attempt(&Obligation::new("Tier3.monoid_refl", goal));
        assert_eq!(
            attempt,
            Attempt::Proved(Tier::Tier2),
            "the worker must prove the universe-polymorphic Monoid lemma AND the C1 gate \
             must accept the polymorphic theorem with level_params = [u]; got {attempt:?}"
        );
    }

    /// Soundness of the instance-axiom graduation path. The `mul_one` law of the
    /// `Monoid` instance lives as the instance's structure FIELD (projection
    /// index 4): `(Monoid.mul_one inst) : ∀ a, a * 1 = a`. The worker's tier-3
    /// path peels `[inst : Monoid M]` into a local fvar, so a proof of the body
    /// `a * 1 = a` is exactly that instance-field projection applied to `a` —
    /// the "instance-field premise" the closure env makes available.
    ///
    /// This test builds that instance-axiom proof, re-abstracts it over the
    /// peeled telescope, and confirms the C1 gate accepts the resulting
    /// universe-POLYMORPHIC `Declaration::Theorem` of
    /// `∀ {M} [Monoid M] (a), a * 1 = a` — the kernel re-checks `Monoid.mul`,
    /// `Monoid.one`, the projection, and the `level_params = [u]` against the
    /// original `∀`-type. It is the soundness witness for the prompt's
    /// instance-axiom mul_one shape: the graduation path is sound by
    /// construction, whatever search lane discovers the term.
    #[test]
    fn test_worker_instance_field_mul_one_graduates_polymorphic_theorem() {
        let u = || Level::param(Name::from_string("u"));
        // body: @Eq.{u+1} M (@Monoid.mul.{u} M inst a (@Monoid.one.{u} M inst)) a
        let mul = Expr::const_str_levels("Monoid.mul", vec![u()]);
        let one = Expr::const_str_levels("Monoid.one", vec![u()]);
        let m_one = Expr::app(Expr::app(one, Expr::bvar(2)), Expr::bvar(1));
        let lhs = Expr::app(
            Expr::app(
                Expr::app(Expr::app(mul, Expr::bvar(2)), Expr::bvar(1)),
                Expr::bvar(0),
            ),
            m_one,
        );
        let body = Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_str_levels("Eq", vec![Level::succ(u())]),
                    Expr::bvar(2),
                ),
                lhs,
            ),
            Expr::bvar(0),
        );
        let goal = monoid_forall(body);

        let mut worker = SwarmWorker::new(WorkerConfig {
            hierarchy: Hierarchy::Algebra,
            ..WorkerConfig::default()
        })
        .expect("algebra-hierarchy environment must build");

        let plan = match tier2_classify(worker.base_env(), &goal) {
            Tier2Outcome::Accept(plan) => plan,
            other => panic!("universe-poly mul_one goal must be tier-2 accepted; got {other:?}"),
        };

        // The instance-axiom proof: the Monoid.mul_one structure field (idx 4) of
        // the peeled instance fvar, applied to the peeled element fvar `a`.
        let inst = Expr::fvar(plan.fvars[1]);
        let a = Expr::fvar(plan.fvars[2]);
        let mul_one_field = Expr::proj(Name::from_string("Monoid"), 4, inst);
        let body_proof = Expr::app(mul_one_field, a);

        // Re-abstract over {M} [inst] (a) and gate against the original ∀-type
        // with level_params = [u] — the kernel is the arbiter.
        let value = reabstract_over_binders(plan.as_ref(), &body_proof);
        let attempt = worker.gate(
            "Tier3.monoid_mul_one",
            &goal,
            value,
            plan.level_params.clone(),
            Tier::Tier2,
        );
        assert_eq!(
            attempt,
            Attempt::Proved(Tier::Tier2),
            "the instance-field mul_one proof must graduate as a universe-polymorphic \
             theorem through the C1 gate; got {attempt:?}"
        );
    }
}
